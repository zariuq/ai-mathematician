#!/usr/bin/env python3
"""Local-only chat, ledger, queue and Lean-feedback controls; no paid API."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import threading
import time

from check_ai_mathematician_atp import read_values
from check_ai_mathematician_library import ROOT, quote
from check_ai_mathematician_prover import prelude as prover_prelude


def prelude():
    return (prover_prelude() + '!(import! &self io)\n!(import! &self re)\n' +
            "".join(f'!(import! &self {quote(ROOT / "phase1" / name)})\n'
                    for name in ("http_transport.metta", "llm_transport.metta", "llm.metta",
                                 "experiment.metta", "llm_experiment.metta")))


def execute(binary, source, output):
    path = output / (hashlib.sha256(source.encode()).hexdigest()[:20] + ".metta")
    path.write_text(source)
    ran = subprocess.run([str(binary), "--lang", "petta@1.0.6", str(path)],
                         cwd=ROOT, text=True, capture_output=True, check=False)
    assert ran.returncode == 0, ran.stderr or ran.stdout[:2000]
    values = read_values(ran.stdout)
    imports = prelude().count("!(import!")
    assert values[:imports] == ["true"] * imports and len(values) == imports + 1, ran.stdout[:2000]
    return values[-1]


def ledger(binary, path, request):
    ran = subprocess.run(["flock", "--exclusive", str(path) + ".lock", str(binary),
                          "--no-results", "--lang", "petta@1.0.6",
                          str(ROOT / "phase1/llm_ledger_main.metta"), str(path)],
                         cwd=ROOT, input=json.dumps(request), text=True, capture_output=True, check=False)
    assert ran.returncode == 0, ran.stderr
    return json.loads(ran.stdout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--http-cetta", type=Path)
    parser.add_argument("--corpus", type=Path)
    parser.add_argument("--lean", default="lean")
    args = parser.parse_args()
    binary = Path(shutil.which(str(args.cetta)) or args.cetta).resolve()
    base = ROOT / ".cetta/llm"
    base.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix="local-", dir=base))
    shared = output / "concurrent.jsonl"
    request = {"operation": "reserve", "model": "local", "cap": 7}
    with ThreadPoolExecutor(max_workers=8) as pool:
        replies = list(pool.map(lambda _: ledger(binary, shared, request), range(24)))
    reserved = sorted(row["n"] for row in replies if row["kind"] == "reserved")
    assert reserved == list(range(1, 8)), replies
    assert sum(row["kind"] == "limit" for row in replies) == 17, replies
    usage = {"operation": "usage", "model": "wrong", "n": 1, "nanoseconds": 3, "usage": None}
    assert ledger(binary, shared, usage)["kind"] == "ledger-fault"
    usage["model"] = "local"
    assert ledger(binary, shared, usage)["kind"] == "usage-recorded"
    assert ledger(binary, shared, usage)["kind"] == "ledger-fault"
    assert len(shared.read_text().splitlines()) == 8
    with shared.open("a") as stream:
        stream.write('{"interrupted":')
    assert ledger(binary, shared, {**request, "cap": 100})["kind"] == "ledger-fault"
    checks = 7
    samples = [("```lean\n  intro P\n  exact P\n```", "intro P\nexact P"),
               ("by\nintro P", "intro P"),
               ("```lean\ntheorem x : P := by\n  exact p\n```", "exact p"),
               ("```lean\nfirst\n```between```lean4\nsecond\n```", "second"),
               ("```lean\n  intro P", "intro P")]
    actual = execute(binary, prelude() + "!(let $parser (ai-math:llm-code-parser)\n" +
                     " (map-atom (" + " ".join(quote(s) for s, _ in samples) +
                     ") $reply (ai-math:llm-extract $parser $reply)))\n", output)
    assert actual == [text for _, text in samples], actual
    checks += len(samples)
    if not args.http_cetta:
        print("LLMHTTPIntegrationSkipped: supply --http-cetta for local transport and --corpus for Lean feedback")
        print(f"AiMathematicianLLM {checks} 0")
        return
    http_binary = args.http_cetta.resolve()
    requests, lock = [], threading.Lock()

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def answer(self, status, body):
            data = body if isinstance(body, bytes) else json.dumps(body).encode()
            self.send_response(status)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            try:
                self.wfile.write(data)
            except (BrokenPipeError, ConnectionResetError):
                pass

        def do_GET(self):
            if self.path == "/slow":
                time.sleep(0.08)
            self.answer(200, self.path.encode())

        def do_POST(self):
            body = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
            with lock:
                count = sum(item["model"] == body["model"] for item in requests)
                requests.append(body)
            if body["model"] == "retry" and count == 0:
                self.answer(503, {"error": "fixture retry"})
                return
            if body["model"] == "malformed":
                self.answer(200, b"not-json")
                return
            if body["model"] in ("proof", "experiment"):
                text = ("exact orIL" if count == 0 else "intro P Q hp r f g\nexact f hp")
                text = "```lean\n" + text + "\n```"
            elif body["model"] == "dsp":
                text = ("Assume P and Q and a proof of P. Introduce the encoded disjunction by its left branch."
                        if count == 0 else "```lean\nintro P Q hp\napply (b_or P Q).mpr\n"
                        "have left : P := by ai_math_auto []\nexact Or.inl left\n```")
            elif body["model"] == "secret":
                text = self.headers["Authorization"].removeprefix("Bearer ")
            else:
                text = "hello λ"
            self.answer(200, {"choices": [{"message": {"content": text}}],
                              "usage": {"prompt_tokens": 3, "completion_tokens": 2,
                                        "untrusted-extra": self.headers.get("Authorization")}})

    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    secret = "local-fixture-credential-not-a-real-api-key"
    url = f"http://127.0.0.1:{server.server_port}"
    try:
        client = lambda model, cap, options="()": (
            f'(ai-math:llm-client {quote(ROOT)} (ai-math:http-session) {quote(url + "/v1")}'
            f' {quote(model)} {quote(secret)} {quote(output / (model + ".jsonl"))} {cap} {options})')
        messages = '((JsonObject ((JsonPair "role" (JsonString "user")) (JsonPair "content" (JsonString "hi")))))'
        actual = execute(http_binary, prelude() + f"""
!(let* (($client {client('normal', 1)})
        ($first (ai-math:llm-chat $client {messages} 1)))
   ($first (ai-math:llm-chat $client {messages} 1)))
""", output)
        assert actual[0][:2] == ["AiLLM:Reply", "hello λ"] and actual[1] == ["AiLLM:Limit", "1"], actual
        assert len(requests) == 1 and secret not in (output / "normal.jsonl").read_text()
        checks += 3
        actual = execute(http_binary, prelude() + f"""
!(let $client {client('retry', 2, '((retry-delay-seconds 0) (token-field "max_completion_tokens"))')}
   (ai-math:llm-chat $client {messages} 2))
""", output)
        assert actual[0] == "AiLLM:Reply", actual
        retry = [item for item in requests if item["model"] == "retry"]
        assert len(retry) == 2 and all("max_completion_tokens" in item and "max_tokens" not in item for item in retry)
        checks += 2
        for model, reason in [("secret", "credential-in-response"), ("malformed", "response-shape")]:
            actual = execute(http_binary, prelude() + f"!(ai-math:llm-chat {client(model, 1)} {messages} 1)\n", output)
            assert actual[0] == "AiLLM:AttemptFailed" and reason in str(actual), actual
            assert secret not in str(actual) and secret not in (output / (model + ".jsonl")).read_text()
            checks += 2
        actual = execute(http_binary, prelude() + f"""
!(let* (($session (ai-math:http-session))
        ((io:pending $fast) (io:submit (http:request "GET" {quote(url + '/fast')} () "" 1000 1000)))
        ((io:pending $slow) (io:submit (http:request "GET" {quote(url + '/slow')} () "" 1000 1000)))
        ($a (ai-math:http-await $session $slow)) ($b (ai-math:http-await $session $fast)))
   ($a $b (io:poll)))
""", output)
        assert actual == [["AiHTTP:Response", "200", "/slow"], ["AiHTTP:Response", "200", "/fast"], ["io:idle"]], actual
        checks += 3
        if args.corpus:
            actual = execute(http_binary, prelude() + f"""
!(let* (($ds (ai-math:load-library {quote(args.corpus.resolve())}))
        ($itp (ai-math:itp $ds {quote(ROOT)} {quote(args.lean)}))
        ($context (AiProver None None $itp None ()))
        ($client {client('proof', 2)}))
   (ai-math:llm-prove $context $client "orIL" ("andI") ("or") 3 (AiITP:Budget 30000 200000 8000)))
""", output)
            assert actual[0] == "AiLLM:Result" and len(actual[2]) == 2, actual
            assert actual[-1][0] == "AiProver:Proved" and actual[-1][3] == "llm-r2", actual[-1]
            assert actual[2][0][4][0] == "AiITP:Rejected" and "source-order" in str(actual[2][0]), actual[2][0]
            proofs = [item for item in requests if item["model"] == "proof"]
            assert len(proofs) == 2 and [len(item["messages"]) for item in proofs] == [2, 4], proofs
            assert "source-order" in proofs[1]["messages"][-1]["content"]
            checks += 5
            actual = execute(http_binary, prelude() + f"""
!(let* (($ds (ai-math:load-library {quote(args.corpus.resolve())}))
        ($itp (ai-math:itp $ds {quote(ROOT)} {quote(args.lean)}))
        ($context (AiProver None None $itp None ()))
        ($client {client('dsp', 2)}))
   (ai-math:dsp-prove $context $client "orIL" ("andI") ("or") 0 (AiITP:Budget 30000 200000 8000)))
""", output)
            assert actual[0] == "AiDSP:Result" and actual[2][0] == "AiDSP:Draft", actual
            assert actual[-1][0] == "AiProver:Proved" and "ai_math_auto" in actual[-1][4], actual[-1]
            drafts = [item for item in requests if item["model"] == "dsp"]
            assert len(drafts) == 2 and "ai_math_auto" in drafts[1]["messages"][-1]["content"]
            checks += 3
            baseline = output / "baseline.jsonl"
            baseline.write_text(json.dumps({"goal": "orIL", "vampire": "Theorem@16", "proved_by": None,
                                             "premises": ["andI"], "defs": ["or"]}) + "\n")
            observations = output / "proposal-results.jsonl"
            actual = execute(http_binary, prelude() + f"""
!(let* (($ds (ai-math:load-library {quote(args.corpus.resolve())}))
        ($context (ai-math:prover-with $ds {quote(args.corpus.resolve())} {quote(ROOT)} {quote(args.lean)} "unused"
          ((slices ()) (use-duper false) (induction false))))
        ($client {client('experiment', 2)})
        ($run (ai-math:proposal-open $context $client {quote(args.corpus.resolve())} {quote(baseline)}
          {quote(observations)} "fixture-toolchain" direct 3 (AiITP:Budget 30000 200000 8000) Fresh))
        ($targets (ai-math:proposal-select $run 1 0 0 true))
        ($first (ai-math:proposal-one $run "orIL"))
        ($resume (ai-math:proposal-open $context $client {quote(args.corpus.resolve())} {quote(baseline)}
          {quote(observations)} "fixture-toolchain" direct 3 (AiITP:Budget 30000 200000 8000) Resume))
        ($again (ai-math:proposal-one $resume "orIL")))
   ($targets $first $again))
""", output)
            assert actual[0] == ["orIL"], actual
            assert actual[1][:2] == ["AiRun:Recorded", "orIL"], actual[1]
            assert actual[2][:3] == ["AiRun:Reused", "orIL", "rechecked"], actual[2]
            logged = [json.loads(line) for line in observations.read_text().splitlines() if line.strip()]
            assert len(logged) == 2 and logged[1]["outcome"] == "proved", logged
            assert logged[1]["premises"] == ["andI"] and logged[1]["defs"] == ["or"], logged[1]
            assert logged[1]["model"] == "experiment" and secret not in observations.read_text()
            assert len([item for item in requests if item["model"] == "experiment"]) == 2
            checks += 7
            config = {"corpus": str(args.corpus.resolve()), "baseline": str(baseline),
                      "output": str(output / "cli-results.jsonl"), "model": "cli",
                      "ledger": str((output / "cli-ledger.jsonl").relative_to(ROOT.parent)), "call_cap": 1,
                      "rounds": 1, "vampire_only": True}
            config_path = output / "configuration.json"
            config_path.write_text(json.dumps(config))
            entry = [str(http_binary), "--no-results", "--lang", "petta@1.0.6",
                     str(ROOT / "phase1/llm_experiment_main.metta"), str(config_path)]
            blocked = subprocess.run(entry, cwd=ROOT, text=True, capture_output=True, check=False)
            assert blocked.returncode == 2 and "configuration-and-unsandboxed-consent" in blocked.stdout
            assert not (output / "cli-results.jsonl").exists()
            config["allow_unsandboxed_metaprograms"] = True
            config_path.write_text(json.dumps(config))
            local_environment = dict(os.environ, LLM_API_KEY=secret, LLM_BASE_URL=url + "/v1")
            ran = subprocess.run(entry, cwd=ROOT.parent, env=local_environment,
                                 text=True, capture_output=True, check=False)
            assert ran.returncode == 0 and "AiRun:Summary" in ran.stdout, ran.stdout + ran.stderr
            assert secret not in ran.stdout + ran.stderr and (output / "cli-results.jsonl").is_file()
            assert (output / "cli-ledger.jsonl").is_file()
            checks += 4
            for key, invalid in (("rounds", -1), ("stride", 0), ("vampire_only", "false"),
                                 ("token_field", "unknown")):
                config_path.write_text(json.dumps({**config, key: invalid}))
                rejected = subprocess.run(entry, cwd=ROOT.parent, env=local_environment,
                                          text=True, capture_output=True, check=False)
                assert rejected.returncode == 2 and "configuration-and-unsandboxed-consent" in rejected.stdout, rejected.stdout
                checks += 1
    finally:
        server.shutdown()
        server.server_close()
        thread.join()
    print(f"AiMathematicianLLM {checks} 0")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ValueError, IndexError, subprocess.CalledProcessError) as error:
        print(f"FAIL {error}", file=sys.stderr)
        sys.exit(1)
