#!/usr/bin/env python3
"""Acquire the pinned official solver without modifying a shared checkout."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[1]
VERSION = '5.1.0'
REVISION = '7b2f410ec4430c26217a85db62cf0c4a97042f8d'
URL = 'https://github.com/vprover/vampire/releases/download/v5.1.0/vampire-Linux-X64.zip'
ARCHIVE_SHA256 = '495828dc76cb17a27080d62dedce755e46de96f47f06f5f0ad4be9cdaf6f968f'


def digest(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cache', type=Path, default=ROOT / '.cetta/tools/vampire-5.1.0-linux-x64')
    a = p.parse_args()
    if platform.system() != 'Linux' or platform.machine() not in ('x86_64', 'AMD64'):
        p.error('this acquisition pin is for Linux x86-64; supply a separately verified solver on other platforms')
    a.cache.mkdir(parents=True, exist_ok=True)
    archive = a.cache / 'release.zip'
    if not archive.exists():
        with urllib.request.urlopen(URL, timeout=60) as source, archive.open('xb') as target:
            while block := source.read(1024 * 1024):
                target.write(block)
    if digest(archive) != ARCHIVE_SHA256:
        raise ValueError('solver archive checksum mismatch; no executable was published')
    with zipfile.ZipFile(archive) as bundle:
        candidates = [n for n in bundle.namelist() if Path(n).name == 'vampire' and not n.endswith('/')]
        if len(candidates) != 1:
            raise ValueError(('expected one solver executable', bundle.namelist()))
        contents = bundle.read(candidates[0])
    binary = a.cache / 'vampire'
    wanted = hashlib.sha256(contents).hexdigest()
    if binary.exists():
        if digest(binary) != wanted:
            raise ValueError('cached executable differs from the pinned archive; refusing to replace it')
    else:
        with binary.open('xb') as output:
            output.write(contents)
        binary.chmod(0o755)
    version = subprocess.check_output([str(binary.resolve()), '--version'], text=True, timeout=15).strip()
    if 'Vampire ' + VERSION not in version:
        raise ValueError(('unexpected solver version', version))
    manifest = dict(version=VERSION, revision=REVISION, url=URL,
                    archive_sha256=ARCHIVE_SHA256, executable_sha256=wanted,
                    version_output=version, archive_member=candidates[0])
    (a.cache / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest, indent=2))
    print(binary.resolve())


if __name__ == '__main__':
    main()
