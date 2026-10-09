#!/usr/bin/env python3
"""Package only this manuscript and its required editable build dependencies."""
from __future__ import annotations
import hashlib
import gzip
import json
from pathlib import Path
import re
import zipfile

PAPER = Path(__file__).resolve().parents[1]
ROOT = PAPER.parents[1]
OUT = PAPER / 'build/zenodo'
NAME = 'low-energy-phenomenology-editable-v1.zip'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    paths = [PAPER/n for n in ['manuscript.md', 'manuscript-en.md', 'zenodo-metadata.md',
             'release-selection.json', 'public-proof-index.json', 'h0-evidence-request.md',
             '.gitattributes']]
    paths += [p for p in (PAPER/'figures').rglob('*') if p.is_file() and
              p.suffix in {'.svg', '.pdf', '.png', '.py', '.json', '.csv'} and '__pycache__' not in p.parts]
    paths += [PAPER/'scripts'/n for n in ['build_pdf.py', 'refresh_availability.py',
              'prepare_zenodo.py', 'package_release.py', 'RELEASE.md']]
    paths += [PAPER/'validation'/n for n in ['verify_new_math.py', 'verify_release.py',
              'release-source-audit.md', 'release-source-audit.json', 'release-public-closure.json.gz']]
    paths += [ROOT/'shared/scripts'/n for n in ['build_pdf.py', 'byline.py',
              'code_availability.py', 'zenodo_metadata.py']]
    paths += [ROOT/'shared/styles'/n for n in ['article-header.tex', 'article-header-en.tex',
              'article-filter.lua']]
    paths += [ROOT/'shared/figure-style/house_style.py']
    members = {str(p.relative_to(ROOT)): p.read_bytes() for p in sorted(set(paths))}
    members['README.md'] = (PAPER/'scripts/RELEASE.md').read_bytes()
    members['LICENSE.txt'] = (
        'Paper text and original figures: Creative Commons Attribution 4.0 International.\n'
        'Author: Jian Gao. License: https://creativecommons.org/licenses/by/4.0/\n'
        'The formal proof repository has its own Apache-2.0 license and third-party notices.\n').encode()
    for name, raw in members.items():
        if re.search(r'(^|/)(?:build|\.git|\.local|__pycache__|prompts)(/|$)', name):
            raise ValueError('Excluded directory in package: '+name)
        if Path(name).suffix in {'.md', '.json', '.py', '.tex', '.lua', '.svg', '.txt', '.csv'} or name.endswith('.json.gz'):
            text = (gzip.decompress(raw) if name.endswith('.json.gz') else raw).decode()
            if (re.search(r'/(?:Users|home)/[A-Za-z0-9._-]+/', text) or
                    re.search(r'[A-Za-z]:\\Users\\[A-Za-z0-9._-]+', text)):
                raise ValueError('Private absolute path in package: '+name)
    identity = {'schema': 'low1-editable-package/v1', 'claim_scope': 'L1-L28',
                'public_binding_complete': False,
                'files': {name: {'bytes': len(raw), 'sha256': digest(raw)}
                          for name, raw in sorted(members.items())}}
    identity['public_binding_complete'] = json.loads((PAPER/'release-selection.json').read_text())['public_evidence']['complete']
    members['MANIFEST.json'] = (json.dumps(identity, ensure_ascii=False, indent=2)+'\n').encode()
    archive = OUT/NAME
    with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for name, raw in sorted(members.items()):
            info = zipfile.ZipInfo(name, date_time=(2026,10,9,0,0,0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o644 << 16
            z.writestr(info, raw)
    with zipfile.ZipFile(archive) as z:
        assert z.testzip() is None
        assert all(z.read(name) == raw for name, raw in members.items())
    report = {'file': str(archive.relative_to(PAPER)), 'members': len(members),
              'bytes': archive.stat().st_size, 'sha256': digest(archive.read_bytes()),
              'privacy_scan_passed': True, 'reopened_and_verified': True,
              'scope': 'Complete editable L1-L28 manuscripts, figures and build dependencies; new public proof acceptance is pending.'}
    (OUT/'package-report.json').write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps(report, ensure_ascii=False))


if __name__ == '__main__':
    main()
