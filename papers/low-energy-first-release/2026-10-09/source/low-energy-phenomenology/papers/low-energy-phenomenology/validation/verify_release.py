#!/usr/bin/env python3
"""Check bilingual equation alignment, English plates and the two reading PDFs."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import xml.etree.ElementTree as ET

import pymupdf as fitz

PAPER = Path(__file__).resolve().parents[1]
OUT = PAPER / 'build/release-checks'
OUT.mkdir(parents=True, exist_ok=True)
checks = []


def check(name, passed, detail=None):
    checks.append({'name': name, 'passed': bool(passed), 'detail': detail})
    print(('PASS ' if passed else 'FAIL ') + name)


def normalize_math(value):
    value = value.replace(r'\text{ 可逆}', r'\text{ invertible}')
    value = value.replace(r'\text{的三根}', r'\text{three roots}')
    value = value.replace(r'\text{the three roots of }6x^3-26x^2+27x-8=0',
                          r'6x^3-26x^2+27x-8=0\ \text{three roots}')
    value = value.replace(r'\text{或}', r'\text{or}').replace(r'\text{四元幂}', r'\text{four-tuple power}')
    value = value.replace(r'\text{four-momentum power}', r'\text{four-tuple power}')
    return re.sub(r'\s+', '', value)


zh = (PAPER / 'manuscript.md').read_text()
en = (PAPER / 'manuscript-en.md').read_text()
body_zh = zh.split('<a id="sec-1"></a>', 1)[1].split('<!-- code-availability:begin -->', 1)[0]
body_en = en.split('<a id="sec-1"></a>', 1)[1].split('<!-- code-availability:begin -->', 1)[0]
displays_zh = [normalize_math(x) for x in re.findall(r'\$\$(.*?)\$\$', body_zh, re.S)]
displays_en = [normalize_math(x) for x in re.findall(r'\$\$(.*?)\$\$', body_en, re.S)]
display_differences = [{'index': i + 1, 'zh': a, 'en': b}
                       for i, (a, b) in enumerate(zip(displays_zh, displays_en)) if a != b]
check('all display equations aligned in order', displays_zh == displays_en,
      {'zh': len(displays_zh), 'en': len(displays_en), 'differences': display_differences})
tags_zh = re.findall(r'\\tag\{([^}]+)\}', body_zh)
tags_en = re.findall(r'\\tag\{([^}]+)\}', body_en)
check('all release equation labels retained in order and unique',
      tags_zh == tags_en and len(tags_en) == len(set(tags_en)) and len(tags_en)>=251)
inline = lambda text: Counter(normalize_math(x) for x in re.findall(
    r'(?<!\$)\$(?!\$)(.*?)(?<!\$)\$(?!\$)', re.sub(r'\$\$.*?\$\$', '', text, flags=re.S), re.S))
iz, ie = inline(body_zh), inline(body_en)
extra = ie - iz
check('all original inline formulas retained', not (iz - ie),
      {'removed': list((iz - ie).elements()), 'English_explicit_notation': dict(extra)})
check('English added math only makes existing block sizes and spin symbol explicit',
      set(extra) <= {r'2\times2', r'4\times4', 'S'})
anchors = [f'sec-{i}' for i in range(1, 15)] + [f'app-{c}' for c in 'abcdefg']
check('fourteen complete sections and seven appendices',
      all(en.count(f'id="{a}"') == 1 for a in anchors))
check('all release claims have English evidence rows',
      all(re.search(rf'^\| L{i}\b', en, re.M) for i in range(1, 29)))
check('six actual bibliography entries in each edition',
      all(re.search(rf'^\[{i}\] ', t, re.M) for t in [zh, en] for i in range(1, 7)))
check('published physics predecessor is referenced in both editions',
      'https://doi.org/10.5281/zenodo.23210292' in zh and
      'https://doi.org/10.5281/zenodo.23210292' in en)
check('English edition has no untranslated Chinese', not re.search(r'[\u4e00-\u9fff]', en))
check('both editions have exactly nine figure references',
      all(len(re.findall(r'!\[[^\]]*\]\(figures/', t)) == 9 for t in [zh, en]))
selection = json.loads((PAPER / 'release-selection.json').read_text())
expected_ids = [f'low1.L{i}' for i in range(1, 29)]
check('release selection has all 28 qualified claims once',
      selection['claim_ids'] == expected_ids and
      [c['id'] for c in selection['claims']] == expected_ids)
epochs = [(range(1, 18), '30218c1aea92640eae09b1d9204a09b01a2d0e47'),
          (range(18, 24), 'e05558097256e86b537c019c8ca63cd449d6b2d2'),
          (range(24, 26), 'c62f3d25c42d4bf2b77ac009b49fc71cfd752f46'),
          (range(26, 29), '71e94e8261d67cf4849a05eb14ac95aa2f7dcbb9')]
check('each claim retains its actual fixed source epoch',
      all(selection['claims'][i-1]['source_commit'] == commit
          for ids, commit in epochs for i in ids))
check('all claims name actual production, consumers and complete bilingual proof files',
      all(c['production'] and c['direct_consumers'] and
          c['written_proof_status'] == 'integrated_bilingual_complete' and
          c['written_proof']['zh']['file'] == 'manuscript.md' and
          c['written_proof']['en']['file'] == 'manuscript-en.md'
          for c in selection['claims']))
check('new leading results locate their proof equations and retain independent conditions',
      all(c['written_proof']['zh'].get('equations') and c.get('conditions')
          for c in selection['claims'][25:]))
audit = json.loads((PAPER / 'validation/release-source-audit.json').read_text())
check('actual new production-byte bindings match original receipts',
      audit['additional_source_bindings_verified'] and
      audit['additional_source_binding_comparisons'] == 36 and not audit['errors_to_resolve'])
public = selection['public_evidence']
binding_consistent = (
    bool(re.fullmatch(r'[0-9a-f]{40}', public['acceptance_commit'] or '')) and
    bool(public['entry_modules']) and bool(public.get('actual_new_reproduction_commands')) and
    audit['whole_L1_L28_public_binding_complete']
    if public['complete'] else
    public['acceptance_commit'] is None and not public['entry_modules'] and
    not selection['release_status']['overall_publication_ready'] and
    not audit['whole_L1_L28_public_binding_complete'])
check('public binding reflects the actual acceptance status', binding_consistent)
check('full import/resource layout and exact H0 request are delivered',
      (PAPER / selection['compile_layout_requirements']['index']).is_file() and
      (PAPER / public['request']).is_file())
for text, heading in [(zh, '## 参考文献'), (en, '## References')]:
    used = set(re.findall(r'\(((?:[1-9]\d*|[A-G])\.\d+[a-z]?)\)', text.split(heading)[0]))
    check(('Chinese' if text == zh else 'English') + ' equation references resolve',
          not used.difference(tags_en), sorted(used.difference(tags_en)))
for text, label in [(zh, 'zh'), (en, 'en')]:
    block = text.split('<!-- code-availability:begin -->')[1].split('<!-- code-availability:end -->')[0]
    check(label + ' availability has the fixed release binding and actual commands',
          all(x in block for x in ['ba591b43e13a59ac676919aa153569615f8d4cb2',
              '30218c1aea92640eae09b1d9204a09b01a2d0e47',
              '8e29b8e1e58f9846fdddedaaeab9fc8724cdcb87',
              'H0mework.Papers.LowEnergyPhenomenology',
              'make bootstrap && make build', 'make check', 'make check-map']))
    missing = []
    for rel in re.findall(r'!\[[^\]]*\]\(([^)]+)\)', text):
        if not (PAPER / rel).is_file():
            missing.append(rel)
    check(label + ' figure paths resolve', not missing, missing)

figure_records = []
for svg in sorted((PAPER / 'figures').glob('*-en.svg')):
    root = ET.fromstring(svg.read_text())
    check(svg.stem + ': English SVG labels',
          not re.search(r'[\u4e00-\u9fff]', ''.join(root.itertext())))
    with fitz.open(svg.with_suffix('.pdf')) as doc:
        words = doc[0].get_text('words')
        outside = [w[4] for w in words if not doc[0].rect.contains(fitz.Rect(w[:4]))]
        check(svg.stem + ': one vector page and no text clipping',
              len(doc) == 1 and not doc[0].get_images() and len(words) >= 5 and not outside,
              {'outside': outside, 'words': len(words)})
    if svg.stem in ['main-02-soft-phases-en', 'main-03-finite-current-en']:
        dashed = [e for e in root.findall('{http://www.w3.org/2000/svg}path')
                  if e.get('d', '').count('M') > 20]
        check(svg.stem + ': dashed curves remain segmented geometry', bool(dashed))
    figure_records.append({'stem': svg.stem, 'sha256': {
        ext: hashlib.sha256(svg.with_suffix('.' + ext).read_bytes()).hexdigest()
        for ext in ['svg', 'pdf', 'png']}})
check('all nine English plates present', len(figure_records) == 9)

pdf_records = []
for language, name in [('zh', 'low-energy-phenomenology'), ('en', 'low-energy-phenomenology-en')]:
    pdf = PAPER / 'build' / (name + '.pdf')
    report = json.loads((PAPER / 'build' / ('pdf-work-en' if language == 'en' else 'pdf-work') /
                         'build-report.json').read_text())
    check(language + ' PDF: no overfull boxes or missing characters',
          report['overfull_boxes'] == 0 and not report['missing_characters'], report)
    with fitz.open(pdf) as doc:
        check(language + ' PDF: every page contains reading text',
              all(len(page.get_text().strip()) > 20 for page in doc), len(doc))
        metadata = json.dumps(doc.metadata)
        uris = [link.get('uri', '') for page in doc for link in page.get_links()]
        check(language + ' PDF: no personal filesystem paths in metadata or links',
              not re.search(r'/(?:Users|home)/[A-Za-z0-9._-]+/', metadata + '\n'.join(uris)) and
              not any(uri.startswith('file:') for uri in uris))
        pdf_records.append({'language': language, 'file': str(pdf.relative_to(PAPER)),
                            'pages': len(doc), 'sha256': hashlib.sha256(pdf.read_bytes()).hexdigest()})

result = {'all_passed': all(c['passed'] for c in checks), 'check_count': len(checks),
          'checks': checks, 'display_equations': len(displays_en), 'equation_labels': len(tags_en),
          'English_inline_additions': dict(extra), 'figures': figure_records, 'pdfs': pdf_records,
          'scope': 'Bilingual structural/formula and PDF checks; visual inspection is recorded separately.'}
(OUT / 'release-alignment.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
raise SystemExit(0 if result['all_passed'] else 1)
