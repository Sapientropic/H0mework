#!/usr/bin/env python3
"""Generate this paper's bilingual Zenodo fields with the shared generator."""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'shared/scripts'))
import zenodo_metadata as common
from refresh_availability import COMMIT

if __name__ == '__main__':
    path = common.write('low-energy-phenomenology', 'manuscript.md', 'manuscript-en.md',
                        ['build/low-energy-phenomenology-en.pdf',
                         'build/low-energy-phenomenology.pdf'])
    text = path.read_text()
    selection = json.loads((path.parent / 'release-selection.json').read_text())
    public = selection['public_evidence']
    binding = public['acceptance_commit'] if public['complete'] else COMMIT
    text = text.replace('python3 shared/scripts/zenodo_metadata.py',
                        'python3 papers/low-energy-phenomenology/scripts/prepare_zenodo.py')
    text = text.replace(common.CODE + '/tree/' + common.TAG,
                        common.CODE + '/tree/' + binding)
    files_end = text.index('\n## Resource type')
    text = text[:files_end] + ('- `papers/low-energy-phenomenology/build/zenodo/'
                              'low-energy-phenomenology-editable-v1.zip`（可编辑正文、图源、数据及构建材料）\n') + text[files_end:]
    related_end = text.index('\n## Notes')
    text = text[:related_end] + ('- Relation：References；Identifier：10.5281/zenodo.23210292；'
                                 'Scheme：DOI；Resource type：Publication → Preprint\n') + text[related_end:]
    text = text.replace('已有本文的 DOI 时填写原 DOI；没有时选择 No，并可用 Get a DOI now! 在草稿中预留。',
                        '本地材料未填写或预留本文 DOI。作者若已有实际预留 DOI，填写该值；否则由作者在草稿中预留。')
    if not public['complete']:
        text = text.replace('Formal proofs, exact programs and frozen receipts are in the code repository above; the paper\'s "Code and data availability" section gives the entry modules and reproduction commands.',
                            'The software link covers the inherited L1–L17 evidence. Complete bilingual text and written proofs now cover L1–L28; the new public proof export and acceptance commit remain to be supplied. See release-selection.json and h0-evidence-request.md before publication.')
    path.write_text(text)
    print('wrote', path.relative_to(ROOT))
