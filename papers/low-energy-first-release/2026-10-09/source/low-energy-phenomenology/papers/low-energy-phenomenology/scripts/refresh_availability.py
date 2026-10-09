#!/usr/bin/env python3
"""Refresh only this paper's pinned Chinese and English availability blocks."""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'shared/scripts'))
import code_availability as common

COMMIT = 'ba591b43e13a59ac676919aa153569615f8d4cb2'
PAPER = ROOT / 'papers/low-energy-phenomenology'
SPEC = common.PAPERS['papers/low-energy-phenomenology/manuscript.md']
NOTE_EN = ('base is the immediate successor of S, containing a tactical proof repair; '
           'the modules used by this paper are byte-identical between the two commits.')

if __name__ == '__main__':
    selection = json.loads((PAPER / 'release-selection.json').read_text())
    public = selection['public_evidence']
    if public['complete']:
        commit = public['acceptance_commit']
        spec = dict(SPEC,
                    revs=list(selection['source_epochs'].items()),
                    aggs=[name.removeprefix('H0mework.Papers.') for name in public['entry_modules']],
                    checks=public['actual_new_reproduction_commands'])
    else:
        commit, spec = COMMIT, SPEC
    for name, block in [('manuscript.md', common.section(COMMIT, SPEC)),
                        ('manuscript-en.md', common.section_en(COMMIT, SPEC, NOTE_EN))]:
        english = name.endswith('-en.md')
        if public['complete']:
            block = common.section_en(commit, spec, NOTE_EN) if english else common.section(commit, spec)
            if commit != COMMIT:
                block = block.replace(f' (tag `{common.TAG}`)', '').replace(f'（标签 `{common.TAG}`）', '')
        else:
            if english:
                block = block.replace('The formal proofs, exact programs and frozen receipts of this paper',
                                      'The inherited L1–L17 formal proofs, exact programs and frozen receipts')
                note = ('The added L18–L23 results retain source commit '
                        '`e05558097256e86b537c019c8ca63cd449d6b2d2`; L24–L25 retain '
                        '`c62f3d25c42d4bf2b77ac009b49fc71cfd752f46`; L26–L28 retain '
                        '`71e94e8261d67cf4849a05eb14ac95aa2f7dcbb9`. Their written proofs are '
                        'included in §§9–13 and Appendices F–G. The [release selection](release-selection.json) '
                        'records each production statement, direct consumer, source digest and original certification. '
                        'At the fixed public observation `51867c59042460646e57d5ead4c405cbca05c240`, '
                        'the new production entries have no export mapping. A public package covering all L1–L28 '
                        'has not yet received an acceptance commit. Its precise material requirements are in '
                        '[the H0 evidence request](h0-evidence-request.md); the older entry above certifies its inherited scope.')
            else:
                block = block.replace('本文的形式化证明、精确程序与冻结回执公开于',
                                      '本稿继承的L1–L17形式化证明、精确程序与冻结回执公开于')
                note = ('新增L18–L23采用源提交 `e05558097256e86b537c019c8ca63cd449d6b2d2`，'
                        'L24–L25采用 `c62f3d25c42d4bf2b77ac009b49fc71cfd752f46`，'
                        'L26–L28采用 `71e94e8261d67cf4849a05eb14ac95aa2f7dcbb9`。'
                        '完整书面证明已纳入§§9–13与附录F–G；逐项生产声明、直接消费者、来源摘要及原认证见'
                        '[发布选集](release-selection.json)。公开观察固定 '
                        '`51867c59042460646e57d5ead4c405cbca05c240`，新增关键生产口尚无导出映射；'
                        '覆盖全部L1–L28的公开包尚无实际验收提交。精确迁入需求见'
                        '[H0材料请求](h0-evidence-request.md)，上面的旧入口保留其继承范围。')
            block = block.replace(common.END, note + '\n' + common.END)
        path = PAPER / name
        text = path.read_text()
        head, rest = text.split(common.BEGIN, 1)
        tail = rest.split(common.END, 1)[1].lstrip('\n')
        path.write_text(head + block + tail)
        print('updated', name)
