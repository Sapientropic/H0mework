#!/usr/bin/env python3
"""Refresh only Case 2 code availability and bilingual Zenodo metadata."""
import argparse
import json
import re
import sys
from pathlib import Path

PAPER = Path(__file__).resolve().parents[1]
ROOT = PAPER.parents[1]
sys.path.insert(0, str(ROOT / 'shared/scripts'))
import code_availability as code
import zenodo_metadata as zenodo

COMMIT = 'ba591b43e13a59ac676919aa153569615f8d4cb2'
ZH = 'papers/low-energy-loop-response/manuscript.md'
EN = 'papers/low-energy-loop-response/manuscript-en.md'
SOURCE_S = '30218c1aea92640eae09b1d9204a09b01a2d0e47'
ENTRY = f'{code.REPO}/blob/{COMMIT}/Lean/H0mework/Papers/LowEnergyLoopResponse.lean'
MAP = f'{code.REPO}/blob/{COMMIT}/tools/export-map.json'
ACCEPTED = '234817b3c3f7a1023226e7a4fdb8660ddcbc9d0a'

def added_availability(english=False):
    fixed = f'{code.REPO}/blob/{ACCEPTED}/docs/first-release-map.json'
    tick = chr(96)
    entries = ['PhysicsCommonSourceAcRelease', 'PhysicsCommonSourceAdRelease', 'PhysicsCommonSourceAeRelease']
    aggs = ', '.join(tick + 'H0mework.Papers.' + name + tick for name in entries)
    if english:
        return (
            f'Q5 and the original five-factor/Noether half-axis and real-signal foundations of Q6 '
            f'reuse the accepted same-byte selection at H0mework {tick}{ACCEPTED}{tick} '
            f'([first-release map]({fixed}), phys.P27/P29/P33). '
            f'The fixed observation {tick}51867c59042460646e57d5ead4c405cbca05c240{tick} verifies unchanged target bytes '
            'and the later root-supplement acceptance; each receipt retains its own commit. '
            f'The versioned entries are {aggs}. '
            'Use the fixed first-release reproduction guide and its actually registered checks.\n\n'
            'The later actual nonlinear Q6 source retains Homework snapshot '
            f'{tick}71e94e8261d67cf4849a05eb14ac95aa2f7dcbb9{tick} and each producer’s recorded epoch. '
            'Its complete written derivation is in Section 13. The 21 selected new roots and their original '
            'certifications are recorded in this edition’s release selection. Their public H0 export and '
            'complete import/resource acceptance are pending; the old Case 2 entry covers Q1–Q4. '
            'The editable materials include the precise source/target bindings and export request.'
        )
    return (
        f'Q5及Q6原五因子／Noether半轴与实信号前置链复用H0mework {tick}{ACCEPTED}{tick} '
        f'的已验收同字节选集（[首发映射]({fixed})，phys.P27/P29/P33）。'
        f'固定观察{tick}51867c59042460646e57d5ead4c405cbca05c240{tick}核对目标字节保持及后续root-supplement验收；'
        f'两份回执保各自真实提交。版本入口为{aggs}，复现采用固定首发指南及其实际登记的检查命令。\n\n'
        f'Q6后续实际非线性源保Homework {tick}71e94e8261d67cf4849a05eb14ac95aa2f7dcbb9{tick}核读快照及各生产体的真实epoch，'
        '完整书面推导在第13节。本版选集登记21枚新增根与原认证；其H0公开迁入和完整import／resource验收仍待绑定。'
        '旧Case 2入口覆盖Q1–Q4；可编辑材料交付精确source／target对应及迁入需求。'
    )

def refresh_code():
    spec = dict(code.PAPERS[ZH])
    spec['note'] = (
        f'本文消费的 Case 1 前作 L1–L17 保持 Homework S=`{SOURCE_S}`。'
        f'本稿[公开总入口]({ENTRY})和[逐文件导出映射]({MAP})给出原来源与公开消费者对应；'
        '固定提交中的原认证与本版局部重放分别登记，不将局部重放记为完整生产链的重新认证。'
    )
    note_en = (
        f'The Case 1 results L1–L17 used here retain Homework S=`{SOURCE_S}`. '
        f'The [public paper entry]({ENTRY}) and [file-level export map]({MAP}) '
        'bind original sources to public consumers. Original certifications at the fixed commit '
        'and the local replays for this edition retain their separate execution identities.'
    )
    for rel, block in [(ZH, code.section(COMMIT, spec)),
                       (EN, code.section_en(COMMIT, spec, note_en))]:
        path = ROOT / rel
        if rel == ZH:
            block = block.replace('本文的形式化证明、精确程序与冻结回执公开于',
                                  '本文Q1–Q4的形式化证明、精确程序与冻结回执公开于')
        else:
            block = block.replace('of this paper are public in', 'for Q1–Q4 are public in')
        block = block.replace('本文所用固定提交为', 'Q1–Q4所用固定提交为')
        block = block.replace('文中出现的形式化声明名及源码路径均指这些提交内的原文件。',
                              '这四项主张的形式化声明名及源码路径指上述提交内的原文件。')
        block = block.replace('The fixed commits used here are', 'The fixed source for Q1–Q4 is')
        block = block.replace('Declaration names and source paths cited in the text and appendices refer to',
                              'Declaration names and source paths for these four claims refer to')
        block = block.replace(code.END, added_availability(rel == EN) + '\n' + code.END)
        text = path.read_text()
        assert text.count(code.BEGIN) == text.count(code.END) == 1
        head, rest = text.split(code.BEGIN, 1)
        tail = rest.split(code.END, 1)[1].lstrip('\n')
        path.write_text(head + block + tail)
        print('updated', rel)

def refresh_metadata():
    out = zenodo.write('low-energy-loop-response', 'manuscript.md', 'manuscript-en.md',
                       ['build/low-energy-loop-response-en.pdf', 'build/low-energy-loop-response.pdf'])
    text = out.read_text().replace('由 `python3 shared/scripts/zenodo_metadata.py` 从正文生成',
        '由本稿 `scripts/refresh_release.py --metadata-only` 调用共享生成器，从中英文正文生成')
    text = re.sub(r'(?m)^- Relation：Is supplemented by；Identifier：.*$',
        f'- Relation：Is supplemented by；Identifier：{code.REPO}/tree/{COMMIT}；Scheme：URL；Resource type：Software\n'
        '- Relation：References；Identifier：10.5281/zenodo.23210292；Scheme：DOI；Resource type：Publication\n'
        f'- Relation：References；Identifier：{code.REPO}/blob/{COMMIT}/Lean/H0mework/Papers/LowEnergyPhenomenology.lean；'
        'Scheme：URL；Resource type：Software', text)
    text = text.replace('## Files（上传）\n\n', '## Files（上传）\n\n'
        '- `papers/low-energy-loop-response/build/low-energy-loop-response-editable.zip`（中英文正文、图源、构建材料和公开证据绑定）\n')
    text = text.replace('已有本文的 DOI 时填写原 DOI；没有时选择 No，',
        '本文尚未提供公开或预留 DOI；由作者在发布草稿中确认。没有已有 DOI 时选择 No，')
    text = text.replace('## Version\n\nv1', '## Version\n\nv1\n\n'
        'Case 1 按实际首发题名、作者与 v1 引用，消费范围固定为 S 的 L1–L17；尚未取得其真实 DOI，使用固定公开证明入口。')
    relation = f'- Relation：Is supplemented by；Identifier：{code.REPO}/tree/{COMMIT}；Scheme：URL；Resource type：Software'
    text = text.replace(relation, relation + '\n'
        f'- Relation：Is supplemented by；Identifier：{code.REPO}/tree/{ACCEPTED}；Scheme：URL；Resource type：Software')
    text = text.replace('# Zenodo 上传元数据\n', '# Zenodo 上传元数据\n\n'
        '**本地成稿；整体公开上传待Q6证据绑定。** Q1–Q4、Q5及Q6前置链已按各自公开验收固定；'
        'Q6新增21根及完整公开闭包需先完成h0-evidence-request.md，再核对本表的最终代码关系和上传身份。\n', 1)
    text = text.replace('Formal proofs, exact programs and frozen receipts are in the code repository above;',
        'Public proofs, exact programs and receipts for Q1–Q4, Q5 and the accepted Q6 foundations '
        'are in the fixed repositories above; the new Q6 evidence request is included in the editable materials;')
    out.write_text(text)
    print('wrote', out.relative_to(ROOT))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--code-only', action='store_true')
    parser.add_argument('--metadata-only', action='store_true')
    args = parser.parse_args()
    if args.code_only and args.metadata_only:
        parser.error('choose one limited operation')
    if not args.metadata_only:
        refresh_code()
    if not args.code_only:
        refresh_metadata()

if __name__ == '__main__':
    main()
