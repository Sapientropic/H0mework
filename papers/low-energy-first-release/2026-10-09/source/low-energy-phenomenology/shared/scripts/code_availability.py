#!/usr/bin/env python3
"""Insert or refresh the code-availability section of each drafted manuscript.

Usage: code_availability.py <H0mework commit> [--only PATH[,PATH...]]...

The section sits immediately before the manuscript's references heading and is
delimited by HTML comments so reruns replace it in place. Per-paper facts (pinned
Homework revisions, aggregator modules, check targets) live in PAPERS below; the
authoritative mapping is H0mework docs/evidence-map.md at the bound commit.

With --only, only the listed files (keys of PAPERS/ENGLISH, e.g.
papers/source-process-core/manuscript.md) are refreshed; without it every file
is refreshed.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BEGIN = "<!-- code-availability:begin -->"
END = "<!-- code-availability:end -->"
REPO = "https://github.com/Sapientropic/H0mework"
TAG = "papers-2026-09"

PAPERS = {
    "papers/source-process-core/manuscript.md": {
        "first_release": True,
        "aggs": ["SourceProcessCore", "SourceProcessCoreHRelease", "SourceProcessCoreAb",
                 "SourceProcessCoreAc", "SourceProcessCoreAd", "SourceProcessCoreAe"],
    },
    "papers/physics-common-source/manuscript.md": {
        "first_release": True,
        "aggs": ["PhysicsCommonSourceHRelease", "PhysicsCommonSourceFRelease",
                 "PhysicsCommonSourceAbRelease", "PhysicsCommonSourceAcRelease",
                 "PhysicsCommonSourceAdRelease", "PhysicsCommonSourceAeRelease",
                 "PhysicsCommonSourceCapRelease", "ConstrainedLocalQuantumV", "ConstrainedLocalQuantumX"],
    },
    "papers/low-energy-phenomenology/manuscript.md": {
        "revs": [("S", "30218c1aea92640eae09b1d9204a09b01a2d0e47"),
                 ("base", "8e29b8e1e58f9846fdddedaaeab9fc8724cdcb87")],
        "aggs": ["LowEnergyPhenomenology"],
        "checks": ["make check"],
        "view": "base",
        "note": "base 是 S 的直接后继战术修复，本文所用模块在两者间逐字节一致。",
    },
    "papers/low-energy-loop-response/manuscript.md": {
        "revs": [("T", "85cb5386ca132818f74d90470d87a252e4a27ea7")],
        "aggs": ["LowEnergyLoopResponse"],
        "checks": ["make check-case2"],
        "note": "",
    },
    "papers/constrained-local-quantum/manuscript.md": {
        "revs": [("T", "85cb5386ca132818f74d90470d87a252e4a27ea7"),
                 ("T2", "958a425f952d6445ecb4123ff553d2a32d5ae010"),
                 ("T3", "f9b733928fb5078ac82430b164dabb8696542e64"),
                 ("V", "6726f385356cb327e7c158687e6e37f5f086fe71"),
                 ("X", "eec031c489f37459742e62a59a26b9866a21caed"),
                 ("K15", "d745a78c89a54632fb29461c51f62d9df7180ec5"),
                 ("K16", "a66cf2d4f1b46465f991401d8e65fde7fab3e4e2"),
                 ("K17", "7e04cfdd4af29c5abe8582a3e0fd93f83b34fd54")],
        "aggs": ["ConstrainedLocalQuantumT", "ConstrainedLocalQuantumV",
                 "ConstrainedLocalQuantumX", "ConstrainedLocalQuantumK15",
                 "ConstrainedLocalQuantumK16", "ConstrainedLocalQuantumK17"],
        "checks": ["make check-5a", "make check-5a-k"],
        "note": "K1–K17 各按其固定提交导出；`check-5a-k` 在 K15–K17 视图重跑三支原程序并与冻结回执逐字段比对。",
    },
    "papers/native-flow/review-20260922-65001/manuscript.md": {
        "revs": [("H", "e60a86058abcb74b7f2225f2383c182be8343785"),
                 ("X", "eec031c489f37459742e62a59a26b9866a21caed")],
        "aggs": ["NativeFlow", "NativeFlowX"],
        "checks": [],
        "note": "",
    },
    "papers/whole-ledger-accounting/manuscript.md": {
        "revs": [("Y", "b81a443863f4d7135ebaca92c5bb7d208ccc18ca"),
                 ("Y1", "296292fc8287a538ef52249277c02dd1edb39742")],
        "aggs": ["WholeLedgerAccounting", "WholeLedgerAccountingY1"],
        "checks": [],
        "note": ("Y1 是 Y 的直接后继，只修正实例 8.7 依赖链上一处 `rfl` 战术（拆出并替换事件携带的"
                 "轨迹等式），命题不变；实例 8.7 的第三阶段付款结算链按 Y1 构建，其余按 Y。"),
    },
    "papers/observation-dynamics/manuscript.md": {
        "revs": [("H", "e60a86058abcb74b7f2225f2383c182be8343785"),
                 ("E", "e53196357f7284ebcbb44c7ed58af0335a1322f0"),
                 ("I", "ca2d0dcbfabd82472423cbc588a73ebb9910d403"),
                 ("X", "eec031c489f37459742e62a59a26b9866a21caed")],
        "aggs": ["ObservationDynamics", "ObservationDynamicsE", "ObservationDynamicsI",
                 "ObservationDynamicsX"],
        "checks": ["make check-obs"],
        "note": "",
    },
}
REFS_HEADING = re.compile(r"^## +(参考文献|References)\s*$", re.M)

# English editions: same facts, same bound commit.
ENGLISH = {
    "papers/source-process-core/manuscript-en.md": ("papers/source-process-core/manuscript.md", ""),
    "papers/physics-common-source/manuscript-en.md": ("papers/physics-common-source/manuscript.md", ""),
}


def first_release_section(commit: str, spec: dict, *, english: bool = False) -> str:
    tree = f"{REPO}/tree/{commit}"
    aggs = (", " if english else "、").join(f"`H0mework.Papers.{name}`" for name in spec["aggs"])
    if english:
        heading = "## Code and data availability"
        body = [
            f"The Lean proofs, direct consumers, reproduction programs and evidence accompanying this paper "
            f"are bound to H0mework commit `{commit}`, under Apache-2.0 for original material. "
            f"The [first-release map]({tree}/docs/first-release-map.json) records each claim’s source revisions, "
            f"declarations, resources and acceptance results. Third-party attribution and publication transforms "
            f"are specified in [NOTICE]({tree}/NOTICE) and the [byte-identity contract]({tree}/docs/evidence-publication.md).",
            f"The paper’s versioned proof entries are {aggs}. Each entry is checked in its own Lean environment. "
            f"The [reproduction guide]({tree}/docs/first-release-reproduction.md) specifies the pinned toolchain, "
            "dependencies and commands.",
            "Run `make check-first-release-entry` from the repository root for entry checks. "
            "`make build-first-release` builds the proof selection; `make trust-first-release` audits the complete "
            "dependency closures of the selected declarations. `make check-first-release-full` performs the complete "
            "proof and scientific checks for both first-release papers. Bell and quantum checks can be run separately "
            "with `make check-first-release-bell` and `make check-first-release-quantum`. Original executions, fresh "
            "verification outputs and failure verdicts retain their separate identities.",
        ]
    else:
        heading = "## 代码与数据可得性"
        body = [
            f"本文的 Lean 证明、直接消费者、复现程序与证据采用 H0mework 固定提交 `{commit}`，原创材料许可为 Apache-2.0。"
            f"各主张的来源版本、声明、资源和验收结果见[首发映射]({tree}/docs/first-release-map.json)。"
            f"第三方归属与公开变换见 [NOTICE]({tree}/NOTICE) 和[字节合同]({tree}/docs/evidence-publication.md)。",
            f"本文的版本化证明入口为 {aggs}，各入口在独立 Lean 环境中验收。"
            f"固定工具链、运行依赖与命令见[首发复现指南]({tree}/docs/first-release-reproduction.md)。",
            "在仓库根目录运行 `make check-first-release-entry` 检查入口；`make build-first-release` 构建证明选集，"
            "`make trust-first-release` 审查所选声明的完整依赖闭包。`make check-first-release-full` 执行两篇首发论文的"
            "完整证明与科学检查，Bell 和量子检查也可分别运行 `make check-first-release-bell` 与 "
            "`make check-first-release-quantum`。原始执行、新验证输出与失败判决保留各自身份。",
        ]
    return BEGIN + "\n" + heading + "\n\n" + "\n\n".join(body) + "\n" + END + "\n\n"


def section_en(commit: str, spec: dict, note: str) -> str:
    if spec.get("first_release"):
        return first_release_section(commit, spec, english=True)
    revs = ", ".join(f"{tag} = `{rev}`" for tag, rev in spec["revs"])
    aggs = ", ".join(f"`H0mework.Papers.{a}`" for a in spec["aggs"])
    checks = "; ".join(f"`{c}`" for c in ["make bootstrap && make build", *spec["checks"],
                                          "make check-map"])
    first = spec.get("view", spec["revs"][0][0])
    lines = [
        BEGIN,
        "## Code and data availability",
        "",
        f"The formal proofs, exact programs and frozen receipts of this paper are public in "
        f"H0mework ({REPO}) at commit `{commit}` (tag `{TAG}`), licensed under Apache-2.0. "
        "H0mework is exported from fixed commits of the private research repository Homework: "
        "source files rewrite only local `import` and resource addresses; published receipts "
        "replace runtime paths with relative ones, leaving computed data and results unchanged, "
        "and the export map records the original byte digests (see the repository's "
        "`docs/evidence-publication.md`). The fixed commits used here are "
        f"{revs}. Declaration names and source paths cited in the text and "
        "appendices refer to the original paths inside these commits.",
        "",
        f"The paper entry modules are {aggs}; their `import` closure is the machine-checked "
        "scope of the bound public selection. The toolchain is pinned to Lean 4 `v4.33.0` and mathlib "
        f"`db584cd6d46c92f209a44c0f1c829460d327499d`. Reproduction: {checks}; "
        "`make check-map` checks the pinned-source identity, artifact hashes and published receipt "
        "contents of every export. To restore a source file at its "
        f"original path, run `python3 tools/source_view.py --output DIR --at {first} "
        "--path PATH` (PATH is the path inside the research repository); apart from receipts with "
        "a registered publication transform and the resource digests that reference them, the "
        "output is byte-identical to the file in the fixed commit; with `--exact` and the original "
        "files from the research repository, every original receipt can be checked byte by byte.",
        "",
        note,
        END,
        "",
    ]
    return "\n".join(lines) + "\n"


def section(commit: str, spec: dict) -> str:
    if spec.get("first_release"):
        return first_release_section(commit, spec)
    revs = "、".join(f"{tag} = `{rev}`" for tag, rev in spec["revs"])
    aggs = "、".join(f"`H0mework.Papers.{a}`" for a in spec["aggs"])
    checks = "；".join(f"`{c}`" for c in ["make bootstrap && make build", *spec["checks"],
                                          "make check-map"])
    first = spec.get("view", spec["revs"][0][0])
    lines = [
        BEGIN,
        "## 代码与数据可得性",
        "",
        f"本文的形式化证明、精确程序与冻结回执公开于 H0mework（{REPO}），"
        f"对应提交 `{commit}`（标签 `{TAG}`），许可 Apache-2.0。H0mework 从私有研究仓 Homework 的固定提交"
        "导出：源码只改写本地 `import` 与资源地址；公开回执把运行路径改为相对地址，计算数据与结果不变，"
        "原始字节摘要记于导出映射（见该仓 `docs/evidence-publication.md`）；"
        f"本文所用固定提交为 {revs}。"
        "文中出现的形式化声明名及源码路径均指这些提交内的原文件。",
        "",
        f"论文入口模块为 {aggs}，其 `import` 闭包即上述绑定选集的机器验证范围。"
        "工具链固定为 Lean 4 `v4.33.0` 与 mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`。"
        f"复现命令：{checks}；其中 `make check-map` 核对全部导出的固定源身份、工件哈希与公开回执内容。"
        f"按原路径还原源码可运行 `python3 tools/source_view.py --output DIR --at {first} "
        "--path PATH`（PATH 为原仓内路径），除登记了公开变换的回执及引用它们的资源摘要外，"
        "输出与固定提交的原文件逐字节一致；加 `--exact` 并提供源仓原件，可逐字节复核全部原始回执。",
    ]
    if spec["note"]:
        lines += ["", spec["note"]]
    lines += [END, ""]
    return "\n".join(lines) + "\n"


def main():
    argv = sys.argv[1:]
    only = set()
    pos = []
    i = 0
    while i < len(argv):
        if argv[i] == "--only":
            i += 1
            if i >= len(argv):
                sys.exit(__doc__)
            only.update(p for p in argv[i].split(",") if p)
        else:
            pos.append(argv[i])
        i += 1
    if len(pos) != 1 or not re.fullmatch(r"[0-9a-f]{40}", pos[0]):
        sys.exit(__doc__)
    commit = pos[0]
    jobs = [(rel, section(commit, spec)) for rel, spec in PAPERS.items()]
    jobs += [(rel, section_en(commit, PAPERS[zh], note)) for rel, (zh, note) in ENGLISH.items()]
    known = {rel for rel, _ in jobs}
    if only:
        unknown = only - known
        if unknown:
            sys.exit(f"unknown --only targets: {sorted(unknown)}")
        jobs = [job for job in jobs if job[0] in only]
    for rel, block in jobs:
        path = ROOT / rel
        text = path.read_text()
        if BEGIN in text:
            head, rest = text.split(BEGIN, 1)
            tail = rest.split(END, 1)[1].lstrip("\n")
            text = head + block + tail
        else:
            match = REFS_HEADING.search(text)
            if match is None:
                sys.exit(f"no references heading in {rel}")
            text = text[:match.start()] + block + text[match.start():]
        path.write_text(text)
        print("updated", rel)


if __name__ == "__main__":
    main()
