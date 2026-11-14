# 忠实表示与精确反演 · Proof and source reproduction

逐项来源见 [R1–R62 与接口 I–V](exact-realization-map.json)。[固定选集](../checks/exact-realization-selection.json) 包含原生产证明、直接消费者和所用回执。各纪元在独立 Lean 环境验收。

Run from the repository root with the pinned Lean toolchain and dependency manifest.

```sh
make bootstrap
lake -d Lean build ExactRealization
python3 tools/exact_realization.py entry
python3 tools/exact_realization.py build --output .local/exact-build
python3 tools/exact_realization.py trust --output .local/exact-trust
python3 tools/exact_realization.py types --output .local/exact-types
make check-map
```

The type report contains the complete Lean expressions, declaration owners and axiom dependencies. Build and trust use the repository's existing Lake output and freshness checks.

```sh
python3 tools/exact_realization.py source --output .local/exact-source
```

The public source view writes each original layout under its fixed revision. For grouped `open private … from` commands, the map records every relocated module selector. The exact source view restores the separately pinned historical bodies where the build uses an adapted body. To verify and restore original receipt bytes, add `--exact --private-originals PATH`, where the private originals are named by their recorded SHA-256. Published views replace machine paths in certificates and logs while preserving numerical values and original success and failure states. The [P5 realization report](../evidence/exact-realization/original/P5/realization.json) is a byte-for-byte copy of the original archive. Its [provenance record](../evidence/exact-realization/original/P5/verification.json) identifies the archive revision and digest.

See the [CI cache comparison](../evidence/exact-realization/acceptance/cache-preservation.json) for the Linux shard keys and the scientific replay comparisons.
