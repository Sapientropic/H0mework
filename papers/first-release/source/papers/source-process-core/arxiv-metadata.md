# arXiv 提交元数据

表单字段只收 ASCII，摘要上限 1920 字符（本稿 1916 字符）。以下各块逐字复制进表单。源码包由 `python3 shared/scripts/arxiv_package.py papers/source-process-core` 生成，输出 `build/arxiv/source-process-core-arxiv.tar.gz`；处理器选 **xelatex**，TeX Live **2025**（包内 `00README.json` 已写明）。

PDF 正文保留完整英文摘要；这里是为长度上限删去复述后的表单版，量词与限定语与正文一致。

**Title**

```
The State Is Not the History, the Source Is: Identity, Responsibility, and Minimal Revision in Processes
```

**Authors**

```
Jian Gao (Independent Researcher)
```

**Abstract**

```
A question leaves a demand for a process to discharge; even when readings agree, an answer must say which run it belongs to. Through four levels of identity (reading, source object, occurrence, obligation) we construct a positive chain walked by the source: the original occurrence hands over a complete source program, which is executed and read back; the execution gives birth to its own debt and pays it step by step; after settlement the actual action asks the next question.
  Any rooted tree and constructor generate a whole-tree program whose trace length is its syntactic budget; a syntax-only parser recovers the tree even when a constant-zero constructor makes every tree execute alike. Derivations and module laws generate exactly the evaluation kernel; source words are equal in history iff every tick's (old value, effect) difference is explained by that tick's relations; the common occurrence fixes the unique comparison of implementations.
  The environment and expression of the original occurrence generate a responsibility row with no prior bearer: every execution step is a strict payment and settlement returns the original evaluation. The residual request takes the paid relation's effect as value with positive budget, so its first step is a new birth. The next question carries the visit's complete time, both histories and an inverse criterion for action differences; all actors jointly recover the all-word model; any source program's paid query generates an obligation admission across which physical and low-level inventories are read back; the default run executes this source-generated request and its subtrees, paying node by node. When the old theory can neither express nor realize a demand, the rooted failure generates a minimal extension, initial among admissible extensions, which every typed revision sends into the new root's first write. The theorems are formalized in Lean 4.
```

**Comments**

```
81 pages plus a 16-page supplement of complete proofs, 6 figures and 2 supplementary figures. Lean 4 formalization and reproduction: https://github.com/Sapientropic/H0mework
```

Formal proofs and reproduction materials: https://github.com/Sapientropic/H0mework/tree/234817b3c3f7a1023226e7a4fdb8660ddcbc9d0a (commit 234817b3c3f7a1023226e7a4fdb8660ddcbc9d0a).

**Categories**：主类 `cs.LO`；交叉列入 `cs.PL`。

**License**：建议 CC BY 4.0。

提交前提：H0mework 已推送并公开（Comments 中的链接指向它）；首次在该分类投稿需要背书（endorsement）。
