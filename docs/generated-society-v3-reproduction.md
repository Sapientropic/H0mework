# 典范社会总定理第三版复现

第三版的[逐项来源映射](generated-society-v3-map.json)给出公开 Lean 声明、直接消费者、各自的原路径与纪元，以及可由内核独立核对的完整类型。G0–G27、G2a 和引用接口继续使用[既有证明选集](generated-society-reproduction.md)的七个环境与历史原件。

| 论文位置 | 形式证明入口 | 固定公开快照 |
| --- | --- | --- |
| 命题 3.2、定理 4.4、定理 5.13；附录 C14–C19 | `H0mework.Papers.GeneratedSocietyMInfinity` | [2d6fbc96](https://github.com/Sapientropic/H0mework/tree/2d6fbc96e33b7c4c3cfd91104fda74e3caeda045) |
| §2.3、§3.5 的四域主体来源；附录 G.4 | `H0mework.Papers.SocietyBookCrossDomainG8` | [fd6147f8](https://github.com/Sapientropic/H0mework/tree/fd6147f8c337d88ebf72d91ddadef0aa601e6c2e) |

第一组采用实际编译的 `e60a8605` 源码，观察因子化模块来自 `df421ff6`。续生投影和活跃决议分类在后期收稿上限有独立版本，可编辑包的 `records/m7-source-binding-v3.json` 分别记录阅读与编译身份。第二组使用原 `f9493be3` 的四域直接构造及 G8 联合消费者。

## 执行

在含固定公开快照的仓库克隆中运行。每条命令使用独立的输出目录。

```sh
make check-map
python3 tools/generated_society_v3.py entry --output .local/society-v3/entry
python3 tools/generated_society_v3.py build --output .local/society-v3/build
python3 tools/generated_society_v3.py trust --output .local/society-v3/trust
python3 tools/generated_society_v3.py types --output .local/society-v3/types
```

`entry` 核对发布文件、七包原验收、第三版验收、公开身份和原字节恢复。已有 Homework 检出时，可为该命令增加 `--homework-repository <path>`，逐项对照固定 Git 原件。`build` 使用现有 Lake 与固定依赖缓存。`trust` 检查 freshness 后在 `--trust=0` 下检查完整类型、证明体及归纳声明元数据。`types` 在 Lean 中重建完整表达式并验证定义相等。

## 回执与缓存

Darwin arm64 本地执行通过。两组分别覆盖 1,078 与 213 个仓内 imports 模块，新增范围逐项检查 123 个完整类型。实际依赖公理为 `propext`、`Classical.choice`、`Quot.sound`，`unsafe` 与 `partial` 均为 0。执行回执与类型可从[映射](generated-society-v3-map.json)中的 `acceptance` 打开。

[缓存保全记录](../evidence/generated-society-v3/acceptance/cache-preservation.json)保存 Linux 的全部 106 个分片缓存键。全部 62,694 个默认构建模块、11 个阶段和完整选集指纹与既有 CI 一致。成功选集见 [CI 43159515852](https://github.com/Sapientropic/H0mework/actions/runs/43159515852)。Bell 与量子载体使用原成功产物的输入身份，`full_replay` 保持 `false`。
