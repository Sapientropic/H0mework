# 典范社会总定理：选集与验收

来源、原路径恢复和完整类型归[逐主张映射](generated-society-map.json)，可执行命令归[复现](generated-society-reproduction.md)。本稿主体为 G0–G9，G10–G12 仅接受实际引用接口。

## 本地状态

完整来源接入、公开／原字节逆恢复、原 map 身份下的 11,921-job Lean 构建、trust=0 metadata 审查和完整类型 DAG 验收均已通过；当前 map authority 修正见下方复核记录。

| 对象 | 实际验收 |
| --- | --- |
| 原来源闭包 | e60 1077、AB 1036、MV5 接口 1583 个模块身份；全部 imports 完整 |
| 公开 owner | 3213 个，新增 2923 个、复用 290 个旧 owner；原证明正文与定义保持 |
| 原材料 | 12 个 epoch 身份、8 份独立文档；保持原字节及原认证状态 |
| 原路径视图 | 公开视图和原字节精确恢复均通过 |
| 原论文合同 | 整账法 40 主张／13 包／5025 类型及一比特 11 主张／23 control 类型的原 `require-ready` 入口通过 |
| 工具 | 385 项完整工具测试通过；固定 Git 配置兼容补强另经 7 项 focused 测试通过 |
| 默认覆盖 | Lake 实际覆盖检查通过：50543 模块，新增 2926 个默认模块（含三个论文入口） |
| H0 独立验收 | `entry --require-ready` 通过：194 映射项、75 资源、535 完整类型声明；构建、trust、types 输入身份保持不变 |

原来源记录中的 strict／T1 与本次 H0 执行分别记账。社会总口的真实公理身份为 `propext`、`Classical.choice`、`Quot.sound`；本次声明审查按完整 type/value 与归纳／互递归元数据验收。

## 缓存保全

[独立逐片报告](../evidence/generated-society/acceptance/cache-preservation.json)确认全部 49055 个旧模块的 owner、源码、递归 imports、强弱选项、资源、默认覆盖和分片归属不变。61 个旧分片的完整记录、指纹和缓存键全部相同；只新增 `s3-09`，2926 模块，预计 3.45 runner 小时。总计划为 11 阶段、62 片，每阶段最多 20 片。

| 身份 | 指纹 |
| --- | --- |
| 迁入前完整选集 | `345402a3c337566e053d60f264f8dca9487d594f2adfaf1daec37ed5765ec9f2` |
| 本稿加入后的完整选集 | `f0b3feec6ad427afa32bb28cbef5c06b762c9b56fad196a8bf5299b7603b6a82` |
| 最终公开 export-map | `e9ab6f1e9b800573a67171eacd8bedd5533a36ec444220965b1bb55829bab526` |
| compatibility | `23f23031eec00a03d30ee31d` |
| CACHE_VERSION | `lean-parts-v1` |

工具链、manifest、工作流及缓存算法逐字保持。固定布局只追加 2926 行；未执行 `--rebalance`、远端 seal/save/prune 或缓存删除。远端 76 项资产的前后 metadata 完全一致。13 处 `open private … from` 地址迁移、9 个文件的非计算代码生成标记均逐条可逆，未改变数学声明或证明体。

Bell 与量子载体的原成功报告、原程序／配置、输入选择和资源身份保持，实际双引擎比较见[科学输入核对](../evidence/generated-society/acceptance/scientific-input-binding.json)。`full_replay=false`，本篇没有科学重跑。最近远端科学 artifact 已按原七天策略过期；较早本机回执在现有 verifier 中因历史 Makefile 差异保留原 `miss` 状态，均未改写为新执行或新缓存命中。

## 远端 CI 身份

只读核实了[原完整内核运行 39025063045](https://github.com/Sapientropic/H0mework/actions/runs/39025063045)、[迁入前当前选集验收 39036946868](https://github.com/Sapientropic/H0mework/actions/runs/39036946868)及[最近成功复用 39771257871](https://github.com/Sapientropic/H0mework/actions/runs/39771257871)。现存旧 seal 实际绑定 `587596253b08df5461d398b4b4505837cce1fbd8`／run `39036946868`。

本稿的新指纹没有执行远端 CI，也没有取得远端 seal。新提交的远端完整验收须在获准推送和运行后单独取得。

## 2026-11-01 authority recheck

并行写作窗口后来更新了 `claims.md` 的书面对照段；本地 map 的 `claims_authority` 已同步到 publish 当前提交 `054d2ee92f226e36166cb33cb5ab8b772fcca39f` 与当前 SHA。另恢复了 3 个导入源码的原始 EOF 字节，使 export-map 与实际文件完全一致。三份受影响源码分别通过 `lake env lean --root=.. --trust=0 -DwarningAsError=true` focused 检查；当前 map 的 `entry --require-ready` 重新通过（194 映射项、3213 owner、75 资源、535 完整类型声明）。完整 11,921-job 语义构建的原回执保留；authority 修正只改变 map 元数据，未重新冒充新的全量构建。逐项回执见[authority recheck](../evidence/generated-society/acceptance/authority-recheck.json)。
