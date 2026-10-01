# CI 与增量构建

[`ci.yml`](../.github/workflows/ci.yml) 处理 `main` 推送、PR 更新和手动运行。同一分支或 PR 的新运行取消旧运行；多个提交一次推送对应一次工作流。README、横幅、许可及作者指南的纯展示改动跳过工作流，冻结来源文档仍参与检查。

## 分工与完整覆盖

[`ci_plan.py`](../tools/ci_plan.py) 的 `make_plan` 从 `lakefile.toml` 的默认库及真实 import 计算模块闭包，沿用各模块的资源依赖、编译参数与库归属。非默认的历史失败库继续通过复现指南中的命令检查。

构建按依赖顺序分为共享基础、并行分片和论文入口汇总。`partition` 将跨并行分片的依赖闭包归入共享基础；化学中的分组计算按组号分成四片，其余并行片覆盖算术、Navier–Stokes、物理和结构模块。每片拥有独立的模块集合，共享基础只编译一次。新增论文入口纳入汇总；新模块按同一规则分配。

并行片同时最多运行四个 job。下游 job 读取本次运行中上游已验收的产物；汇总完成后执行 `lake --no-build build`，要求全部配置的默认目标均已满足。每片先用 Lake 检查产物是否有效，需要时再重编；缓存命中也执行这项检查。

冻结证据 job 独立运行导出映射校验、低能唯象复核与工具测试。私有期间，Lean jobs 保留手动触发规则；公开后，证明、资源或构建配置的改动自动执行 Lean jobs。仅修改复核脚本或冻结来源文档时执行证据检查。手动运行执行全部检查。

## 缓存与资源

[`lean-part.yml`](../.github/workflows/lean-part.yml) 分别缓存固定依赖与各片证明产物。依赖缓存按平台、工具链及 manifest 区分；证明缓存键由该片模块、传递依赖、实际资源内容和有效编译配置生成。提交号与展示文档变化不改变证明缓存键。旧同平台、同工具链的分片缓存可供 Lake 增量检查，资源或上游证明变化会传到消费者。

分片存档保存所属模块的 `.olean`、`.ilean`、生成 C、trace 与哈希文件，排除临时 `.setup.json`，并使用 zstd 压缩。精确缓存命中且 Lake 检查通过时，直接传递已有存档，省去重新压缩。job 间传递的短期工件保存一天。`completed_setup_files` 仅清除已有更新编译 trace 的 setup 文件，避免按文件年龄删除仍在使用的编译输入。

首次云端运行、缓存过期或被回收后，需要重新编译缺失的产物。共享基础的冷构建仍较大；分片缓存减少后续迁移独立论文时的重复工作。GitHub 缓存容量及七天未访问回收规则见[官方缓存说明](https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching#usage-limits-and-eviction-policy)。本仓配置不增加收费缓存容量。

本地查看分工、检查一片已有产物：

```bash
python3 tools/ci_plan.py plan
python3 tools/ci_plan.py build --part physics --check-only
```
