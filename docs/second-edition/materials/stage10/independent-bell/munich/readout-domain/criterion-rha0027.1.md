# RHA0027.1：同发生 parent 只构造一次

RHA0027 的三个实际 intake 控制已通过，当前 typed Prepared 源恢复未重算任何 pump residual。
其原 `from_record` 路径却为 programme 及两条 Gaussian 腿分别重建同一 native parent。

此修订从同一已核 parent record 构造一枚 `ReferenceLocalPhaseSource`，由它生成原 programme
及两条 Gaussian 腿；原构造器继续检查，最终完整 record 必须与 RHA0025 已发行 snapshot 相同。
同源、同 occurrence 的三个限制直接共用 carrier，不新增数值态、模型或输入 premise。
缓存来源、完整 phase-frame／前驱检查、旧 E 一次及真实 retarded cuts 保持。

代码在实际共享-parent 恢复与迟滞入口检查前先提交冻结；旧首次 intake 与全部冻结输出保持。
