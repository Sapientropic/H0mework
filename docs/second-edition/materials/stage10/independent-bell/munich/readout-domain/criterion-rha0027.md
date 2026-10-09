# RHA0027：已核源曲线直接消费到真实入口

RHA0025 的完整 pump 重核结果与原未信任 witness 区分。后续实例恢复可消费同一已检查证据，
不重新运行 pump solver，也不把未检查的 endpoint、hash 或成功布尔值当成数学证明。
冻结首回执绑定实际完成的 RHA0025 输出、原 source payload、固定科学代码和全部相关依赖；
仅恢复这枚既有源的已付缓存。原构造器继续核每个 source frame、前驱、误差与母源 identity。
这是已生成 generation0 源的证据复用，不是新 producer 或 generation1 类型转换。

完整局部 density checker 在 `certify` 成功后保一份 detached 结果。
`verify` 默认只在同一完整 source record、相同 curve／precision／价格及闭包下复用该份检查；
显式 `recheck=True` 重验同一曲线。修改 endpoint、价格、source 或执行闭包均不得命中。
cache miss 继续执行原完整 residual，不增加启发式 fallback。

`PreparedRetardedGaussianInlet` 在同一进程收到刚检查过的十份证书时直接消费这些结果，
避免将每份完整 residual 无条件再算一次。数值误差、Gamma 价、真实 cuts 和旧 E 一次不变。
相关 producer／consumer 与正例、显式 override、形似反例在实际入口执行前提交冻结。
旧冻结输出保持；不读 ETH、不改 publish、不外联，不变更 source/root／whole-ledger／tick16→17。
