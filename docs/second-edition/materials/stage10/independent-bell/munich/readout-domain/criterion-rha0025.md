# RHA0025：原 primitive 与完整曲线重新发行仪器入口

旧 source-issued inlet 的 441MB 缓存属于原首次 Ready 及两 pump 的同源发生。
它不是下一 high-poll 的 generation1，旧 executable bindings 也不作为当前证书使用。
原始载荷 SHA `e9667f34d6d8743ee9a7c3baaf49d7210ab637f37d04255a46141483d35e5128`
及两 pump witness SHA `e638e87134e1608511e39b0a846c8aa6c4096a5dc16a2cde45d6ac47da0e5f4f` 保持。

从原 PRM 的 source-owned basis recipe 和完整 raw 控制重新构造 `NativeToneFrame`、
`ReferenceAtomicClockSource`。除旧 `source_bindings` 外，全部数学源字段必须逐项相同。
新 source 从 primitive 自产入态；旧 Ready 矩阵、旧 pump endpoint 和旧 gate endpoint 均不作输入。
这不是给旧证书改 hash，也不把首次 Ready 转换为下一 high-poll。

旧首 poll 只提供 `untrusted_pieces`、时间 chart 与精度。当前完整 CP checker 重新核曲线，
新 Ready 由同一首 poll 的源 PC／queue／flag 作用生成。新完整 local programme 再按所有
source-issued factor、两侧及两个 pump 的顺序检查旧 raw curve／shared witness；
每个下一 phase 只能由新上游证书发行。原 waveform、参考 Gamma、相位时间和完整母源保持。

门前入口阶段将旧 density curve 的 pieces 交给当前源；初始矩阵由新 pump 口自产。
完整局部残差与源 Gamma 价格重算，`PreparedRetardedGaussianInlet` 按原两 flight 与真实切口
发行新 typed inlet。旧输入误差由该构造携一次；局部数值终态不被直接信任。

默认检查至两 pump；`ready/pumps/inlet` 是具名执行阶段，输出位置可显式 override。
每次 attempt、日志与结果独占新目录；大曲线和 source snapshot 保在 ignored 本地 state，
Git 只保存科学源码及小回执。实际执行前先提交冻结，不读新事件、ETH 或 publish，不外联。
原 source／whole-ledger／tick16→17 保持，实际 raw-lambda 会员和唯一硬件身份仍按完整联合域裁决。
