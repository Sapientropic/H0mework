# 完整统计纤维与公开读出认证

四个完整 single 区间生成同源协方差域，joint 区间生成共同相位纤维；源域直接生成配对读出。
本目录消费公开 Table S-II 的完整计数与 po0003 原统计域。当前责任由
[NIST active card](../../investigation/README.md)维护。

## 源与完整相位

[ef0003](criterion.md)保留全部六训练 CI，四 single 和两 joint 都可在各自完整区间内变化。
坐标 m,z,x,r,e 描述同一两偏振 TMSV、共同实 Jones frame 与 scalar losses；
k=(1−2λ)T 保留逐 pulse phase mixture，再消费五 fresh pulse any-click 与独立 OR 背景。

[PhaseFiber](PhaseFiber.lean)从原 RawSource 与合法 k 内部生成 λ/Snapshot。
两训练口的资格等价于物理 k 区间和共同线性 slab；g=0、T=0 与 pure-mode 边界完整保留。
[TrainingChart](TrainingChart.lean)从同一实际源生成并反解四均值，完整区间等价于八 halfspaces；
数据的严格增序生成 z>0、R²>0。
[phase](phase-certification.json)与[chart](chart-certification.json)分别由独立审计认证，
fresh trust0/werror 与标准三公理通过。CLI认证有效；此目录的 LSP 因无 toolchain 祖先未成功。

[CovarianceSource](CovarianceSource.lean)从五个原始 m,z,x,r,e 与基本物理界内部生成
arctan 共同轴、原 RawSource 和合法 phase，并精确读回五坐标、全部 cells/N5。
z>0 正规图谱的全部合法 tuple 可生成原源；pure nV=0/T=0 与全部 λ 读出等价保留。
[独立认证](covariance-source-certification.json)支付783声明、九文件fresh strict与16项独立控制；
源、角度见证和目标readback等式均不由调用者供应。

## 已认证训练纤维

[交叉证书](cross-verification.json)逐项重算主/独两棵树的全部 **81,922 节点**，
支付初始全域、每次 contractor 的 outer 性、完整 partition、排除依据及全部 cap/boundary。
主保留15,061块，独立保留11块；每个保留块包含同源基域、共同 k 和配对读出。
完整外覆盖成立；外包块不必整体可行，资源 cap 保留其收紧责任。

512个成员全部从各自 native recipe 重生。主256个 Gaussian 训练包络全部包含；
实际 Γ/Fock 前缀6加原尾有128个完整包含、128个边界包络。独立256个实际 Born 包络全部包含。
边界包络保留，不将它们当作实际 Born 完整包含证人。

**141项实际 Born 具体越界反证统一留出包含**：主47项、独立94项。
例如独立 member6 的 j01≈0.00016726781197301952，严格高于原上界0.00016712361973910759。
这些源满足全部六训练 CI；因此训练约束不蕴含全部留出落带。
非空、完整外覆盖与共享 phase/no-signaling 关系已签收；整个源族没有被拒绝。

## 全数据交集

[ef0003.1](criterion-all-data.md)另外生成 F_all=F_train∩全部公开留出 CI。
同 local setting 的两 single CI 求交，四 joint 同时约束同一 k；原预算和原训练首算保持。
[主](primary_all_data.py)和[独](independent_all_data.py)分别生成 source cover、全数据成员与配对读出；
[验收器](verify_all_data.py)分别认证外覆盖、具体非空、源歧义与可认证关系。
这是回顾性全数据相容性，训练统一预言的反证仍保原身份。

[完整验收](all-data-verification.json)逐项重算另81,922节点及128个成员。
主1790排除块、14,595保留块；独立22,996排除块、1581保留块，全部边界和cap保留。
每条路径64个 actual Γ/Fock 源均满足十二项原 exact CI及完整outcomes。

**每条路径有41个严格正CH、23个严格负CH源。**
[具体符号证书](all-data-sign-certification.json)另从各 native recipe 重生每路径正负各一个源：

| 成员 | etaA | 实际 Born CH（约） | 十二原 CI |
| --- | --- | --- | --- |
| 每路径 member0 | 11/16=.6875 | −1.80599e−5 | 全部包含 |
| 每路径 member2 | 23/32=.71875 | +8.0978e−7 | 全部包含 |

两路径 native 坐标不同；相同etaA不等于同一完整源。
具体证人反证整个 F_all 的统一严格正和统一严格负，源域符号为 `mixed_certified`。
这是当前十二CI合同的符号分歧；其他公开校准信息与NIST原实验统计分析各守自己的检验口。

## 消费与复核

[verify_fiber](verify_fiber.py)的 `consume` 核固定科学源码、原 CI、两首原字节、源绑定与独立证书。
复制路径 override 只换证书位置；disable 关闭本字段，伪通过或外国脚本不能替换固定消费者。
[readiness](../../../readiness.py)的 `public_statistical_fiber` 消费认证字段。
实际 apparatus optimum 继续按[原 r6 合同](../../results-r0006.1.md)验收。

[all_data_signs](all_data_signs.py)组合完整全数据覆盖和具体符号证书，
[covariance_source_certify](covariance_source_certify.py)消费源生成内核。
[实际readiness回执](../../../evidence/readiness-full-fiber-ef0003.1.json)的三个新字段均有效，
`conditional_public_source_fiber_certified=true`；原名义最优性保持有效DEVIATION，CLI退出1。
18项readiness intake控制、38项全数据/符号控制与27项训练纤维控制通过。

源生成证书的历史编译环境保留。快消费者严格核工具链、候选和4386个实际import来源；
Lake新增的独立CPS1库注册通过结构检查，改变compiler options、覆盖原root或搜索目录均拒绝。
该读出迁移没有改原证书，也没有将当前环境冒称为新fresh编译。

```bash
python3 verify_fiber.py --check-only
python3 -m unittest test_verify_fiber
```

fresh 复核使用新路径：`python3 verify_fiber.py --output /tmp/p23-full-fiber-new.json`。
科学首程序的默认输出已冻结，复跑须显式提供新路径。
typed-rational XZ 逐字节还原原 JSON；本地 gzip 不进 Git。
实际 source/epoch 身份、新通用无限 Born 与 controller advance 按各自原合同消费。

## 论文 claim 对应

| 位置 | 登记决定 |
| --- | --- |
| 物理P23 | X时点的.0003历史输入及旧gate事实保留；现行单位修复、真实接线和新源读出另带revision/source登记。 |
| 物理P24 | AB/r3的.003双实现负向事实保持；现行r6/r6.1有效DEVIATION及独立readiness回执另登记。 |
| 物理P25/P28及光学BL9–BL12后续 | 原五中心scalar slice的留出包含保留其合同；完整六训练CI→完整外覆盖/统一预言反证、十二CI→相容纤维/具体CH分歧、原始坐标→源生成内核分列新主张。 |

源生成与共同关系可直接由定理认证。原CI内符号分歧不改写P1–P22、旧slice或NIST原实验裁决。
publish由独立论文仓库维护。
