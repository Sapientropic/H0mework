# 公开联合约束的非空正CH源域

完整公开setting曝光、四outcome与两侧single已经压缩原共同源域。
在[sc0001合同](criterion.md)的共同conditional source law下，新联合95%置信源域非空，
整个接受域统一满足 **CH_N5 > 1.37901805×10⁻⁶**，精确有理下界由证书保存。
八个原Γ/Fock物理成员同时满足旧72CI、新96项conditional约束和四项联合source cut。

## 同一个源如何消费更多公开信息

原四模EF source、共同Jones frame、scalar loss、每pulse相位mixture及fresh-pulse OR保持。
各setting的曝光直接来自同一完整十六计数；设置可依赖past，conditional outcome law
使用同一个Snapshot。新增six-feature采样界从源生成，随后反演每setting的概率域。

原20bet的全trial归一化支持函数为

```text
h = l·CH−ε(1−ε)·min(onlyA01,onlyB10,j11)
d_k = 1+2^-k h
log E_k = Wobs log(a_k)+Lobs log(b_k)−T log(d_k)
```

它保持未知setting分布的归一化、原ε=.003、neutral及全部曝光T。
[源内核](NormalizedSourceBet.lean)自产精确支持顶点、d_k正性和一步期望界；
[独立内核认证](kernel-certification-first.json)核71项声明及13790项传递依赖，
fresh trust0/werror和标准三公理通过。

## 联合95%预算与连续覆盖

旧72CI和全部旧输出保持原字节。安全旧失败界为3/(80×32767)；
总预算1/20扣除该失败界，余量等分给24项完整曝光contrast族和24×4×6×40 conditional方向bet。
[统计交叉证书](statistics-cross-verification.json)逐项核576个新区间、23040方向bet、
480个原fixed-bet基础值及24个有理反演括号。
两个统计首分别冻结于5a35416ec6与85d5b45efa，原预算和CI没有重新拟合。

四个每pulse接收均值域的宽度变化为：

| 共同均值 | 新宽度／旧宽度 | 收窄约 |
|---|---:|---:|
| A0 | .83284930 | 17% |
| B0 | .77364993 | 23% |
| A1 | .67212320 | 33% |
| B1 | .79644198 | 20% |

从原已认证的11个完整外包盒继续收紧，共1035节点、512次分割、209排除叶和314保留叶。
[域首回执](domain-first.json.xz)e25c01bafd保存线性contractor、同k多项式、八段相位分区和排除依据。
[独立域证书](domain-verification.json)942aaa8c90支付全部节点、6720相位witness、
32旧源的2304项旧CI、3072项新conditional和128项source cut检查。
八个合格成员沿原recipe/source/native窗口保身份；没有新Fock、grid或求解器执行。
保留叶保有边界及cap的outer责任，实际成员单独认证。

N5的严格正下界从h cut、源内核与三项loss的共同CI下界生成；
验收没有后置CH>0筛选，也没有把外包盒的CH hull当作全域结论。
旧72CI中的负CH成员和旧mixed判决保留其原合同；新交集的统计裁决另按联合错误率消费。

## 消费入口与声明范围

[最终证书](source-compression-verification.json)c0ae9f2bd7签收联合95%、非空、连续外覆盖及N5统一正CH。
`verify.consume(certificate_path=None, disabled=False)`核原字节与绑定；
默认和同字节副本override消费成功，disable不读证据，形似或scope升格拒绝。
快速消费不重跑统计、树、Fock或Lean。
[readiness](../../../readiness.py)的`public_source_compression`直接消费这些字段。
[实际门禁回执](../../../evidence/readiness-source-compression-sc0001.1.json)签收
public_review_completed、public_source_domain_compressed、joint_95_source_domain_nonempty、
joint_95_source_domain_CH_N5_positive均为true；原名义最优性仍是有效DEVIATION。
不变的名义科学义务沿[原实际CLI回执](../../../evidence/readiness-source-compression-sc0001.json)保身份，
[完成器](complete_readiness.py)核固定来源后重消受影响入口，没有重复名义grid/Fock。

源平稳及past-conditional law按共同EF模型合同承担；统计接受域不识别唯一实际硬件源。
σ、近似pair、跨epoch器件及未知mask历史搜索没有取得新的95%资格。
原r6名义最优性拒绝、root/current/whole-ledger与tick16→17保持。
论文登记见[声明映射](../paper-claim-map.md)，当前路线只由[NIST active card](../../investigation/README.md)维护。

```bash
python3 verify.py --check-only
python3 -m unittest test_statistics_verify test_domain_verify
```
