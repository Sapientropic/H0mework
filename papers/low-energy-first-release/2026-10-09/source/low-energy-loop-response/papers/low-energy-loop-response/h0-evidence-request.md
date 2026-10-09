# Case 2 新选集的 H0 证据迁入请求

本稿已纳入 Q5 与升级后的 Q6。原 Q1–Q4 的 T/S、791 原档案和旧公开身份保留。固定公开观察提交 `51867c59042460646e57d5ead4c405cbca05c240` 已核；以下需求供拥有 H0mework 写授权的材料窗口执行。本写作窗口没有改源仓、跑科研生产、编译 Lean 或公开上传。

本地成稿与原科研签收成立。新 Q6 的公开生产／消费者及实际 import／resource 验收尚待绑定，因而整套公开包仍为 **pending**。不得删除已闭合结果以保旧入口，也不得把旧 `H0mework.Papers.LowEnergyLoopResponse` 宣称为新增全选集的入口。

## 保留和直接复用的身份

- 旧 Q1–Q4：Homework T=`85cb5386ca132818f74d90470d87a252e4a27ea7`，稿1依赖 S=`30218c1aea92640eae09b1d9204a09b01a2d0e47`；H0=`ba591b43e13a59ac676919aa153569615f8d4cb2`。旧入口及 `make check-case2` 保原范围。
- 本次增量上限：Homework `71e94e8261d67cf4849a05eb14ac95aa2f7dcbb9`；各根另保下面的真实最后源 epoch 与原回执。
- Q5、K34、原五项及 K44/K45 已有同字节验收：H0 `234817b3c3f7a1023226e7a4fdb8660ddcbc9d0a` 的 `docs/first-release-map.json` 中 `phys.P27/P29/P33`。13 个直接根／必要 helper 的 source 与 target SHA、精确 URL、声明或 import 身份已在 [public-source-bindings.json](data/public-source-bindings.json) 的 `newaccepted` 完整登记。
- 原公开回执：[proof-20261007/receipt.json](https://github.com/Sapientropic/H0mework/blob/234817b3c3f7a1023226e7a4fdb8660ddcbc9d0a/evidence/first-release/acceptance/proof-20261007/receipt.json)，SHA `c0e7872ea7f795a25b784870fd43468d306465c60087dde962d3827208462ce8`。
- 后续更完整的固定验收：[proof-root-supplement-20261007/receipt.json](https://github.com/Sapientropic/H0mework/blob/51867c59042460646e57d5ead4c405cbca05c240/evidence/first-release/acceptance/proof-root-supplement-20261007/receipt.json)，SHA `fce024e638563a21fd526ae087b2eb8062c9a7cb3a824649074551c553161ec1`。13 根的对应目标字节与原234提交相同；后续回执不能拼成旧234提交的URL。

## 需要新增迁入的精确根

前缀 A 为 `Verification/physics/low-energy-phenomenology/alpha-source/`；E 为 `A/em-identification/`。下列21枚固定源在上述固定公开 export-map 中均无映射。全文 source SHA 与 import 列表也保存在 `newpending.selected_roots`；空目标和空公开回执保持 pending，不能预填成功值。

| 固定源（相对 A/E） | 源 SHA-256 | 最后源 epoch |
|---|---|---|
| `A/CanonicalPreparationSourceUnitMixedDerivative.lean` | `d139ec516e2d8062766f37f87698b668ca7136b4dc005cb2744985579804e5dc` | `3bbcbd590fbd1892661b8f5f0a09b555e7b9c7d4` |
| `A/CanonicalPreparationSourceUnitAmputatedFourPoint.lean` | `c3edfd1ae26e45893779617f569191ff3f6c8627f03ec52ec5a1ec40c86dbc3a` | `3bbcbd590fbd1892661b8f5f0a09b555e7b9c7d4` |
| `A/CanonicalPreparationSourceUnitPhysicalCurrent.lean` | `b043b9184fada775a93d3fe571b592a8ed552b65002dbcbb6ae7e9872507fef9` | `3bbcbd590fbd1892661b8f5f0a09b555e7b9c7d4` |
| `A/SourceUnitMixedDerivative.lean` | `eb53a792264da671263b83cd34263248780e127cd84623fb7ad58e336ec749d6` | `3bbcbd590fbd1892661b8f5f0a09b555e7b9c7d4` |
| `A/SourceUnitAmputatedFourPoint.lean` | `443eb386b71cdd21eb3431bc5888d89abd91f9f19c47c25a1cfe0a3d716afcf9` | `3bbcbd590fbd1892661b8f5f0a09b555e7b9c7d4` |
| `A/SourceUnitPhysicalCurrent.lean` | `d421450e1870e0853f5fcdfeb0fa681753b41a9e6fc80c8716201216dca1793e` | `3bbcbd590fbd1892661b8f5f0a09b555e7b9c7d4` |
| `A/PhysicalActualUnitFourPointReturnTypedMouths.lean` | `bafa00bf1ac3b0220100164f779376c7914b462cddd3386dc64645dee84fec23` | `3bbcbd590fbd1892661b8f5f0a09b555e7b9c7d4` |
| `A/AuditCanonicalPreparationPhysicalActualUnitFourPointReturn.lean` | `030a476a95e89c327fe7c10f678c10add5af2f99a67104ce6679a5c5bc741b81` | `3bbcbd590fbd1892661b8f5f0a09b555e7b9c7d4` |
| `E/ActualDressedNoetherHistory.lean` | `b6667516e78f8d313971d6c66c9ae15f82a0c78dcb61efb28392526de61c8185` | `f13ed87d6340e2cb041334eedfdc881dfb209abd` |
| `E/ActualDressedNoetherAction.lean` | `ceac49dbaee75179221e902f2d249029cf9aead6d439d12fa54a81d4a57363aa` | `f13ed87d6340e2cb041334eedfdc881dfb209abd` |
| `E/ActualDressedNoetherResponse.lean` | `fc8cf5a350c374bc57a965f62f6fe4bfb261def4886514ccfd790aee6065cc60` | `f13ed87d6340e2cb041334eedfdc881dfb209abd` |
| `E/ActualDressedNoetherBoundary.lean` | `3a37fd2d72377c96087e0c88bafe03353cb005c2ba6145a6f3824b31ab8e1097` | `f13ed87d6340e2cb041334eedfdc881dfb209abd` |
| `E/ActualDressedNoetherCauchy.lean` | `70f2a3abeb61aa8b135c16cf156c68b86af670baae0056eb269aacdea861d240` | `f13ed87d6340e2cb041334eedfdc881dfb209abd` |
| `E/ActualDressedNoetherAudit.lean` | `b0d3e5f75ef1c4f90b7e4e3f346ac5f9526f71762c968cb7a77d2fd55fdb81b4` | `f13ed87d6340e2cb041334eedfdc881dfb209abd` |
| `E/ActualDressedSignalOperator.lean` | `e15c768ab17636d0e2ffd8160422270563ef9137b4be217612af88f0770b9477` | `c015842c42751dc786dcce9522e67887b6b6d9e8` |
| `E/ActualDressedSignalPrice.lean` | `41e5b571be0c95a7d804eea7e01a2b4cd8b1f750e9016ecf31e1f881497774d6` | `c015842c42751dc786dcce9522e67887b6b6d9e8` |
| `E/ActualDressedSignalCausal.lean` | `d89b25b5c3a4bb67aac1aa853a9830947fe1f790323af468679521b05275a50d` | `c015842c42751dc786dcce9522e67887b6b6d9e8` |
| `E/ActualDressedSignalTensor.lean` | `b93e070bd3b1db46f1c527a5c93fb72ba42d7c7d05128d619b467441bbcf9ab1` | `c015842c42751dc786dcce9522e67887b6b6d9e8` |
| `E/ActualDressedSignalPencil.lean` | `ef41652832bb2296e0c35ba870389d6a2969d4262fcdf61d02dcb8b3970e9f73` | `c015842c42751dc786dcce9522e67887b6b6d9e8` |
| `E/ActualDressedSignalAudit.lean` | `ac78801c4cfe89b475a1bc0823e9703822f77e232b292ea2e19415a730a8d4f2` | `c015842c42751dc786dcce9522e67887b6b6d9e8` |
| `E/ActualDressedSignalPencilAudit.lean` | `c638006b330a24b1ffae6a43cd0a73980362c4c09c28ed41af2171b9993bbafd` | `c015842c42751dc786dcce9522e67887b6b6d9e8` |

K53 的三枚 `CanonicalPreparationSourceUnit*.lean` 是薄 import。实际承重证明是三枚 `SourceUnit*.lean`，不可只迁 alias。原 `source_delivery` 给实际 SOURCE FIRST 与稳定源字节的逐一同一性；不是重编或新证明。独立 normalized primal／dual 的 `sourceUnitRead` 与 K54 的 creation-minus-background observer 保各自读口，不能宣称 K54 直接调用前者。

## 选集所需的定理与接口

1. K53 保真实 mixed derivative、两有序项与直接 contact、原 amputation、独立外腿校正、同 physical clock 的五项与全289 current/co-source；所有单位与非实 z/w 条件原样保留。
2. Noether 的 `History/Action/Response/Boundary/Cauchy` 连同实际 `Audit` 保原 nonlinear preparation、真实 creation unit 减同 background、原作用的 Euler 负号、完整两时间边界 co-source、原 Green、九 null 数据及36 curvature rows。Cauchy 在本稿承担 fullfield 接口；不登记独立“完整72极”主张。
3. K54 的 `SignalOperator/Price/Causal/Tensor/Pencil` 及两个实际 Audit 保源生正 duration、两 real quadrature、全289×289矩阵、未平均窗口 `W_T(p0,lambda) K(p)−Pi_T`、同钟 `W_T=T`，并保 shifted-clock 独立反例。有限 nonlinear 窗口与线性化半轴的量词分别签收；后者使用 `Re(lambda)>sourceClockGrowth(p)` 与真实 tail price。
4. K44 的最终半轴 CLM 消费完整 real Noether 四 key Euler current。原 raw 五项必须加已付的中央 contact 增量：`D_N = D_5 + U_L(-t) R_L (J_Nprime−J_rawprime) R_R U_R(t)`。仅 `J_N(0)=J_raw(0)`，不能声称全 h 同一；四 keys `−k,k,2p+k,−(2p+k)` 以 Finsupp 合同后再读口。必要 contact producer 已在原 AE 闭包，直接复用。

## 实际闭包与资源要求

以各原独立认证所付的 SOURCE FIRST、完整 type/value/opaque/constructor/recursor 元数据为起点建立实际依赖图，逐条对固定源 SHA。当前71e文本 import 候选图的扫描不等于原已签 object 图，不能凭同名文件或最新 `.olean` 替换旧支付对象。新 `data/public-source-bindings.json::newpending.dependency_scope` 记录了候选扫描的范围及25条没有对应 tracked 源路径的 import edge；部分是已有 retained/generated source，需核原验收与生成身份，不能统称缺失数学证明。

材料窗口应实际完成：

- 导出21根和每一个实际 import；能复用既有相同 source/target 字节和验收的依赖就保其原 epoch。SOURCE alias 必须绑定其实际源体；retained/generated 源保生成器、原 source SHA、原回执 pointer 与公开派生身份。不得以当前候选图带入无关研究结果。
- 从实际被消费的 `include_str`、运行时读取与 audit observer 入口建立 resource 闭包。每个资源保 source SHA、target SHA、公开变换及读口；保持必要 clock、profile、measure、完整 mixed 与 field/null/contact数据。
- `ActualDressedNoetherBoundary` 的证明真实引用原 `CanonicalPreparationPhysicalFullSourceWindow` 私有 weighted-boundary 定理 owner。迁入时按现有 public-tooling 的 declared private-name/audit-owner 规则登记双向改写，保持值及完整闭包可还原；不能只改 import 后留下失配私有 owner。
- 给新选集建立薄论文入口与一个真实登记的 focused proof/consumer package。建议入口名 `H0mework.Papers.LowEnergyLoopResponseRRelease`；此名称是请求，不是已存在的公开绑定。保旧入口后，在新入口复用旧Q1–Q4、已有AE/AD/AC闭包，并消费新21根及实际 Audit。
- 按材料仓实际登记后的入口执行 build、完整 type/value trust 与 focused direct-consumer/关键反例验收；验收输出写新目录，保旧回执字节。不得把原289场科研程序或本轮局部检查冒称重认证。
- 从实际 export-map 验证每个 source/target SHA、重定位 import、private owner与resource的双向源身份；保存新固定提交、入口、运行命令、回执 SHA 和通过范围，之后再更新本稿 `release-selection.json` 与 `public-source-bindings.json` 的 pending 项。

## 原签收凭据与公开派生

以下四个原科研回执保原字节于源仓。原回执含私有运行路径，应按材料仓已有 publication transform 导出必要公开派生；原 source SHA、target SHA、变换和原 payload 同一性都须登记。不能直接把私人原 JSON／日志上传，也不能把公开派生冒称原件。

| 原回执（相对 A/E） | 原 SHA-256 |
|---|---|
| `A/canonical_preparation_physical_actual_unit_four_point_return_certification.json` | `6d450d8d6764c967ce03cf4fe412fff358c71d2a9aed8bc9913a17cb16902445` |
| `E/actual_dressed_noether_certification.json` | `775900422b92c0762c07ad885578c90808c5bb12f16a623145c0aa7f621d96c4` |
| `E/actual_dressed_signal_certification.json` | `5c641aae60208a4ec6322321be08b35e8eda26e683cdfd25d267f89785881b4b` |
| `E/actual_dressed_signal_pencil_certification.json` | `4af72fa9d2f28a8749eabe2f633fcf49d63dc0f41ad2a52003eaf9f21bd6e8ad` |

K53 的 `canonical_preparation_physical_actual_unit_four_point_return_source_delivery.json` 还应导出必要的公开派生，它逐一绑定三枚实际 SourceUnit 原源和 FIRST 对象；原 SHA `69ffbf5bdd8e12910b70fff87a522831526a0a5641d67c7215eaec3081919c30`。新 public JSON 可省私人运行路径，但必须保存这些源／原对象／原 FIRST receipt 哈希与稳定字节身份。

## 本稿的当前交付判定

原Q1–Q4与Q5/K44/K45公开证据可以按各自固定身份复用。21个新根及其实际源闭包/资源和选集验收尚未获得新的H0公开绑定，所以 **本地写作完成** 与 **整套公开上传就绪** 分开签收。需求关闭的唯一条件是上述真实新映射、固定提交和通过回执齐全；材料窗口完成后通知写作窗口回填实际身份。

Zenodo 本地可编辑包继续排除原 `source-evidence.tar.gz`、私人原manifest、历史日志、缓存与内部提示词。原791档案保持在本地；公开证明以已核固定仓与必要派生数据交付。
