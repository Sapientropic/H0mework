# 同源环境作用、完整计数与raw校准

固定局部环境模式与原RawKernel生成真实光学端口，制备变化和校准读出消费同一个carrier。
[当前责任](../../investigation/README.md)由名义装置active card维护。

## 源与全部n效果

[ev0001](criterion.md)以原H/V透射和合法complex ξ为primitive，
内部生成两occupied列、六端口、no-click Gram X=I−E与全部n的actual Γ。
真实偏振作用保持Pol⊗Env，不能将两个环境分量直接替换为旧occupied Γ(R)。
ξ=1直接退回原所有n的Γ；[独立证书](certification.json)支付实际端口、上下界和该极限。

[sp0001](sector-criterion.md)从同一个occupation对称像生成symmetric-power乘法、transpose及adjoint自然性。
原paired amplitudes内部拆出sourceRoot与D，因此实际sector Born为
`Re[Z trace SP_n(D† XA D XBᵀ)]`，保留任意n、complex source phase和原sectorMass预算。
Bob用普通transpose。[独立证书](sector-certification.json)覆盖该实际身份及h0/h1，
通用递推和无限determinant和按各自证明范围消费。

## 完整数值读出

[evg0001](numeric-criterion.md)的主路径从实际六rows生成三项Gaussian no-click；
独立路径从Pol⊗Env投影、normalized occupation和paired amplitudes直接求相干Born。
total-pair≤6的前缀保持原归一，遗漏由原numberMass tail外包，随后运输至N1/N5本地OR。
新环境作用改变local bucket的二阶项，single-pair coherence的相同product不能代替完整效果。

两个[冻结首回执](verification.json)形成后才交叉；全部八source的原生效果、
local/joint no-click、16个完整窗口及40个fringe探针都有共同数学包络。
通用QA/QAB≤4、joint≤8及导数≤14由完整系数生成，q∞保留。
这个系数口没有宣称已经枚举所有fringe极值。

复现使用新输出路径：

```bash
python3 test_counts_primary.py
python3 test_count_consumer.py
python3 verify_counts.py --output /tmp/p23-environment-count-cross-new.json
```

JSON-only override只更换首回执目录，所有科学程序固定来自仓库。
显式disable和形似错误版本均被拒绝；原最优门禁由[名义重放入口](../../README.md)维护。

## 名义校准生成器

[mc0001](matched-criterion.md)从实际全部n端口和同一paired振幅证明matched V/V无限Born：
`Q_AB = 1 / (1 + n_V (T_A + T_B − T_A T_B))`。
局部silent端口产生singles，独立OR背景生成raw `K_A=J/S_B`、`K_B=J/S_A`及正herald分支。
[独立证书](matched-certification.json)同时支付已知源损耗逆读和forward必满足的rawK三次式；
未知源的全部根搜索由下述数值producer承担。

[nec0001](calibration-criterion.md)固定公开的reference drive、总pair量、
matched Klyshko与两个不同basis的raw可见度角色，先冻结后生成source。
公开总pair量首先确定reference16°的同一个G，随后运输至balanced45°；
heralding效率先作为raw读出，不直接冒充裸透射。
K的全部实根及环境c的完整合法域都保留。
全HV/DA极值必须由完整条纹证书产生，不能用局部端点代替。
对称环境分解与两个单侧override各自验收，不并成一个最优带。
该名义物理规格有明确模型身份，实际逐run资格由独立记录承担。

[校准交叉验收](calibration-verification.json)重生两条路径的完整首回执、全部实根和合法分支，
再从公开输入独立生成共同源，核对152项coherent Fock探针。
主路径的unrounded G区间与独立路径的15位有理grid保持各自身份；
共享源核对不能以近似相等替代exact source identity。
公布最优r/角、旧ef/pd参数及Table S-II不进入这个校准逆读。

## 五控制重放与门禁

[r0006](../../criterion-r0006.md)在每个合法校准源上固定G、裸透射、环境作用与source phase，
优化泵方向和四个接收角，目标为N1 raw CH；N5保持诊断角色。
两套确定性搜索分别生成全部候选，公开五值在搜索完成后才进入比较。
[r0006.1](../../criterion-r0006.1.md)从独立程序自己的未收敛候选续算，收紧线搜索包夹，
原模型、19点、whole-cycle停止阈值、五分量容差和舍入带保持。

[重放交叉消费者](verify_environment_replay.py)从冻结公开输入重新生成全部源、合法根、
原生与独立Born读出及每个具名模型的带。默认17点与两个环境override分别裁决。
新门禁由`nist-real/nominal_environment_optimum.py`直接接入`checks.control_loop`和
`readiness.components.nominal_apparatus_optimum`；有效负向回执也有`evidence_valid=True`。
显式R3 selector保留历史消费，R6证据失效时关闭门禁。名义合同不新增实测、绝对mW或actual epoch前提。
