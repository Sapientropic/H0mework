# 原源低能唯象：精确从属读出

2026-09-19。基线 e60a86058abcb74b7f2225f2383c182be8343785；施工前 HEAD 557a190ecbd60b99ede762694d3e78472f3dc676。没有修改原源、作用、真空、Stage10 或 controller 权威。

## 已实际执行的验收

五个正式 LowEnergy 模块及其直接消费者以 Lean 4.33.0、`--trust=0 -DwarningAsError=true` 编译通过。`results/lean-audit.log` 保存 14 个承重声明的公理输出，全部仅依赖 propext、Classical.choice、Quot.sound；不声称零公理或全库重建。

`results/exact-run.log` 保存精确生产计算，`results/independent-check.log` 保存另一个实现的复核。检查器不导入生产脚本，以补集外积、Cartan 权重、精确投影逆恒等式、谱因式分解、根隔离与双素数行列式交叉核对；均已通过。不冒充独立研究者审稿或 Python 的形式化验证。

## 直接复核命令

从 Homework 根目录运行 `python3 Verification/physics/low-energy-phenomenology/exact_readout.py --root . --out Verification/physics/low-energy-phenomenology/results`，再运行 `python3 Verification/physics/low-energy-phenomenology/check_readout.py --root . --receipt Verification/physics/low-energy-phenomenology/results/exact-readout.json`。

Lean 从 Lean 目录逐一运行 `lake env lean --trust=0 -DwarningAsError=true SaturationMonoid/PhysicsCore/LowEnergy/NAME.lean`，NAME 依序为 ScalarInventory、Normalization、Running、JointMassCoordinates、Consumer。更新被导入模块后须同时刷新相应 `.lake/build/lib/lean/.../NAME.olean`；本轮已实际完成。随后运行 `lake env lean --trust=0 -DwarningAsError=true ../Verification/physics/low-energy-phenomenology/Audit.lean`。

自动化 shell 封装的远程写入被工具安全检查阻止，因此没有安装 verify.sh；上述独立命令与成功日志保留。

## 精确适用范围

单份左 Weyl Λ⁶⊕Λ²⊕Λ⁴ 加一份复 Λ⁴，得到标量迹 (5,5,5,20) 与 b₀ (56/3,4,1/3,−28)。这是实际库存代入已有一圈公式的 Lean 定理；微扰物理手征计数与圈积分身份不由该算术定理代填。

原源质量映射的整数坐标与 Gram 公式已 Lean 证明。完整 7×21 矩阵的秩 5、输入核 16、平方奇异谱 0[2],2[4],4[1] 属于精确程序回执。旧单通道 rank=3 定理保持原身份。

母 48 维轨道秩 34，不是 48 个已安装传播场；原生 12 维 P286 标量—规范块秩 9，谱 0[3],1[6] 与 6x³−26x²+27x−8 的三根，不代填完整耦合背景上的粒子极点。

交换只在重方向上求逆，保留 B-正交零模投影。回执含完整矩阵、特征多项式、有理根区间、投影逆、12 枚 63 维稀疏表示电流及十份原源码 SHA-256。`proton_lifetime=null`，没有填入外态、强子矩阵元或 GeV 能标。

Running 只证明明定的三条仿射函数与正性区间，不作全理论不可统一裁决。完整 BF 到散射耦合、微扰库存、耦合波动、阈值、B/L 和单位仍为同源识别责任。

出版侧图像用 Python 标准库生成可编辑 SVG，无包安装：`python3 papers/low-energy-phenomenology/figures/src/draw_figures.py --receipt papers/low-energy-phenomenology/figures/data/exact-readout.json --output papers/low-energy-phenomenology/figures`。出版 JSON 是本目录回执的哈希一致副本，不是第二个证据权威。

## 全局稳定子解析补充

[解析证明](stabilizer-derivation.md) 从 W_v†W_v 的三个不同本征空间得到完整块分解，进而证明裸标量的母紧稳定子为 (SU(2)×USp(4)×U(1))/Z₂，P286 内恰为嵌入 SU(2)。这是真正给出满射与核的解析推导，不是由维数猜群，也尚未标为 Lean 群稳定子定理。

运行 `python3 Verification/physics/low-energy-phenomenology/stabilizer_check.py --receipt Verification/physics/low-energy-phenomenology/results/exact-readout.json --out Verification/physics/low-energy-phenomenology/results/stabilizer-check.json` 复核所用整数 Gram、辛二形式分解和相位方程。此补充不修改任何原作用或物理识别。

本轮继续构造见[原作用耦合响应](coupled-response/README.md)：新增真实交叉项、辅助场消元、原标量时间号数和线性化增长方向。旧裸谱不再被预解释为完整稳定粒子谱，各项数学证据保持原身份。
