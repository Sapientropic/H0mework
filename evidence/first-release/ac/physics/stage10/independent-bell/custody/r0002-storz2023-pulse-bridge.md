# ETH 2023 名义脉冲桥：metadata-only 独立核对

**计算通过。** 只消费 [custodian 控制 packet](r0002-storz2023-metadata.json)；未打开
`independent-bell/cache`、sequestered、论文结果或实验数据。未修改源、统计或解析规则。
本报告签收登记的 Methods 理想条件模型，不充当完整 apparatus calibration。

## 从脉冲到概率

以 `|g⟩=(1,0)`、`|e⟩=(0,1)`，原始读出 `g→+1, e→−1`，初态为实
`Ψ+=(|ge⟩+|eg⟩)/√2`。固定标准主动旋转：

```text
R_φ(t) = exp[-it(cos φ X + sin φ Y)/2]
U_A(a) = R_(π/2)(aπ/2) R_0(π/2)
U_B(b) = R_(θ_geo+π/2)(bπ/2) R_θ_geo(π/2)
```

乘积右端先作用。直接计算 `U† Z U` 得到物理初态上的测量算子：

```text
A0 = Y                         A1 = −X
B0 = −sin θ_geo X + cos θ_geo Y
B1 = −cos θ_geo X − sin θ_geo Y
```

实 `Ψ+` 的 `XX=YY=1`，局部均值为零。因此直接 Born 展开为
`P(x,y|a,b)=[1+xy cos(θ_geo+(b−a)π/2)]/4`，无结局重标或目标 correlator 输入。
名义 `θ_geo=−π/4` 时，按 `(a,b)=00,01,10,11` 的相关系数是
`(1,1,−1,1)/√2`；四结局顺序始终为 `(++,+−,−+,−−)`。

共同参考变换 `W=R_x(π/2)⊗R_x(π/2)` 把初态变为 `−iΦ+`，共同相位不影响概率。
在此 frame，Alice 轴为 `Z,−X`；Bob 为 `(X+Z)/√2,(−X+Z)/√2`。
用固定 Bob 共轭 `B→XBX` 回到既有 `herald=+1` 的 `Ψ+` 家族，故交给
[predict.py](../predict.py) 的 **XZ 字典**为：

```text
alice_axes_xz = [(0,1), (-1,0)]
bob_axes_xz   = [(1/√2,-1/√2), (-1/√2,-1/√2)]
herald = +1;  原 x/y 不翻转; independent_calibration 不提供
```

## 已登记的物理条件

此点零假设采用实 `Ψ+` 制备、理想旋转与读出，以及两站相位对齐后上述名义几何角。
Eq.16 的复合有效相位、`theta_control` 与拟合 offset **没有**被设成 `θ_geo`；packet
未给它们逐 setting 的完整转换或 disjoint 原始相位校准。本计算不补造该等式。
独立 phase/readout/visibility 的数据与传播证据缺失，按协议省略 calibrated model，
保留 ideal 模型原 α=.025，未用预算不重分配；六半径仍是既有条件敏感性。
若该条件模型被拒，拒绝的是含理想制备／相位／读出合同的联合命题；未经校准分离，
不能把仪器失配唯一归因于原 source。这里不读取结果，也不调整模型。

## 合成验收

[test_pulse_bridge.py](../tests/test_pulse_bridge.py) 独立构造 2×2 旋转及 4×4 张量 Born 计算：
核对全部 4 settings × 4 outcomes、一般名义角、归一化／边缘、共同 frame、Bob 共轭和固定字典。
反例覆盖颠倒脉冲顺序、只给 Bob 固定脉冲加相位；二者改变联合表，不能替代登记序列。
既有 parser 合成测试确认三行 header、CRLF/空格/无末尾换行、列顺序、全部结局保留、
物理行号、非法行中止、已解包输入不再次按 FPGA code 解码；cap 测试不读取界外下一事件。

运行 `PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s Verification/physics/stage10/independent-bell/tests -p 'test_*.py' -v`：
**15 项全部通过**。所有输入均为 synthetic 或已披露控制元数据。
