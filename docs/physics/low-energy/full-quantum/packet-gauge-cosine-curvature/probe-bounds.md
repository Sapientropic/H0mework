# 原source Hessian在整个轻探针球上的运输

本文件与 `probe_bounds.py` 由root构造，消费已签 `CosineMomentum` 的同一ψ、P、H、K、V
及原位置矩。它为本目录零current探针的实际积分张量提供直接的全轻球消费者。

对任意单位外动量方向n、探针方向v，置 `X=n·y`、`Y=v·y`、`W_m=X^mV`。
原单位方向矩 M_j、T_j 同时控制混合位置矩：Hölder给
`||Y X^j f||≤M_(j+1)(f)`。原流的有序Duhamel微分因此同样给全部混合方向的

\[
 P_m(t;f)=\sum_{j=0}^m\binom mj(Nt)^{m-j}M_j(f).
\]

令 `C_m,k=C[W_m]_k ψ`。零探针的真实current变化是
`C_m,0=2K W_m ψ/N²`，因为两传播腿严格相消；其本身保持全时间常量。
对于任意物理k，以 `|exp(i k·y)−1|≤|k||Y|` 作用同一原向量，可逐项估计
`C_m,k−C_m,0`。

原直接current项给

\[
 2N|k|\bigl(M_{m+1}+Nt M_m\bigr).
\]

Hψ的两条传播腿分别给下列不同的时间矩，保留原次序：

\[
 L_m(t)=\int_0^t\sum_{j=0}^m\binom mj
   [N(t-s)]^{m-j}P_{j+1}(t;H\psi)\,ds,
\]
\[
 R_m(t)=\int_0^t\left[P_{m+1}(s;H\psi)
             +N(t-s)P_m(s;H\psi)\right]ds.
\]

左式先把 `X^m` 通过 `U(s-t)`，再用phase差的一次Y矩；右式先把Y通过
`U(t-s)`，再作用于 `X^m V U(s)Hψ`。二者均来自原加权域，不是整体算子范数的
小动量假设。原 `H_k` 项已含一次 `|k|`，另给
`N²|k|∫₀^(2t)P_m(s;ψ)ds`。

令 `alpha=√2/N²`，合成得真正源向量界

\[
 \|C_{m,k}(t)-C_{m,0}(t)\|
 \le |k|\,D_m(t),
\]
\[
 D_m=\alpha\left[
 2N(M_{m+1}+NtM_m)+2N(L_m+R_m)
 +N^2\int_0^{2t}P_m(s;\psi)ds\right].
\]

程序对m=0、2生成全部非负有理系数。m=0恰恢复已经签收的恒定外场probe界
`alpha[2NM1+4N(T1+N)t+4N²T0 t²]`，独立检查两腿计数。
m=2直接控制实际外q Hessian；负号不改变范数。

原未变化current另有

\[
 \|(B_k(t)-B_0)\psi\|
 \le\alpha|k|(2T_1+N+2NtT_0).
\]

完整半轴阶乘moments给η≥5上的三个同源常数：Jlip控制未变化current的probe差，
Clip控制q Hessian的probe差，Z2zero控制零probe的q Hessian本身。
P固定且为收缩，因此raw与connected各保持这些界；均值没有被置零。

在实际 `z=w=6c(1−i)` 上，原零probe的raw和connected Laplace向量范数都小于1。
由两条实际Gram腿的完整展开，对所有单位外方向n，

\[
 |D_q^2\mathcal N^{[1]}(0;k,l)[n,n]
     -D_q^2\mathcal N^{[1]}(0;0,0)[n,n]|
 \le (|k|+|l|)(C_{lip}+J_{lip}Z_{2,0})
       +2|k||l|J_{lip}C_{lip}.
\]

这是完整复数误差；两probe可独立变化，不能删去最后两项交叉。
同一式分别适用于raw和connected。单位向量极化也直接控制六个混合坐标分量。

`probe-bounds.json` 从原正式轻半径的已签源读回，给整个原轻球的误差小于
`0.001106`，整个 `sqrt2/32768` 传播球的误差小于 `0.002204`。
这些是实际tensor积分的运输半径，不是其未知中心值。中心值由本目录原完整半轴积分
生成后再消费；没有新增采样、截断或归一化。
