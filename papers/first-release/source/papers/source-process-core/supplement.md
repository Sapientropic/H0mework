# 补充材料：完整证明

**《状态不是历史，源才是：过程同一性、责任承接与最小修订》**

**作者：高健（Jian Gao）**

本补充给出正文 §6.5、§7.3 末、§8.5 与 §9 各结果的完整书面证明。正文已陈述结果并给出证明思路；这里逐条交代对象与定义域、实际输入与量词、关键引理、决定性推导，以及同一对象在后续结果中的直接使用，最后对应到形式证明。记号与正文相同，定义、定理与公式编号均指正文。正文 §2–§5、§6.1–§6.4、§7.1–§7.3 与 §8.1–§8.4 的证明已在正文与附录 A–C 中完整给出，不再重复。

每节末的“形式对应”列出承载该结果的 Lean 声明；所在源提交与完整路径见正文附录 D.2，公开复现入口见正文“代码与数据可得性”。

---

## S0 共同工具

**S0.1 剩余计数与执行。**命题 3.7 给出：每个执行步恰使剩余计数减 $1$；常量没有执行步；从左到右的执行 $\mathrm{exec}_\rho(e):e\to\mathrm{const}(\mathrm{ev}_\rho e)$ 的长度为 $r(e)$；每条执行迹都是推导，故端点求值相等（命题 3.6(1)，下称**可靠性**）。

**S0.2 配对语言保持剩余计数。**附录 A.2 的配对化 $e\mapsto\widetilde e$ 把变量、常量、加法、线性与双线性节点逐一换成配对值上的同类节点，因此 $r(\widetilde e)=r(e)$（对 $e$ 的结构归纳，每个节点贡献的计数不变），且
$$\mathrm{ev}_{(\rho,\varepsilon)}(\widetilde e)=\bigl(\mathrm{ev}_\rho(e),\ \mathrm{eff}_{\rho,\varepsilon}(e)\bigr).\tag{S0.1}$$

**S0.3 迹的关系像与更新读法。**设 $t:e\to e'$ 是环境 $\rho$ 下的执行迹。每个执行步是一枚推导证据，其关系像是两端点之差；整条迹的关系像伸缩为 $e-e'$。由可靠性，$e-e'\in\ker(\mathrm{ev}_\rho)$。给定增量 $\varepsilon$，命题 3.3 的更新等式给出
$$\mathrm{ev}_{\rho+\varepsilon}(e-e')=\mathrm{ev}_\rho(e-e')+\mathrm{eff}_{\rho,\varepsilon}(e-e')=\mathrm{eff}_{\rho,\varepsilon}(e)-\mathrm{eff}_{\rho,\varepsilon}(e').\tag{S0.2}$$
特别地，$e'=\mathrm{const}(c)$ 时 $\mathrm{eff}(e')=0$，更新后的值就是 $\mathrm{eff}_{\rho,\varepsilon}(e)$。

**S0.4 余像与诱导映射。**对 $\mathbb Z$-线性映射 $f:X\to Y$，记 $\mathrm{Res}(f):=X/\ker f$ 为其余像，$\mathrm{can}_f:X\to\mathrm{Res}(f)$ 为商映射；$\mathrm{Res}(f)\cong\mathrm{range}(f)$。若 $f'\circ s=t\circ f$（称 $(s,t)$ 为从 $f$ 到 $f'$ 的态射），则 $s(\ker f)\subseteq\ker f'$，故 $s$ 诱导 $\overline s:\mathrm{Res}(f)\to\mathrm{Res}(f')$，满足 $\overline s\circ\mathrm{can}_f=\mathrm{can}_{f'}\circ s$。$\mathrm{can}_f(x)=0$ 当且仅当 $f(x)=0$。

**S0.5 提升残差。**设 $(s,t)$ 是从 $f:C\to D$ 到 $f':C'\to D'$ 的态射。对 $c\in C$，其**纤维** $\mathrm{Fib}_f(c):=\{x:f(x)=f(c)\}$。$s$ 把 $\mathrm{Fib}_f(c)$ 送入 $\mathrm{Fib}_{f'}(s c)$，并把 $\ker f$ 送入 $\ker f'$。对 $y\in\mathrm{Fib}_{f'}(sc)$，令
$$\mathrm{lift}(c,y):=[\,y-s(c)\,]\in\ker f'\big/s(\ker f).$$

> **引理 S0.5.** $\mathrm{lift}(c,y)=0$ 当且仅当存在 $x\in\mathrm{Fib}_f(c)$ 使 $s(x)=y$。
>
> *证明。*若 $y-s(c)=s(k)$，$k\in\ker f$，取 $x=c+k$，则 $f(x)=f(c)$ 且 $s(x)=y$。反之若 $x\in\mathrm{Fib}_f(c)$ 且 $s(x)=y$，则 $k=x-c\in\ker f$，$y-s(c)=s(k)$。∎

**S0.6 作用词模型。**设 $X$ 为加法群，$(A_\ell)_{\ell\in L}$ 为其上一族加性作用，$\mathrm{rd}:X\to Y$ 为加性读出。对词 $w=\ell_1\cdots\ell_n$（先作用 $\ell_1$）记 $A_w:=A_{\ell_n}\cdots A_{\ell_1}$。令 $K:=\{x:\forall w,\ \mathrm{rd}(A_wx)=0\}$。

> **引理 S0.6.** (i) $K$ 对每个 $A_\ell$ 封闭，因而每个 $A_\ell$ 诱导到 $\mathrm{Mod}:=X/K$；(ii) $[x]=[y]$ 当且仅当 $\forall w,\ \mathrm{rd}(A_wx)=\mathrm{rd}(A_wy)$；(iii) 把 $[x]$ 送到读出族 $(w\mapsto\mathrm{rd}(A_wx))$ 的映射单射，因而 $\mathrm{Mod}$ 与这一族的像（即全部词读出的完成载体）线性同构，同构与各作用交换。
>
> *证明。*(i) 若 $x\in K$，则对任意 $w$，$\mathrm{rd}(A_wA_\ell x)=\mathrm{rd}(A_{\ell w}x)=0$。(ii) 由 $K$ 的定义与线性。(iii) 由 (ii)，交换性在代表元上逐词验证。∎

**S0.7 效应历史方程。**设另有 $W$ 上的加性作用 $(U_\ell)$ 与加性观察 $M:X\to W$。对点 $x$ 与词 $w$，令总残差 $R(w,x):=U_wM(x)-M(A_wx)$；单字母残差 $r(\ell,x):=U_\ell M(x)-M(A_\ell x)$；递归定义
$$\mathrm{Acc}([\,],x)=0,\qquad \mathrm{Acc}(\ell w,x)=U_w\,r(\ell,x)+\mathrm{Acc}(w,A_\ell x).$$

> **引理 S0.7.** $\mathrm{Acc}(w,x)=R(w,x)$；记录 $(\ell_k,x_{k-1},r(\ell_k,x_{k-1}))$ 的历史长度为 $|w|$。
>
> *证明。*对 $w$ 的长度归纳：
> $$\begin{aligned}R(\ell w,x)&=U_wU_\ell M(x)-M(A_wA_\ell x)\\&=U_w\bigl(U_\ell M(x)-M(A_\ell x)\bigr)+\bigl(U_wM(A_\ell x)-M(A_wA_\ell x)\bigr),\end{aligned}$$
> 第一项是 $U_w\,r(\ell,x)$，第二项是 $R(w,A_\ell x)$。∎

**S0.8 联合作用词载体。**设 $I,H,Q$ 为加法群，带三族作用 $(\alpha_\ell),(\eta_\ell),(\mu_\ell)$ 与两个加性读出 $c:I\to H$、$m:I\to Q$。在 $I\times H\times Q$ 上令 $\theta_\ell:=\alpha_\ell\times\eta_\ell\times\mu_\ell$，种子 $\mathrm{seed}(i):=(i,c(i),m(i))$。**完整轨道载体** $\mathcal C$ 是全部 $\theta_w(\mathrm{seed}\,i)$ 张成的子模。

> **引理 S0.8.** (i) $\mathcal C$ 是包含全部种子且对每个 $\theta_\ell$ 封闭的最小子模；(ii) 三个分量投影 $\pi_I,\pi_H,\pi_Q$ 与词作用交换；(iii) 关联元 $\mathrm{inc}(w,i):=\theta_w(\mathrm{seed}\,i)-\mathrm{seed}(\alpha_wi)$ 的 $I$ 分量为零，$H$、$Q$ 分量分别是 $\eta_wc(i)-c(\alpha_wi)$ 与 $\mu_wm(i)-m(\alpha_wi)$。
>
> *证明。*(i) 生成子模由定义包含种子；任一包含种子且封闭的子模包含全部 $\theta_w(\mathrm{seed}\,i)$，故包含其张成。$\mathcal C$ 自身对 $\theta_\ell$ 封闭，因为生成元的像仍是生成元。(ii) $\theta_\ell$ 是分量积。(iii) 由 (ii) 逐分量计算。∎

---

## S1 定理 6.10：无旧承担者的责任出生与付款

**对象与定义域。**固定世界网络 $N$、其上一个带完整整账根登记的权威根、原点当前 $c$，以及读取器：它对根在 $c$ 处的每个发生给出完整的环境—表达式对。记 $o$ 为 $c$ 处的规范发生，$(\rho,e)$ 为读取器在 $o$ 的输出，$B=r(e)$，$\Lambda=\Lambda_{\rho,e}$ 为定义 6.9 的执行债律。

**输入与量词。**定理对上述任意数据成立。不输入旧责任行、已登记的询问、程序表、未来请求表或空覆盖证书；原点支撑在整个计算中固定。

**构造。**

1. *扩世界与词汇。*扩世界 $N[\Lambda]$ 由定义 6.3 给出：支撑为 $\mathrm{Sup}\times\mathrm{Option}(\text{债状态})$。词汇的当前取 $\Lambda$ 的债状态，即对 $(e',t)$，$t:e\to e'$ 为已付执行迹；初始当前为 $(e,\mathrm{id})$。当前 $x$ 的支撑是 $(\mathrm{supp}(o),\mathrm{some}\ x)$。
2. *事件代数。*在当前 $x=(e',t)$ 上，**源选动作**是执行器的输出：若 $e'$ 为常量，取结算；否则取命题 3.7 执行的第一步 $s:e'\to e''$。后继当前 $x^+$ 在结算处为 $x$，在执行步处为 $(e'',t\cdot s)$。编译把结算送到 $\Lambda$ 的恒同输运（定义 6.9 第四项），把执行步送到原生写入。
3. *整账演化。*$\mathrm{whole}(x)$ 把支撑 $(\mathrm{supp}(o),x)$ 上的每一行送到 $(\mathrm{supp}(o),x^+)$ 上：数学行 $\mathrm{row}(x)$（$\Lambda$ 在状态 $x$ 的债行）送到 $\mathrm{row}(x^+)$；每条旧行原样输运。去向与起源互逆。
4. *补丁、余项与证书。*有限补丁只含一条生成行，即数学行；其余全部行由同源输运余项覆盖——余项的发生是“该行属于旧账”的证据，无需旧账有限。补丁折叠回整账演化：$\mathrm{fold}(\mathrm{patch}(x))=\mathrm{whole}(x)$。重构证书由整账演化去向的单射性生成。
5. *编译器、根与过程。*编译器在每个当前发射补丁与整账；整账根由源与编译器组成；权威根与活过程按根登记的标准构造得到。过程在计数 $k$ 的状态记为 $x_k$，满足 $x_0=(e,\mathrm{id})$ 与 $x_{k+1}=x_k^+$。

**关键引理。**

> **引理 S1.1（一步预算）.** $r(x^+)=r(x)-1$（自然数减法）；若 $r(x)=0$，则 $x^+=x$。
>
> *证明。*$r(x)>0$ 时 $e'$ 非常量，源选动作是执行步，由 S0.1 剩余计数减一；$r(x)=0$ 时 $e'$ 为常量，动作是结算，后继不变。∎

> **引理 S1.2（预算与历史）.** 对每个 $k$：$r(x_k)=B-k$，且 $|t_k|+r(x_k)=B$，其中 $t_k$ 为 $x_k$ 的已付迹。
>
> *证明。*对 $k$ 归纳。$k=0$ 时 $t_0$ 为空、$r(x_0)=B$。归纳步：若 $r(x_k)>0$，执行步使迹长加一、计数减一；若 $r(x_k)=0$，状态不变，且 $B-(k+1)=0$。∎

**决定性推导。**

1. *出生。*由构造 2–4，每个当前恰发射一个事件；编译在结算处为恒同输运，在执行步处为原生写入。补丁恰含一条生成行；全部旧行作为余项保留，起源—去向互逆给出重构证书。原支撑不变（支撑第一分量恒为 $\mathrm{supp}(o)$），法则面、旧投影与原点处的类型与值观察作为根读出保留。
2. *付款。*第 $k$ 访问的同债当前是 $\mathrm{row}(x_k)$；去向等式 $\mathrm{whole}(x_k)(\mathrm{row}(x_k))=\mathrm{row}(x_{k+1})$ 沿 $k$ 归纳给出它到 $\mathrm{row}(x_0)$ 的谱系。其预算为 $r(x_k)=B-k$（引理 S1.2）。$k<B$ 时 $r(x_k)>0$，源选动作是执行步 $s$，同债目标是 $\mathrm{row}(x_{k+1})$，预算严格下降（引理 S1.1）；以两侧空历史合成为定义 6.6 的付款宏。目标预算 $\le$ 当前预算，故不回充；续行关系沿预算严格下降，良基。
3. *结算。*$k=B$ 时 $r(x_B)=0$，故 $x_B$ 的表达式为常量 $\mathrm{const}(v)$，局部结算存在；预算为零的当前没有付款宏。已付迹 $t_B:e\to\mathrm{const}(v)$ 的长度为 $B$（引理 S1.2），由可靠性 $v=\mathrm{ev}_\rho(e)$。由引理 S1.1，$x_{B+1}=x_B$；访问计数继续推进，因果深度不同的访问在有限历史中仍被区分。
4. *收据。*由 S0.3，$t_B$ 的关系像是 $e-\mathrm{const}(\mathrm{ev}_\rho e)\in\ker(\mathrm{ev}_\rho)$；对任意增量 $\varepsilon$，它在 $\rho+\varepsilon$ 下的值是 $\mathrm{eff}_{\rho,\varepsilon}(e)$。∎

**直接使用。**命题 6.11 以整树程序为读取器调用本定理；定理 7.7 与 §9 的各个运行都以同一所有者无关安装为数学行，读取其值、计费历史、原材料与关系边界。

**形式对应。**`JS/OwnerFree/Source.lean`（`vocabulary`、`eventAlgebra`、`whole`、`mathEntry`、`destination_math`）；`OwnerFree/Compiler.lean`（`remainder`、`patch`、`patch_fold`、`compiler`、`ledgerRoot`）；`OwnerFree/Completion.lean`（`next_budget`、`budget`、`history_accounting`、`completed_value`、`completed_history_length`、`completed_next_state`）；`OwnerFree/Payment.lean`（`lineage`、`debtCurrent`、`activePayment`、`wellFounded`、`no_refill`、`endpoint_no_paid`）；`OwnerFree/Consumer.lean`（`value_source`、`paid_history`、`relation_boundary`、`updated_inverse_fibre`）。提交 AB。

---

## S2 定理 8.12 与定理 7.7

### S2.1 定理 8.12：实际动作生成下一问

**对象。**询问帧 $\Phi$：询问状态、读取根编译器的完整原生程序、当前访问登记的原始输入 $(\rho,e)$、为每个原发生给出实际环境的读取器 $E$、因果深度 $k$。帧的数学状态是 $\Lambda_{\rho,e}$ 的已付状态 $(e',t)$；$\rho'$ 为 $E$ 在帧所在发生处的读数，$\varepsilon=\rho'-\rho$。

**(1) 请求的值。**残差请求 $e\ominus e'=e+\mathrm{linear}_{-\mathrm{id}}(e')$ 登记在 $\rho+\varepsilon=\rho'$ 上。按求值定义 $\mathrm{ev}_{\rho'}(e\ominus e')=\mathrm{ev}_{\rho'}(e)-\mathrm{ev}_{\rho'}(e')$。由可靠性 $\mathrm{ev}_\rho(e)=\mathrm{ev}_\rho(e')$，旧值为零。已付迹的关系像为 $e-e'$（S0.3），其在 $\rho'$ 下的值由 (S0.2) 等于 $\mathrm{eff}_{\rho,\varepsilon}(e)-\mathrm{eff}_{\rho,\varepsilon}(e')$，与请求值一致。由 S0.4，这份证书在 $\mathrm{ev}_{\rho'}$ 下的典范残差为零，当且仅当它的值为零，即请求值为零。结算处 $e'=\mathrm{const}(\mathrm{ev}_\rho e)$，请求值是 $\mathrm{eff}_{\rho,\varepsilon}(e)$。

**(2) 必然出生。**$r(e\ominus e')=r(e)+\bigl(r(e')+1\bigr)+1$：加法节点贡献 $1$，线性节点贡献 $1$。此数为正，故初始状态不是常量，执行器的第一个动作是执行步；在出生编译中，这一步编译为责任准入（新责任的出生），而不是任何旧债行的付款。

**(3) 递归帧与运行。**定义帧的**秩** $\mathrm{rk}(\Phi):=(r(e),\,k+1)$，按字典序比较。下一帧由当前动作决定：

- 执行步：同一帧，深度加一，秩为 $(r(e),k+2)$；
- 结算：出生帧，旧状态取当前询问状态，程序取后继程序，登记输入取残差请求，深度归零，秩为 $(r(e)+r(e')+2,\,1)$。

两种情形都严格增大秩。帧序列 $\Phi_n$（$\Phi_{n+1}$ 为 $\Phi_n$ 的下一帧）因此沿字典序严格递增。帧的擦除确定其秩：原始输入由根的观察读回（擦除保留词汇与访问，观察读回登记的原始输入），因果深度由擦除后访问的历史读回。若 $\Phi_m$ 与 $\Phi_n$ 擦除相同而 $m<n$，则秩相同，与严格递增矛盾。故擦除单射。逐支检查后继合法：执行步使用直接回答的后继律，结算使用责任准入的后继律，两者都保持同一根上生成的活法则。现成规范询问运行时在计数 $n$ 的节点就是 $\Phi_n$ 的呈现：对 $n$ 归纳，节点的激活后继等于下一帧。每个帧的查询纤维是单点（它唯一的查询就是该帧的登记输入），故不需要外部的未来请求表。

**(4) 付款与出生分离。**把实际节点限制到固定根的债过程：执行步分支在同一数学行上发射同债付款回执，其整账去向等于联合执行步的账演化（定理 6.10(2) 的读法）；预算为零处没有付款宏（定理 6.10(3)）；结算分支的出生是新的责任准入。∎

**形式对应。**`JS/Native/ResidualRequest.lean`（`expression_eval`、`old_value`、`budget`、`action_is_paid`、`updated_value`、`residual_zero_iff`）；`JS/Native/Restructuring/Inquiry/Continuation/` 的 `Policy.lean`（`rank`、`Before`、`next_progress`、`frames_forward`）、`Inventory.lean`（`rank_eq_of_erasure`、`frames_erase_injective`）、`Occurrence.lean`（`successor_valid`）、`Runtime.lean`（`actual_node`、`macro_next`、`macro_next_preserves`）、`Payment.lean`（`actual_paid_receipt`、`no_paid_of_zero`）。提交 AB。

### S2.2 定理 7.7：登记输入的共享运行与后继供料

**对象。**命题 7.6 的固定数据：旧询问状态（根、访问、审计协议、演算、查询类型、承担者与权威）、完备复内积空间 $\mathcal H$ 上安装的识别、该访问的一步及其处置 $\mathrm{settle}$；另取根在该访问登记的原询问输入 $\iota$：一个投影位置、它在该发生处的激活证明、分类等式与查询类型等式。

**(1) 登记激活。**按 $\mathrm{settle}$ 的输出分支。

*全生成或联合残差支。*命题 7.6 给出程序包与计算询问状态，后者的根是装入计算询问后的根。在该根上新增一条**查询投影律**：投影类型为单点；在发生 $o'$ 处，激活当且仅当 $o'$ 是本次访问的准确发生；载荷类型为计算查询；投影值是以 $\iota$ 的原查询为关联的计算查询。新根 $r_\iota$ 是原根加这一面投影；访问不变。登记输入 $\iota'$ 取这面投影、准确发生的激活证明与分类等式（分类在准确发生处按定义取激活支），查询类型等式按定义成立。询问状态 $s_\iota$ 的根为 $r_\iota$，访问、审计协议与演算沿用旧状态；承担者经查询的关联读出；权威是旧权威沿新增投影面的提升；编译程序对每个查询取回答，回答面是程序包的结果面经投影嵌入。

于是 $s_\iota$ 对 $\iota'$ 的查询编译为回答（按定义）。回答面读出的表达式是程序包的整树程序，故解析器读回 $T$（定理 3.9(3) 与命题 7.6 的树等式）；值为 $\delta_{\tau(T)}$（定理 3.9(1)）；源状态是程序包的已付状态。旧状态对每个原查询 $q$ 的编译面经同一嵌入读回，所读出的仍是旧编译的典范令牌。

*其余四支。*终账支返回根编译器在源发生处的整账编译，三个残差支返回残差对象本身，与命题 7.6 一致。

**(2) 共享运行。**以 $s_\iota$ 为询问状态、以“返回 $\iota'$ 查询的原始输入”的常值函数为读取器，构造数学询问运行时（定理 6.10 的所有者无关安装，加上 §8.5 的运行时）。所有者无关安装的原始输入就是该查询的原始输入；由定理 3.9(3)，其表达式读回 $T$。定理 6.10(3) 给出计费历史长度 $r(\mathrm{prog}_\kappa T)$，由定理 3.9(2) 改写为 $\beta(T)$；完成值 $\mathrm{ev}(\mathrm{prog}_\kappa T)=\delta_{\tau(T)}$。各计数处数学行的整账写回与原材料、各运行偏移处的实际查询、回答与后继，是数学询问运行时在相应计数与偏移的节点等式（定理 8.12(3)）。

**(3) 后继供料。**输入只取活根、访问 $v$、识别与审计协议。在非终账分支，步携带后继 $\mathrm{succ}$ 与等式 $\mathrm{next}(v)=\mathrm{succ}.\mathrm{current}$；令 $v^+:=v.\mathrm{next}(\mathrm{succ})$。识别在 $v^+$ 生成一步并经 $\mathrm{settle}$ 分类，(1)(2) 的构造在 $v^+$ 重新给出供给与运行。终账支只返回整账编译。每个非终账支把前拍的程序包（对齐两支）或残差（三个残差支）与下一运行配对返回。

两拍的整账写回与下一当前：步的定义包含 $\mathrm{whole}(\mathrm{step}(v))=\mathrm{generatedLedgerAt}(v.\mathrm{current})$ 与 $\mathrm{nextCurrent}(\mathrm{step}(v))=\mathrm{generatedNextCurrentAt}(v)$，在 $v^+$ 同样成立。后继的目标发生等于根在 $v^+$ 当前的规范发生（目标发生是编译器为下一当前发射的事件），历史是发生的函数，故两处历史相等。∎

**直接使用。**§9 的联合程序（定理 9.2）以同一识别与同一后继为输入；定理 9.8 的默认运行在每个访问消费 (3) 的下一运行。

**形式对应。**`DJ/Input/{Source,Consumer}.lean`、`DJ/Input/Runtime/{Source,Consumer}.lean`、`DJ/Next/{Source,Consumer}.lean`；低源询问 `JS/OwnerFree/Installation/Math/{Inquiry,Frame}/Source.lean`。提交 AC。

---

## S3 定理 9.2 与定理 9.3

### S3.1 定理 9.2：同一程序承载完整时间、共同历史与作用差

**对象。**活根、时间访问 $v$、识别、审计协议；$\mathrm{step}(v)$ 落在全生成或联合残差支，带后继 $v^+$、历史转移与配对对齐；$T$ 为命题 7.6 的对齐构造子树。

**(1) 时间码。**根的时间访问由三种归纳历史之一给出：自初始当前有限步可达，封闭共尾，或共尾之后可达。对每一种，归纳类型 $\mathrm{Hist}$、$\mathrm{Post}$ 与原可达性证据之间有互逆的编码与解码，按构造子逐一定义并逐一验证。时间码 $c=(\text{当前},\text{历史码})$；$\mathrm{enc}$、$\mathrm{dec}$ 逐分量取上述编码与解码，故互逆，$\mathrm{enc}$ 单射。$\mathrm{act}(c)=(\mathrm{rcpt}(c),\mathrm{nx}(c))$ 的第一分量包含 $c$ 本身，故 $\mathrm{act}$ 单射。后继：时间访问的后继由编译器的下一当前与历史延长给出，编码在延长上逐构造子交换，于是 $\mathrm{enc}(v^+)=\mathrm{nx}(\mathrm{enc}\,v)$。

**(2) 联合程序。**节点类型取（$T$ 的对齐节点，时间码），$T_J$ 为 $T$ 的每个节点配上 $\mathrm{enc}(v)$。结果类型取五元组
$$(\text{效应折叠值},\ \text{收据树},\ \text{两段历史的原始材料},\ \text{两侧评价器输入},\ \text{两侧暴露计划}).$$
构造子 $\kappa_J(n,\vec y)$：第一分量是原依赖效应的单节点折叠 $\mathrm{effectFold}(n_1,[\,y_{i,1}\,])$；第二分量是以 $\mathrm{act}(n_2)$ 为根、以各子结果的收据树为子树的树；后三分量分别取两段历史的原始材料、两侧评价器输入与两侧暴露，与子结果无关。程序 $P=\mathrm{prog}_{\kappa_J}T_J$（定义 3.8）。环境 $\delta$ 把每个节点变量送到其状态点；$\delta'$ 把每个节点 $n$ 送到 $\delta_{n^+}$，$n^+:=(n_1,\mathrm{nx}(n_2))$（无后继时保持 $n_2$）。

*值。*对 $T_J$ 与子列作互递归：
$$\mathrm{ev}_{\delta'}(P)=\delta_{\mathrm{fold}_{\kappa_J}(T_J^+)},$$
其中 $T_J^+$ 是把每个节点换成 $n^+$ 的树——这与定理 3.9(1) 的证明相同，只是基点换成 $n^+$。由 S0.2，配对环境 $(\delta,\delta'-\delta)$ 下 $\widetilde P$ 的值为 $(\mathrm{ev}_\delta P,\ \mathrm{eff}_{\delta,\delta'-\delta}P)$；更新等式（命题 3.3）给出 $\mathrm{eff}_{\delta,\delta'-\delta}(P)=\mathrm{ev}_{\delta'}(P)-\mathrm{ev}_\delta(P)$。合起来，值为 $(\delta_F,\delta_{F'}-\delta_F)$，$F=\mathrm{fold}_{\kappa_J}T_J$，$F'=\mathrm{fold}_{\kappa_J}T_J^+$。

*分量。*对 $T_J$ 归纳：$F$ 的第一分量只依赖各节点的第一分量与子结果的第一分量，恰为 $\mathrm{fold}_{\mathrm{effectFold}}(T)=\tau(T)$；$F$ 的第二分量是 $T_J$ 逐节点取 $\mathrm{act}$ 的像树，其根为 $\mathrm{act}(\mathrm{enc}\,v)$，由 (1) 解码回 $v$。

*计费与付款。*由 S0.2 与定理 3.9(2)，$r(\widetilde P)=r(P)=\beta(T_J)$，而 $T_J$ 与 $T$ 形状相同，故 $\beta(T_J)=\beta(T)$。把定理 6.10 施加于读取器 $o\mapsto(\text{配对环境},\widetilde P)$：已付迹长度为 $\beta(T)$，每个计数 $k<\beta(T)$ 有严格付款，目标预算不回充，续行良基。

*逆读与后继。*在每个计数，安装面保留的表达式是 $P$，解析器读回 $T_J$（定理 3.9(3)），去掉码分量即读回 $T$。读回的根码解码为 $v$，其生成下一当前就是根在 $v$ 处的生成下一当前。更新态射 $(\mathrm{id},\mathrm{ev}_{\delta'})$ 从 $\mathrm{ev}_\delta$ 指向 $\mathrm{ev}_{\delta'}$；源侧取旧迹的关系词，目标纤维元素取旧、新两条迹关系词之和。由引理 S0.5，提升残差为零当且仅当目标纤维元素是旧纤维中某一元素的像；这份残差随结果原样保留。

**(3) 共同历史。**源、目标历史都是同一历史法则在两个发生处的历史；共同历史的事件、支撑、生成元闭包与关系闭包取两侧之并。两条转移把各侧的生成元按定义嵌入。完成映射把一侧生成元闭包中的词 $u$ 送到共同完成中同一个词的类，因此像为零当且仅当 $u$ 属于共同历史的关系闭包。两侧评价器取历史法则在两个发生处的忠实评价，在每个生成元上读回原忠实面的值；关系可靠性两侧等价。完成载体 $\mathrm{Src}$、$\mathrm{Tgt}$ 之积带有由两条转移诱导的作用与观察，构成作用模型；配对与对偶作用由历史的标量配对给出；测量 $\mathrm{Src}\times\mathrm{Tgt}\to\ell^2(\mathcal H\times\mathcal H)$ 与该空间上的线性等距演化组成积分—相干联合作用数据。

**(4) 作用差的逆判据。**记 $\partial_s,\partial_t$ 为两侧的微分（测量），转移满足 $\partial_t\circ\iota=\partial_s$。

*若*存在 $r$ 使 $\partial_s r=\partial_s a_s$ 且 $\iota(r)=a_t$：则 $d=\iota(r)-\iota(a_s)=\iota(r-a_s)$ 属于 $\mathrm{range}\,\iota$，像残差为零；$\partial_t d=\partial_s(r-a_s)=0$，观察残差为零。

*反之*，像残差为零给出 $r_0$ 使 $\iota(r_0)=a_t$，于是 $d=\iota(r_0-a_s)$，观察残差 $\partial_td=\partial_s(r_0-a_s)=0$，故 $r_0\in\mathrm{Fib}_{\partial_s}(a_s)$。

计算程序是三输出表达式：差 $d$，它的测量，及它在余核中的类；其剩余计数为 $25$。定理 6.10 给出 $25$ 步已付迹，每步严格付款，续行良基，整账与下一当前在每个计数保持。

**(5) 字面后继。**$\mathrm{step}(v)$ 的目标发生是编译器为下一当前发射的事件，等于 $v^+$ 当前的规范发生，而后者就是 $\mathrm{step}(v^+)$ 的源发生。历史、生成元闭包、关系闭包、暴露与暴露树都是（当前，发生）的函数，故两两相等；目标词沿生成元闭包的相等运到下一源词，底层的词不变。∎

**形式对应。**`Occurrence/Temporal/{Source,Action/Source,Action/Inverse}.lean`；`Occurrence/Temporal/History/Common/{RootSource,Closure,Evaluator/Source,Action/Source}.lean`；`DJ/Joint/{Source,Laws,Consumer,TargetDifference,TargetProgramme,TargetConsumer}.lean`；`DJ/Next/{Material,Pursuit}.lean`。提交 AD。

### S3.2 定理 9.3：全部作用者的共同恢复

**对象。**定理 9.2 的数据与一个计数。源、目标配对展开树分别以全部配对位置为节点，每个节点带暴露 $(M_p,A_p,U_p)$。作用者是树迹中的成员；节点 Hilbert 的指标取树迹的位置（同一载荷重复出现时分别计入）。

**(1) 全词模型。**联合载体取两侧载体之积；字母 $\ell$ 的作用是该作用者的载体作用（源作用者作用于第一分量，目标作用者作用于第二分量，“同时”同时作用两侧的根），根作用者的作用就是原步的源、目标暴露作用。读出 $\mathrm{rd}$ 是粗读口与全部作用者测量的积。引理 S0.6 给出商 $\mathrm{Mod}$、纤维刻画与完成等价；完成载体中两元素相等当且仅当它们对所有后续词的读出相同，这是 S0.6(ii) 在完成一侧的表述。

**(2) 有序效应历史。**取 $W=\mathcal H^{\text{作用者}}$，$U_\ell$ 对被选作用者的分量施加 $U_p$、其余分量不变（“同时”对两侧根分量施加），$M$ 为各作用者的测量。引理 S0.7 给出总残差等于各步残差经其后演化运送之和，历史长度为 $|w|$；单字母情形，总残差就是该作用者的协变效应 $U_pM_p(x)-M_p(A_px)$。

**(3) 节点 Hilbert。**测量 $\mathrm{meas}:\mathrm{Mod}\to\ell^2(\text{位置};\mathcal H)$ 逐位置取该作用者的特征（作用者测量经模型读出）。在 $\ell^2$ 中范数平方是各坐标范数平方之和，故
$$\|\mathrm{meas}(x)\|^2=\sum_p\|M_p(x)\|^2.$$
字母在 $\ell^2$ 上的演化逐坐标取 $U_p$ 或恒等，故是线性等距。节点效应按协变耦合残差的定义逐坐标展开。

**(4) 未来恢复与三面。**

*未来恢复。*设 $x\in\mathrm{Mod}$ 被粗读口与全部未来读口同时送到零。全部未来 $\mathcal H$ 读口为零意味着：对每个前缀界与每个词，每个作用者在词作用后的测量与零点处相同。粗读口为零给出粗读出在每个词作用后与零点相同。于是 $x$ 与 $0$ 在每个词作用后的全部读出相同，由 (1) 得 $x=0$。合成映射单射，$\mathrm{Mod}$ 与其像线性同构，两个方向的复合是恒等。

*三面。*以 $I=\mathrm{Mod}$（作用为模型推进）、$H=$ 全部前缀界上的 $\ell^2$ 族（作用为逐界演化）、$Q=$ 粗模型（作用为粗推进），$c$ 为未来读口，$m$ 为粗限制，作引理 S0.8 的完整轨道载体 $\mathcal C\subseteq I\times H\times Q$。积分面与粗读面就是第一、第三分量。相干面把第二分量（全部前缀界上的族）送到沿前缀界限制的逆极限：逐界限制与演化交换，故这是相容族的完成映射，并与每个字母的演化交换；完成映射的每一界坐标就是第二分量在该界的值，所以相干面为零当且仅当第二分量为零。于是三面同时为零的元素三个分量都为零，即为零：三面联合单射，在像上双逆，并与词作用交换（S0.8(ii)）。

**(5) 有偿恢复。**对点、种子词、历史词与查询词 $q$，所有者无关计算执行的是按查询词生成的程序，其剩余计数由程序预算引理给出为 $|q|+3$；定理 6.10 给出已付迹长度 $|q|+3$，计算值等于下一值（值读回引理）。恢复映射施加于作用后的元素，第一分量按 (4) 的同构读回下一值。配对库存作为新生库存的一部分进入下一次出生，同债不回充（定理 6.10(2)）。∎

**形式对应。**`AW/{Source,Complete/Source,EffectHistory/Equation,EffectHistory/Source}.lean`；`AW/NodeHilbert/{Source,Future/Recovery/Source}.lean`；`AW/NodeHilbert/Future/Wave/{Words/Kernel,Full/Source,Recovery/Source,Recovery/Consumer,Incidence/Consumer}.lean`。提交 AD。

---

## S4 定理 9.5–9.7

### S4.1 定理 9.5：母准入

**对象。**询问帧 $\Phi$ 与源程序 $\mathcal S=(L,\text{读取器},\ldots)$（定义 9.4）。共享运行时把 $\Phi$ 与 $\mathcal S$ 的读取器装成询问状态并回答其唯一查询；$s$ 是这一已回答状态，$o$ 是其当前发生，$\rho'$ 是共享运行时字面下一状态的查询原始输入的环境。

**(1) 材料与值。**材料按定义装配：环境 $\rho$ 与表达式 $e$ 取读取器在 $o$ 的输出，增量 $\varepsilon=\rho'-\rho$，已付状态 $(e',t)$ 取共享运行时在 $o$ 的结果，承担者取 $s$ 对该查询的承担者。登记输入是定义 8.11 的残差请求，环境为 $\rho+(\rho'-\rho)=\rho'$。值与残差由 S2.1(1) 给出。

**(2) 必然准入。**残差请求的初始状态若为结算，其预算为零（执行债律在结算处预算为零）；但残差请求预算为 $r(e)+r(e')+2>0$（S2.1(2)），矛盾。故源的第一个动作是执行步。出生程序由旧状态、查询、登记输入、源包、权威与这一步生成；在 $s$ 的根与访问上，编译程序把唯一查询送到该出生程序在精确时间因果事件上的生成，即责任准入，等式按定义成立。

**(3) 目标。**准入目标携带：字面下一当前等于目标状态的（词汇，根，访问）；整账的第一次写入；每个旧投影在目标上的结果与原结果相等（异构相等）。后继合法性由“主动节点在准入后继下保持生成活法则”的一般准则给出，其前提正是上述字面下一当前与编译等式。

**(4) 新生帧。**新生帧取 $s$ 为旧状态、残差请求为登记输入、读取器环境、深度零，库存为已付迹的全部暴露。其当前状态按定义就是准入目标状态。定理 8.12 的运行时以它为初始帧：初始节点的擦除等于目标呈现的擦除；每一拍的宏后继与活法则保持是 S2.1(3) 的节点等式；不回充与良基是 S2.1(4) 与定理 6.10(2)。

**(5) 下一内容。**由 (S0.1) 与更新等式，已付结果的（旧，效应）之和等于程序在更新环境中的值：
$$\mathrm{ev}_\rho(e)+\mathrm{eff}_{\rho,\varepsilon}(e)=\mathrm{ev}_{\rho+\varepsilon}(e).$$
新生帧在每个发生处的环境由这一值的环境读出给出。宏历史程序满足 $\mathrm{next}(\mathrm{hist}_k)=\mathrm{hist}_{k+1}$；初始帧的活跃环境已是第 $k$ 拍历史的下一值，即第 $k+1$ 拍，新生帧再推进一拍，故为第 $k+2$ 拍。新生库存取旧库存与已付暴露的并列种子，两者都是它的部分（左、右嵌入）。

**(6) 原生移位。**同一阶段的查询帧经原生游标移位得到新的帧；对它施加 (1)–(4)，即得编译、整账首写、后继合法、字面后继、每个偏移的运行、不回充与良基；移位后环境就是游标移位的实际环境，效应与逆读由残差请求读出。∎

**形式对应。**`ACT/Programme.lean`、`ACT/Receipt/{Source,Execution,Compiler,Consumer,Runtime}.lean`、`ACT/Target.lean`、`ACT/Receipt/Faces/{Source,Action,Consumer,Native/Source,Native/Consumer}.lean`；下一内容 `AW/NodeHilbert/Future/Wave/Incidence/Environment/{Source,Consumer}.lean`。提交 AD。

### S4.2 定理 9.6：有类型库存越过准入

**对象。**定理 9.5 的设置；物理原始输入 $(\rho_P,e_P)$（变量取物理类型 $\mathrm{Var}_P$）与已付结果，低层原始输入 $(\rho_L,e_L)$（变量取 $L$）与结果。绑定 $\sigma:\mathrm{Var}_P\to\mathrm{Expr}_L$，$\sigma(x)=\mathrm{const}(\rho_P(x))$。

**(1) 绑定保值。**对表达式结构归纳证明 $\mathrm{ev}_{\rho_L}(e[\sigma])=\mathrm{ev}_{\rho_P}(e)$：变量处 $\mathrm{ev}_{\rho_L}(\mathrm{const}\,\rho_P(x))=\rho_P(x)$；常量处两边相同；加法、线性、双线性节点由归纳假设逐项相等。形式词按线性延拓。低层查询 $(\rho_L,e_P[\sigma])$ 的值因此等于物理查询的值。代换迹是物理已付迹沿 $\sigma$ 的代换，起点为 $e_P[\sigma]$，关系边界随之代换；物理已付状态是常量，代换后仍是常量。任何以常量为终点的执行迹，其长度等于起点的剩余计数（命题 3.7(1)），故代换迹的长度为 $r(e_P[\sigma])$。

**(2) 库存登记与读回。**完整材料（两侧原始输入与结果、绑定、两份已写库存与代换迹）作为一面投影安装在帧的基础根上，载荷类型就是材料的类型。母准入目标的投影律继承旧投影律（定理 9.5(3)），在这面投影处的结果与原结果异构相等；类型相等由同一异构等式给出，沿它把结果转换为材料类型，即得到材料本身。

**(3) 新生库存。**物理库存中的每个事件经 $\sigma$ 代换迁入低层语言，迁入后与低层库存并列成为新生库存；左、右嵌入保证两侧每个事件都在其中。新生帧按定理 9.5 运行；下一库存是新生库存的扩展，坐标映射在 $\mathrm{mathNext}$ 与 $\mathrm{nextBorn}$ 两种动作下都单射，且逐事件读回原事件。

**(4) 逆读。**以新生库存的事件为指标，词族 $W$ 的联合映射 $W\mapsto(\mathrm{index}\mapsto(\mathrm{ev}_\rho,\mathrm{eff}_{\rho,\varepsilon})(W_{\mathrm{index}}))$；实际词族的典范残差为零当且仅当其像为零（S0.4），而像就是结果值。下一拍的逆读是更新态射诱导的映射（S0.4）。共尾的每一拍：关系词在该拍环境下的配对值，读出下一拍场在偏移零处的值；已付迹长度等于原始输入的剩余计数。∎

**形式对应。**`ACT/Receipt/Inventory/{Source,Laws,Installation}.lean`；`Inventory/Born/{Source,Consumer}.lean`；`Inventory/Born/Vector/Fibre/{Source,Consumer}.lean`；`Inventory/Born/Coordinates/Actual/{Source,Query}.lean`；`Coordinates/Actual/Cofinal/{Source,Consumer}.lean`。提交 AE。

### S4.3 定理 9.7：词—状态配对与有偿前缀

**对象。**运行时及其源；状态 $s$ 的旧环境 $\rho_s$ 与增量 $\varepsilon_s=\rho_{\sigma(s)}-\rho_s$。轨道变量的绑定 $\sigma$ 满足两条读回：$\mathrm{ev}_{\rho_s}(\sigma x)=\rho_{\sigma(s)}(x)$ 与 $\mathrm{eff}_{\rho_s,\varepsilon_s}(\sigma x)=\varepsilon_{\sigma(s)}(x)$。

**(1) 配对。**$\langle w,\cdot\rangle$ 在基点 $\delta_s$ 上取阶段库存 $(\mathrm{ev}_{\rho_s}w,\mathrm{eff}_{\rho_s,\varepsilon_s}w)$，由自由模泛性质（命题 2.3）唯一线性延拓；对 $w$ 线性由求值与效应的线性给出。

**(2) 协变与像作用。**在基点上：
$$\langle w[\sigma],\delta_s\rangle=\bigl(\mathrm{ev}_{\rho_s}(w[\sigma]),\ \mathrm{eff}_{\rho_s,\varepsilon_s}(w[\sigma])\bigr)=\bigl(\mathrm{ev}_{\rho_{\sigma(s)}}w,\ \mathrm{eff}_{\rho_{\sigma(s)},\varepsilon_{\sigma(s)}}w\bigr)=\langle w,A\delta_s\rangle,$$
中间一步是代换引理：代换后求值等于在“变量取代换式之值”的环境中求值，效应同理；两条读回把这个环境认作 $\rho_{\sigma(s)}$ 与 $\varepsilon_{\sigma(s)}$。两边对 $\mathbb Z[S]$ 线性，故整个载体上 $\langle\sigma^*(\cdot),\cdot\rangle=\langle\cdot,A(\cdot)\rangle$。这说明 $(\sigma^*,A^*)$ 是从配对到自身的态射，由 S0.4 诱导余像上的作用；读出公式在 $\mathrm{can}[e]$ 上由定义给出。

**(3) 迭代即时间。**对 $n$ 归纳：$n=0$ 平凡；归纳步用 (2) 的基点等式于第 $d$ 拍，再对 $d+1$ 用归纳假设。$\mathrm{act}^n[e]=[e[\sigma]^n]$ 由诱导映射与典范映射交换得到。

**(4) 前缀计费。**第 $i$ 个前缀执行 $\widetilde{e[\sigma]^i}$，由 S0.1 与 S0.2，迹长 $r(e[\sigma]^i)$；求和得 $\Sigma_n$。批量查询把 $n+1$ 项装入向量值语言：每一项经一个坐标嵌入节点与一个累加节点进入，剩余计数为各项之和加 $2(n+1)$；执行长度等于剩余计数（命题 3.7(2)）。定理 6.10 给出逐步严格付款与同债谱系。

**(5) 调用恢复。**调用帧在计数 $c+i$ 处的实际查询材料给出该处环境；所需快照的旧值与增量逐项取自这些环境（增量为相邻两处之差）。由此组装的批量环境与轨道批量环境按定义逐坐标相等，故两个查询的结果值相等；每个调用的已付迹长度等于其剩余计数（定理 6.10(3)），求和得调用计费等于调用成本。∎

**形式对应。**`Operations/Inquiry/Context/Native/Pairing/{Source,Orbit/Source,Orbit/Action,Orbit/Iteration,Orbit/Iteration/Batch,Orbit/Iteration/Current}.lean`；调用与历史 `…/Batch/Calls/{Source,Consumer,History/Source,History/Consumer}.lean`（完整前缀见正文附录 D.2）。提交 AE。

---

## S5 定理 9.8：默认运行执行源自产请求与子树

**(1) 源自产请求。**取定理 9.2 的联合程序根与已安装读取器，作所有者无关安装的源询问帧，种子取登记表达式生成元的零展开。默认运行时的源程序以“本发生的原始请求”为读取器：在发生 $o$ 处，读取器返回为 $o$ 生成的请求表达式与环境。把定理 9.5 施加于这一源程序：查询原始输入就是安装面读出的请求（按定义）；结果值等于请求的执行值（定理 6.10 的完成值，连同 $\mathrm{ev}$ 的可靠性）；已付迹长度等于登记输入的剩余计数（定理 6.10(3)）；新生配对库存按定理 9.5(5) 由既往已写与本次已付两部分组成；每个计数的实际查询、回答与后继是运行时的节点等式。账根相同是构造上的恒等。分支版本的核心表达式与关系表达式各自成为二元批量的一个坐标，批量执行的迹与代换迹进入初始库存。

**(2) 子树进入主表达式。**主表达式是三项之和：原查询表达式、旧码处子树、新码处子树，各项经坐标嵌入进入输出类型。某码处的子树：若识别在该码的访问没有后继，子树为零常量；否则为该码处子程序原始输入的嵌入。于是
$$\mathrm{ev}(\text{主})=\bigl(\mathrm{ev}(\text{查询}),\ \mathrm{ch}(c_{\mathrm{old}})+\mathrm{ch}(c_{\mathrm{next}})\bigr),$$
其中子树值的第一分量为零。剩余计数逐项相加，再加两次加法与一次线性嵌入，共三个组合节点：$r(\text{主})=r(\text{查询})+c_{\mathrm{old}}+c_{\mathrm{next}}+3$。已付迹长度：所有者无关安装的迹长等于剩余计数，查询自身的已付迹长度等于 $r(\text{查询})$，代入即得。两棵子树的执行长度等于各自的剩余计数（命题 3.7(2)）。旧库存与新付事件的保留由并列种子的嵌入给出；旧、新作用者分量之和是本次源操作的状态点，由完整作用者载体的读出读回。

**(3) 子树环境。**在被供给的发生处，子树环境由该环境中原绑定的读出定义；新生帧的环境取实际更新后的环境（定理 9.5(5)），子树环境随之由同一绑定读出。标量与配对库存的保留与 (2) 同理；运行时初始节点与每拍输入是运行时的定义式。∎

**形式对应。**`ACT/Inventory/Pair/Residual/Joint/Past/NextObservation/Request/Acted/{Source,Consumer}.lean`；`DJ/{Joint,Branch}/Primary/{Source,Consumer}.lean`；`DJ/Branch/JointQuery/Actor/{Source,Embedding,Action/Source,Operation/Source,Operation/Consumer}.lean` 与 `Actor/Operation/Query/Inventory/{Language,Source,Consumer,Action/Source,Action/Consumer,Live/Source,Live/Consumer}.lean`；默认后继 `DJ/Next/{Source,Consumer}.lean`。提交 AE。

---

## S6 首发选集编号与证明位置

下表把首发选集的主张编号对应到正文结果与书面证明位置。选集编号与公开代码选集的首发映射（H0mework `docs/first-release-map.json`）中的 `core.Cn` 一致，供逐条复核。

| 选集编号 | 正文结果 | 书面证明 | 源提交 |
| --- | --- | --- | --- |
| core.C1 | §6.1 命题 6.1 | 正文 | H（base 回归修复） |
| core.C2 | §6.4 定义 6.6、定理 6.7、注 6.8 | 正文 | H |
| core.C3 | §2.1 定义 2.1、命题 2.2 | 正文 | H |
| core.C4 | §8.4 运行时段 | 正文 | H |
| core.C5 | §8.4 命题 8.9、表 4、图 5 | 正文；附录 C.3 | H |
| core.C6 | §8.4 命题 8.10 | 正文 | H |
| core.C7 | §3.1–§3.3 定义 3.1–3.2、命题 3.3–3.6 | 正文 | H |
| core.C8 | §4 定理 4.4、4.6、4.7、命题 4.8 | 正文；附录 A–B | H |
| core.C9 | §2.2–§2.4 命题 2.3、定义 2.4、命题 2.5 | 正文；附录 A.1 | H |
| core.C10 | §5 定义 5.1、命题 5.2、定理 5.3 | 正文 | H |
| core.C11 | §7.1–§7.3 命题 7.1、定义 7.2、命题 7.3–7.5 | 正文；附录 C.6 | H |
| core.C12 | §6.2–§6.3 定义 6.2–6.3、命题 6.4–6.5、表 2 | 正文；附录 C.5 | H |
| core.C13 | §8.1–§8.3 定义 8.1、命题 8.2–8.3、定理 8.4、定义 8.5、定理 8.6–8.7、命题 8.8 | 正文；附录 C.1–C.4 | H |
| core.C22 | §6.5 定义 6.9、定理 6.10 | S1 | AB |
| core.C23 | §3.4 命题 3.7、定义 3.8、定理 3.9；§6.5 命题 6.11；§10.1 | 正文（完整） | AB |
| core.C24 | §8.5 定义 8.11、定理 8.12、例 8.13、图 6 | S2.1 | AB |
| core.C25 | §7.3 命题 7.6 | 正文（完整） | AB |
| core.C26 | §7.3 定理 7.7(1)(2) | S2.2 | AC |
| core.C27 | §7.3 定理 7.7(3) | S2.2 | AC |
| core.C28 | §9.1 定义 9.1、定理 9.2 | S3.1 | AD |
| core.C29 | §9.2 定理 9.3 | S3.2 | AD |
| core.C30 | §9.3 定义 9.4、定理 9.5 | S4.1 | AD |
| core.C31 | §9.3 定理 9.6 | S4.2 | AE |
| core.C32 | §9.3 定理 9.7 | S4.3 | AE |
| core.C33 | §9.4 定理 9.8(1) | S5 | AE |
| core.C34 | §9.4 定理 9.8(2)(3) | S5 | AE |
