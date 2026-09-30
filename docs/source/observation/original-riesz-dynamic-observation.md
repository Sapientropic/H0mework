# 原 Pa 源波进入已有动态观察 Model

固定原c、h、source w_a/w_b及其原Pa波W_a/W_b，见[原source能量](original-riesz-source-energy.md)。
令W=W_a+F W_b，A_h为原 `burnolPairedAmbientCompression`，
o_c为原 `burnolCompletedMellinEvaluator`。原K、Pa、B、Q与全部残差保持。

## 原 source 与一步读取

sourceWave只把原W送入既有even-ambient projection。
0≤h≤log2时，旧source已生成的Pa归属被公开复用：
projection所得vector在完整L²上仍是原W，并保留原Pa membership。

原zero经完整Pa正交性给当前o_c(W)=0。
原B的能量读取、literal B=χ_c K−A_h K及A_h的实际对称性共同生成

```text
o_c(A_h W) = (1/2) star(E_h),
E_h = <w_a,w_a> + <w_b,w_b>.
```

同一owner的已生严格能量使0<h≤log2时该后继读数非零。
这条方程没有把未来读数、非零值或Pa landing当source输入。

## 已有引擎直接消费

modelWave逐字调用既有 `SourceGeneratedActionObservationHistory.projection`，
action/observer就是上述两枚原CLM的linearMap面；未新建动态核或Model。
既有modelReadout_projection、modelAction_source与model_fibre_iff生成：

```text
模型当前读数 = 0
模型作用后读数 = (1/2) star(E_h)
modelWave ≠ 0                  （原owner与正shift范围）
```

完整未来观察由A_h的实际迭代生成，不接受未来答案表。
这个Model的精确范围是原Mellin读者及这枚固定作用的全部迭代。

## 原 Q 的真实作用差项

同一原源同时生成

```text
Q W = 0
Q(A_h W) ≠ 0
Q(A_h W) ≠ 原PaPairedDilationCompression_h(Q W).
```

静态投影先删去这条方向会丢失实际后继读数；已有动态Model保留它。
这不否定原压缩算子在自身carrier上的定义，也不是领域或框架no-go。
h=0的modelWave由原source programme直接生成0，无需zero输入。


## 同一 Model 的原 L² 实现

原A_h/o_c的CLM面直接交给[既有观察核的Hilbert实现](../../realization/algebraic/source-generated-observation-history.md)。
闭核来自实际全部stage读者；原ambient完备性生成原商范数及正交代表R，完整核残差D保留：

```text
D W + R(modelWave) = W                  （完整原L²）
‖W‖² = ‖D W‖² + ‖modelWave‖²
o_c(A_hⁿ R(modelWave)) = o_c(A_hⁿ W)
R(modelAction modelWave) = A_h R(modelWave)
D(A_h W) = A_h D W
‖E_h‖ ≤ 2 ‖o_c‖ ‖A_h‖ ‖modelWave‖
```

后两条作用方程消费原A_h已生成的对称性。原zero的后继能量读数保持，原owner及正shift给恢复代表严格正范数；
h=0由原source programme生成零。这里的R是同一Model在原空间中的代表，不替换原K。

## 范围与入口

模型作用不是living-runtime tick。原root/current/整账/next未因此改变。
完整残差仍属于上述实际观察核；原Q B与fixed −ρ保留自己的源责任。

- 正式 `Physical/.../Finite/Pairing/CoPoisson/Observed/{Source,Model,Projection,Hilbert}`。
- 通用 `GenericFoundation/Operations/Observed/{History,Kernel,Coimage,Hilbert}`；当前责任只见[maximum active](../../../handoffs/no-island-no-magic-mathematics-active-route.md)。
