# c0002：同一置信合同的候选生成修订

[rd0001](criterion.md)的完整source carrier、四个forecaster、权重、全部原序prefix、
阈值40及两run预算1/20保持。c0001两run各35候选均被排除，完整域判决为未决。
[原首轮](primary-first.json)及其attempt保留；候选排除不升级为全域no-go。

原数值求解器在闭域边界遇到无限目标，数值差分产生无效值，最佳候选仍在名义起点。
c0002使用全部四component的解析梯度及完整polar Jacobian。
候选搜索限制为`mu∈[-.99,.99]`、`radius∈[0,.999999]`、`angle∈[-pi,pi]`，
避免试探zero-support边界。它是完整carrier内部的候选生成子域，
完整经验置信域仍包含全部合法读出率和zero边界。

沿原35个固定起点、SciPy1.13.1、L-BFGS-B、maxiter1500、ftol1e-12、40bit有理化；
解析梯度的gtol固定1e-7，maxls固定50，其他参数沿SciPy默认。
起点与候选顺序沿原声明，不据统计结果选择编码、分母、切点、模型或阈值。
生成回执记录初始/最终目标、解析梯度及实际参数位移。
新driver在执行前冻结本修订及全部新程序，独占创建c0002回执。
失败保留未决；成功须沿原Decimal及独立整数检查，核每run全部prefix和完整源概率。
独立概率仍由原八维Born收缩自产，不调用候选梯度、主概率公式或主数值回执。

科学合同版本`stage10-munich-readout-rd0001`，候选修订`c0002`。
新回执为`primary-attempt-c0002.json`、`primary-first-c0002.json`、
`primitive-witness-c0002.json`、`independent-attempt-c0002.json`与`independent-first-c0002.json`。
