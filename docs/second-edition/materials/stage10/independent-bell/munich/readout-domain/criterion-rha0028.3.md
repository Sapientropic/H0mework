# RHA0028.3：下界原价与向上舍入半径分别核验

主完整门界已经按 RHA0028.2 写出。独立比较原先将 `centre - rounded_error` 与
采用未舍入 payment 的既定下界强制相等，两者差异为输出向上舍入。此修订独立重算
原 payment、逐项核输出半径的 dyadic ceiling，再核 `max(0, centre-payment)`；
下界仍不得超过独立有理 Mark／raw population 证明的下界，不改变主算法或科学阈值。

主结果、原 attempt 和失败保留。显式 `--reuse-completed-primary` 只读取这枚实际完成的
冻结回执；原主数学代码、已发行 inlet、完整报告字节与字段必须相同，再执行新的独立检查。
该开关不能接收任意 path、endpoint 或替换源，不重算已经完成的主界、pump 或 density。
