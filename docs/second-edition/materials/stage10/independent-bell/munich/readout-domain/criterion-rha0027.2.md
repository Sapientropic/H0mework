# RHA0027.2：续接输出路径规范化

RHA0027.1 续接已恢复同一已核 pump 源，并写出首份局部 density 证书；
后续结果索引将相对路径直接交给 `relative_to(absolute ROOT)`，产生编排异常。
原失败 attempt 与已写证书保留。

此修订仅在工作开始前将输出目录 resolve 为绝对路径，并核它属于 workspace。
源、曲线、精度、误差、缓存、真实 cuts 和构造器不变。使用新独占目录执行，代码先提交冻结。
