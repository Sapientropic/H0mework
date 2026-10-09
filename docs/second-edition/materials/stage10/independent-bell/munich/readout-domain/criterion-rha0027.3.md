# RHA0027.3：保存成功的局部检查直接续接

RHA0027.1 的首份完整局部 density 证书已成功写出，随后失败发生在路径索引，不在 residual。
此修订读取已完成并冻结的那一份证据；其 source record、执行依赖、曲线、初态、精度、价格
和真实 cut 必须与当前 owned source 逐字段相同。原 `verify` 继续核 source-frame，已付缓存
不接收任意 JSON、未完成检查或旧 endpoint 替换。

仅这份完成的检查复用，其他九份继续完整 residual。数学源与误差不改，失败 attempt 和旧文件
保留，使用新的独占输出目录。证据复用是既有检查的读取，不登记为新数学认证。
