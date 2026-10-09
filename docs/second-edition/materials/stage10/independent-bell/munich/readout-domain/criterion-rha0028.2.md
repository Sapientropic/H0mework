# RHA0028.2：完整 pattern 覆盖与同发生绑定

独立消费者逐项要求原四个 pattern 完整有序；II 下界、完整 activity 上界与当前 inlet
必须指向同一 retarded source occurrence。缺失 pattern 或借用另一 source 的同形界不准入。
原数值算法与误差价保持，RHA0028.1 的五项已完成控制保留；新增缺 pattern 反控及来源绑定
先提交，再执行原完整门首计算。
