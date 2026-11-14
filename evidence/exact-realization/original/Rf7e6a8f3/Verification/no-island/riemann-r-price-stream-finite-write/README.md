# 原 Division 的有限价格流写入

完整已准入价流的前缀能量上确界等于原 Γ² 图的范数平方。总能量与已保留前缀之差恰为误差平方，由此选出严格达到容差的最短前缀。

将该前缀的有限逆交原 R，得到下一拍的有限图和原关系库存，并在同一有限图上读取各原 K 价。完整图与关系的误差、每项价格的误差分别由对应算子范数控制。

最短前缀选择使用整条已准入价流的能量上确界。独证反控在同一原 Division 的非零图上验证零长度前缀留下全部误差。

```sh
python3 Verification/no-island/riemann-r-price-stream-finite-write/certify.py --repo "$PWD" --compiled-root "$CP618_COMPILED_ROOT" --base-lean-path-file "$CP618_LEAN_PATH_FILE" --output "$CP618_AUDIT_DIR"
```

加 `--verify-inputs-only` 核对正式 Main、选中对象和已付来源。
