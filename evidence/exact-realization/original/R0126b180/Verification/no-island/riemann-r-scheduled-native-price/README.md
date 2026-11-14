# 原调度收据的 Fourier–K 价格与库存回写

每个调度地址保留原 rooted material 与同一前驱的实际 paid material。由 paid 表达式在其环境中求值，合成完整四支后，在原 Q 上读取固定 Fourier–K 价格。追加采样保留每条旧收据，新增收据的地址严格递增。

从实际价格列组成的有限记录驱动原稀疏出生解码器，恢复旧系数与新增系数。恢复结果分别进入原 Γ² 图和原关系库存的后继作用。独立核验同时消费同前驱的原整账与字面下一拍。

```sh
python3 Verification/no-island/riemann-r-scheduled-native-price/certify.py --repo "$PWD" --compiled-root "$CP591_COMPILED_ROOT" --base-lean-path-file "$CP591_LEAN_PATH_FILE" --output "$CP591_AUDIT_DIR"
```

加 `--verify-inputs-only` 核对正式 Main 源码、所选对象和已付父证据。
