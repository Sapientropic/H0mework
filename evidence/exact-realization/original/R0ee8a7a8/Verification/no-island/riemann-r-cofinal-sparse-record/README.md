# 原 R 尾部的稀疏价格采样与回写

原尾的固定 Fourier–K 价保证新生列在任意晚的尾上有非零残差。保留原采样地址，选择严格更晚的首个非零枢轴。扣除旧拟合在该地址的预测后，用一个实际新读数恢复新生系数，并复用旧 Gram 求解。

旧价和追加价都来自同一实际场。记录从空表递推，每次只添一个地址。原价格系数进入 CP589 的完整 Γ² 图与关系库存，分别沿原作用写到字面下一拍。反控确认非零新生量的最新读数无法由旧预测代替。

```sh
python3 Verification/no-island/riemann-r-cofinal-sparse-record/certify.py \
  --repo "$PWD" --compiled-root "$CP590_COMPILED_ROOT" \
  --base-lean-path-file "$CP590_LEAN_PATH_FILE" --output "$CP590_AUDIT_DIR"
```

加 `--verify-inputs-only` 核对正式 Main 源码、所选对象和已付父证据。
