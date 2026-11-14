# 原 R 后继价格的完整前驱

对任意有界 Hilbert 作用，用真伴随拉回每个后继测元。所有有限残差为零且前驱能量有界，恰好刻画该作用的可观察价格像。测元能分离输出时，全部前驱是读回前驱沿作用核的平移。

原 R 的相邻系数更新有逐槽前缀逆，因而原完整图上的前驱唯一。用字面后继的原 K 价格读回原前驱和两拍关系库存，并接原整账与后继。零作用反控使用同一实际非零原场，区分合法的当前价格与指定作用的后继价格。

```sh
python3 Verification/no-island/riemann-r-action-price-inverse/certify.py --repo "$PWD" --compiled-root "$CP620_COMPILED_ROOT" --base-lean-path-file "$CP620_LEAN_PATH_FILE" --output "$CP620_AUDIT_DIR"
```

加 `--verify-inputs-only` 核对正式 Main、选中对象和已付来源。
