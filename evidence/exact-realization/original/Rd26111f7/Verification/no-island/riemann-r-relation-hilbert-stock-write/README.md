# 原关系的完整 Hilbert 库存与字面后继

原两槽的总场以原 gap 系数与完整正交余量表示，原 exterior 槽另外保留。原生成闭包内的关系词经实际 evaluator 与原 factor 写入库存，可逆地读回完整两槽。库存相等的纤维精确等于原 factor 纤维。

库存步进对 gap 采用已付 Fourier 更新，对余量施加原 R。每个原 Model 都与该步进交换。原两枚字面 `sourceClass` 保留各自 exterior 槽，并接回原 disposition、整账和 next。同总场的平衡对检验了保留独立 exterior 槽的必要性。

```sh
python3 Verification/no-island/riemann-r-relation-hilbert-stock-write/certify.py \
  --repo "$PWD" --compiled-root "$CP564_COMPILED_ROOT" \
  --base-lean-path-file "$CP564_LEAN_PATH_FILE" --output "$CP564_AUDIT_DIR"
```

加 `--verify-inputs-only` 可静态核对正式 Main 源码、所选对象和已付父证据。
