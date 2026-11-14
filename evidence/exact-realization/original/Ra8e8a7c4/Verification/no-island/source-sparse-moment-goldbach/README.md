# Goldbach 原 actor 的稀疏矩

从有限有号源的前 2k 个矩，取最大非奇异 Hankel 块。该块与下一矩列生成递推，只在实际可用的源地址找根。恢复的地址再用幂矩阵读回原权重。

Goldbach 对完整原 actor 的两相邻状态取整系数差，用四个有理矩恢复其作用。末态的同一解码接回原 Reached 或 Exhausted 消费与收据。

```sh
python3 Verification/no-island/source-sparse-moment-goldbach/certify.py --repo "$PWD" --compiled-root "$CP614_COMPILED_ROOT" --base-lean-path-file "$CP614_LEAN_PATH_FILE" --output "$CP614_AUDIT_DIR"
```

加 `--verify-inputs-only` 核对正式 Main、选中对象和已付来源。
