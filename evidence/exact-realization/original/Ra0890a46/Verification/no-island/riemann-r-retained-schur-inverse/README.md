# 原 R 保留价格矩阵的 Schur 更新

同次 advance 发出的旧列、新行和角元组成完整加边矩阵。存储的旧逆给出原已付残差，Schur 分解给出新逆，行列式乘上同一残差。角元取旧块预测值时，同一加边矩阵的行列式为零。

矩阵递推在每个秩保留原记录。同次发出的新旧价格同时进入新矩阵逆和原稀疏逆，并接回 Γ² 图、关系库存、整账与字面下一拍。

```sh
python3 Verification/no-island/riemann-r-retained-schur-inverse/certify.py --repo "$PWD" --compiled-root "$CP602_COMPILED_ROOT" --base-lean-path-file "$CP602_LEAN_PATH_FILE" --output "$CP602_AUDIT_DIR"
```

加 `--verify-inputs-only` 核对正式 Main、选中对象及 CP601、CP476 和固定 Mathlib 输入。
