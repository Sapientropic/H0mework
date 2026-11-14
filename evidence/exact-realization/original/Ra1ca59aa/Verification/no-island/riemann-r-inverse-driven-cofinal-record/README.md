# 原 R 的旧逆驱动逐轮记录

上一轮的原矩阵逆作用于保留的实际新生旧列，给出旧拟合。原旧地址生成 cutoff，拟合生成搜索 fuel，搜索结果给出完整下一条记录。新地址严格晚于所有旧地址。

同次发出的行列驱动 Schur 逆和行列式更新。更新后的逆与原稀疏解码器都读取这次发出的新旧价格。写回保原 Γ² 图、关系库存、整账和下一拍。

```sh
python3 Verification/no-island/riemann-r-inverse-driven-cofinal-record/certify.py --repo "$PWD" --compiled-root "$CP603_COMPILED_ROOT" --base-lean-path-file "$CP603_LEAN_PATH_FILE" --output "$CP603_AUDIT_DIR"
```

加 `--verify-inputs-only` 核对正式 Main、选中对象与已付 CP602 证据。
