# 原素数幂挠塔的相干提升与 Kummer 读数

原连接映射与素数倍乘给出的相邻层限制交换。在环境可除以该素数时，对已有下层余核类与相容的上层源类，原环境挠元的提升可以修正两者的差，得到同时满足下层限制和上层读数的余核类。由这些相容纤维，每个原相干源类都有一个相干余核提升。

同一有理椭圆曲线的原几何除法给出上述可除性。独立控制将一个实际有理点送入原相干源，取得同一余核提升，再用它的每层限制认回原 Kummer 类。既有原 R 的关系整账和字面下一拍也通过直接消费核对。

反控使用可除以 2 的环境 ℚ×(ℚ/ℤ)。上层零类读数正确，却不能限制到指定的非零下层挠类，使用环境挠元修正后两项同时成立。四正一反与 36 个逻辑声明的内核复验通过，其中 13 个私有声明。精确核对 264 项项目绑定、15 项 Mathlib 绑定与既有 29 项 Kummer 模块首命中。

```sh
python3 Verification/no-island/cofinal-torsion-kummer-completion/certify.py --repo "$PWD" --compiled-root "$CP741_COMPILED_ROOT" --base-lean-path-file "$CP741_LEAN_PATH_FILE" --output "$CP741_AUDIT_DIR"
```

加 `--verify-inputs-only` 核对正式 Main、选中对象与来源。
