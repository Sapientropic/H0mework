# 原 R 外场的增量检验向量

新增列在旧张成空间之外的正交余量生成新检验向量。每个旧检验向量按与新增列的配对更新。对任意完整场，新坐标给出新增列的系数，旧求解器消费扣除该列后的余量，恢复其余全部坐标。

原外场自作用给出字面新增列，原列独立性保证其创新非零。原 D 的字面外槽经同一增量读口保持原价格。W 的实际写出场在下一相给出原固定双端残差的两倍作为新增系数，并给出外场范数下界。独证还直接消费 W 自身的来源发生、born 关系、整账和规范后继。

非正交反控取旧列 e₀、新列 e₀+e₁，并以新列作完整输入。旧求解器直接读取完整场给出 1。实际新系数为 1，扣列后旧读数和完整 Gram 对应坐标均为 0。

四正一反通过，53 个新逻辑声明逐项内核复验，含 30 个私有声明。来源核验覆盖 444 项项目依赖和 57 项 Mathlib 依赖，W 与 Reg 的 10 个旧声明沿 CP774 的已签完整 ConstantInfo 及传递公理证据复用。

```sh
python3 Verification/no-island/riemann-r-outside-incremental-cotest/certify.py --repo "$PWD" --compiled-root "$CP775_COMPILED_ROOT" --base-lean-path-file "$CP775_LEAN_PATH_FILE" --output "$CP775_AUDIT_DIR"
```

加 `--verify-inputs-only` 核对正式 Main、选中对象和来源。
