# 原已付 Step 的依赖切口

CP528 从原固定目标 Goldbach pair 库存中的实际 `RelationOccurrence` 读回出生地址和原 Step 下标。切口给出原端点处的前段、Step 和后段，拼合得到同一条完整 typed Trace。关系词由选中的 Step 原样读回。真实 generator 锚的绝对位置为零，关系发生的地址从各出生段内的 (1+j) 开始。

独立验收从同一 later inventory 取两次真实出生的任意各一个原 Step，核对出生、下标、Trace 拼合与关系词。反控在这份库存中排除 generator 锚的关系地址。142 个新数学原体在已付 CP397 Step 与 CP527 Coverage 上逐项复验。两枚编译器递归伴随声明各只有一条自引用边。

从仓库根传入完整编译视图及其有序 Lean 路径。

```sh
python3 Verification/no-island/paid-step-dependent-cut/certify.py \
  --repo "$PWD" --compiled-root "$CP528_COMPILED_ROOT" \
  --base-lean-path-file "$CP528_LEAN_PATH_FILE" --output "$CP528_AUDIT_DIR"
```

加 `--verify-inputs-only` 核验正式源码、选中对象和已付父证据，调用 0 次 Lean。
