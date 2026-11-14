# 原 Goldbach 后继的共尾逆读

原整系数后继及其原生反向作用在全截断积、相干逆极限和分离余像上满足左逆律。同一已付 Goldbach 脉冲的实际下一点由原反向作用读回完整当前点，保留原整账和字面 next。

原初始状态的系数读与单点嵌入给出完整分解。各素数幂层、相干逆极限和分离余像的后继像恰为初始系数读为零的元素。原反向作用构造这些元素的前驱。原实际初始点的系数为一，所以它在每个素数幂层和相干逆极限中都没有后继前像。

四正一反通过。32 个新声明含 14 个私有声明通过独立内核复验。精确核对 225 项项目绑定及 11 项 Mathlib 绑定。

```sh
python3 Verification/no-island/cofinal-topology-native-inverse/certify.py --repo "$PWD" --compiled-root "$CP731_COMPILED_ROOT" --base-lean-path-file "$CP731_LEAN_PATH_FILE" --output "$CP731_AUDIT_DIR"
```

加 `--verify-inputs-only` 核正式 Main、选中对象与来源。
