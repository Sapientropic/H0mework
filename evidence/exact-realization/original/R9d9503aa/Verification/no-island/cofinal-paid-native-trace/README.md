# 原付费执行的相干词与固定目标终态

原表达式的常数、线性和双线性运算在相干完备化上解释，保留其求值、完整 effect 与剩余步数。每个原付费步骤由它自己的构造子输运。完整轨迹保持长度与每个有序槽，任意形式词也保留原求值和 effect 两个读数。

固定目标 Goldbach 的实际 active tick 将同一个新付费词追加到原轨迹及其相干解释，并读取它的完整 old/effect 对及原作用逆。终态直接消费原收据和处置，读回原执行长度与计算值。独立控制也调用原 Fock 兄弟和依赖作用的同一次整账。

反控删除实际 active tick 的最后一枚付费词，原轨迹和相干轨迹的长度都会改变。四正一反与 57 个逻辑声明的内核复验通过，其中 12 个私有声明。两枚由编译器生成的递归伴生项经独立检查，逻辑声明对它们的引用均为零。核对 281 项项目绑定和 17 项 Mathlib 绑定。

```sh
python3 Verification/no-island/cofinal-paid-native-trace/certify.py --repo "$PWD" --compiled-root "$CP745_COMPILED_ROOT" --base-lean-path-file "$CP745_LEAN_PATH_FILE" --output "$CP745_AUDIT_DIR"
```

加 `--verify-inputs-only` 核对正式 Main、选中对象与来源。
