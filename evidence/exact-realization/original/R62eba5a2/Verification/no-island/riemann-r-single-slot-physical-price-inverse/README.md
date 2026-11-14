# 原物理单槽价格恢复完整二阶库存

原 comb 在单位位置隙内没有正整数通道，原 R 的向内 dilation 保持位置隙。原 ambient 物理投影在这个偶场库存上单射。原 Xi 首系数使每一拍的实际物理槽非零，支付严格 Γ² 对角能量与非零独立原 K 价格。

原物理投影的真伴随经过两层闭图的正交投影，生成独立 K 的库存协向量。同一当前槽的有限价格经有向 Gram 逆，在完整二阶图范数中收敛到原当前库存。沿原 R 写回，同一批输入恢复字面下一库存。验收在同一发生读取原关系、整账和 native next，并排除任意实际槽的全体原 K 价格归零。

```sh
python3 Verification/no-island/riemann-r-single-slot-physical-price-inverse/certify.py \
  --repo "$PWD" --compiled-root "$CP577_COMPILED_ROOT" \
  --base-lean-path-file "$CP577_LEAN_PATH_FILE" --output "$CP577_AUDIT_DIR"
```

加 `--verify-inputs-only` 核对正式 Main 源码、所选对象和已付父证据。
