# Goldbach 原存储历史的材料时间表

原历史的存储首态与尾段生成同一张材料表。选中生成 C 以 fuel+1 预分配，每个原存储态投影并追加一次。相邻材料从同一数组的两个位置读取，作用环境取新材料减旧材料。

同一份固定目标读口交付全部原脉冲环境和终态。任意实际阶段可直接消费原 character、cochain 和 lifting-residual 逆像。终态材料进入原两支 disposition，并接回已登记的整账、字面下一拍与良基凭据。绑定前后的两个实际材料格可区分。

```sh
python3 Verification/no-island/goldbach-stored-actor-timeline/certify.py --repo "$PWD" --compiled-root "$CP598_COMPILED_ROOT" --base-lean-path-file "$CP598_LEAN_PATH_FILE" --output "$CP598_AUDIT_DIR"
```

加 `--verify-inputs-only` 核对正式 Main 源码、所选对象、CP597 两项已付证据与选中生成 C。
