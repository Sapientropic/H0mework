# 《战争与和平的源生终局定理》本地验收

PE1–PE33 的公开选集收于 Homework `cf880bb282f0ff28d6e9f9fc890341baaa8b0eb0`。六个证明包按各自原截面构建，共覆盖 2,076 个独立证明 owner，其中 872 个新增。8,947 个按截面计的 Lean 源码身份和 86 个资源身份均通过原字节恢复。早期战争临界、防卫、追偿、止战和应急期限直接复用已有的公开证明。[固定选集](../checks/enforceable-peace-selection.json) · [来源与消费者](enforceable-peace-map.json) · [复现](enforceable-peace-reproduction.md)

六包在 Darwin 上通过构建和 `--trust=0` 审计，1,396 个声明的完整类型均由内核复核。依赖公理为 `propext`、`Classical.choice` 和 `Quot.sound`，`unsafe = 0`、`partial = 0`。原聚焦验收和原四机签认各自按来源登记。固定证据、首发入口及原社会著作补集的验收也通过。[构建](../evidence/enforceable-peace/acceptance/build.json.gz) · [信任](../evidence/enforceable-peace/acceptance/trust.json.gz) · [完整类型](../evidence/enforceable-peace/acceptance/declaration-types.json.gz) · [本地检查](../evidence/enforceable-peace/acceptance/local-verification.json)

原认证账本的 27 笔签名通过核验，公开 Lean 后端逐笔到达同一钟 28 账头，原债地址与零余额一致。独立夹具验证完全不相交的两届冷恢复及有序处置，批量与逐步入口的 13 个观察一致。早期两项临时适配器只留原 SHA-256，线上结果以原回执和签名账本为据。[离线复演回执](../evidence/enforceable-peace/acceptance/offline-replay.json)

## 缓存保全

原提交 `d1b19e5004b60dc5086e1b41bceee75c2fba98a1` 的远端运行全绿，80 片的完整 Linux 存档均已核对。迁入后，旧 80 片的 modules、targets、upstream、fingerprint 和完整键逐片相同。新增内容分配到 `s10-15`（382 个模块）、`s11-02`（465 个）和 `s11-03`（31 个）。默认覆盖通过，Bell 和量子载体沿原成功工件复用。新选集已有本地验收，远端验收待正式 CI。[原提交运行](https://github.com/Sapientropic/H0mework/actions/runs/42620486915) · [逐片比较及完整计划](../evidence/enforceable-peace/acceptance/cache-preservation.json)
