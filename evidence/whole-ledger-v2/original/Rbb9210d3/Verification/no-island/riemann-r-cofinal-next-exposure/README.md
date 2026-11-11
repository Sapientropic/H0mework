# 原 cofinal 后继的完整请求收据

CP514 从原库存中实际发生的关系选取支持项。通用 Feed 沿原请求的精确分割取得整个执行 exposure。请求位置按源事件计，支持项按原作用词的有限列表计，exposure 偏移按已执行前缀计。内部原子的位置为 exposure 起点加 1 再加该原子的下标。

实际 Γ born 原子和原接收端 decoder 接入字面后继 site (update+3)。完整收据保留 stock、decoder、paid Trace 及其两个位置。收据边界进入该 site 的原 Joint 与 cochain completion。一次内核应用使用同一个 canonical 方法，联结原 born 原子、两个位置、实际后继 completion 和 CP506 的原 whole/THIS-next。

135 个数学原体、66 个 private 声明、638 个编译器额外名和 68 个值体引用已核验。两个字面相同的计算在一份真实 Feed 中请求位置分别为 0、1，完整 exposure 偏移分别为 2、4。反控核验同值错位与当前包冒充下一包。

复验使用完整 compiled overlay 的 LEAN_PATH，默认读取仓库 Main 源。

    python3 Verification/no-island/riemann-r-cofinal-next-exposure/certify.py \
      --repo "$PWD" --compiled-root "$CP514_COMPILED_ROOT" \
      --base-lean-path-file "$CP514_LEAN_PATH_FILE" --output "$CP514_AUDIT_DIR"

加 --verify-inputs-only 可用零 Lean 核验当前源和四个已付项目父。晋升前可指定 --source-root。已有成功报告时用 --resume-audit REPORT_SHA256 复用本关原体检查。
