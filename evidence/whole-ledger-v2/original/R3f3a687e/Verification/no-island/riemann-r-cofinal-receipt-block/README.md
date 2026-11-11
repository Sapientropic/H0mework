# 原 Γ Step 整段的次包回执

原 paid trace 的 relation Steps 按原位置进入 Feed。每一项先生成自己的请求和完整执行回执，之后才合计带符号的关系词。通用构造给出实际写入库存中连续的整块。

实际消费者使用同一个原 source-price method，把整块读到 `update+3` 的字面次包，并证明其带符号总词等于旧 `nextBoundary`。原 Joint completion、whole 收据和 literal next 一起由该 method 消费。

独证检查 77 个新原体、54 个 private 声明、800 个编译器额外名及 40 条值体绑定。两步测试使用真实 `add (var ()) (const 1)` 执行。中间 AST 的两个请求分别在父位置 1 和 2，各支付一步，即使两个带符号的回执词相加为零。提前合计关系词会使两个请求消失。

复验默认读取工作树中的两枚正式源码，并使用固定的完整对象视图。

    python3 Verification/no-island/riemann-r-cofinal-receipt-block/certify.py \
      --repo "$PWD" --compiled-root "$CP521_COMPILED_ROOT" \
      --base-lean-path-file "$CP521_LEAN_PATH_FILE" --output "$CP521_AUDIT_DIR"

加 `--verify-inputs-only` 执行零 Lean 输入核验。已有通过的独立原体报告时，`--resume-audit REPORT_SHA256` 保留该次检查。
