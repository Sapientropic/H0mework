# 原源封口的成功八字节／完整错误 codec 认证

签收 `b8de2ba34d`：私有 Seal 由 `at400` 直接消费原 private GeneratedAt，内部检查 visit4／NN400／physics4000、实际 physical word 与原 layout 均为8 bytes。真实 source parser／clock 已生成的地址界推出 `stateBound<2^56`、`visit×256<2^64`，未输入 caller-bound、Snapshot／target-after、normalizer 或未来 key 特征。

成功采用总8 bytes little-endian visit×256，最低 byte 0为tag；错误采用tag1＋完整变长UTF8。`parse_encode`／`encode_parse`／`encode_injective` 双向规范及无别名成立，空String、Unicode与NUL完整保留，success_size恰8。parser拒收错误长度／未注册tag／无效UTF8／越界或非规范 bytes；并不将任意语法合法key冒认为该Source发生。

`restoreKey` 成功分支从同source、installed及实际Anchor按需执行原自主前缀，经过原生成器／Current parser／三clock，核自身生成Key与输入相同才接受。错误只消费私有 past ErrorCache；ErrorEntry 由自身 `fromAddress` 真正失败产生，保留address／why／generated等式，没有Snapshot、after、未来表或外给成员proof。`saveAddress` 一次自产自身源发生与error-entry，`restore_saveAddress` 及四字母任意word下全部69原读者恢复精确。

`savePublished` 直接消费同 Ready／原 PublishedAt 内已经发生的完整 next，只序列化其自己生成的key，保存不执行第二次F；`restore_savedPublished`、`savedPublished_same_image`（69）与 `savedPublished_whole_six`（原actual destination）同口保持，savedPublished_size恰8。`serialized_minimum_future_kernel` 给出byte相等当且仅当原全部四字母未来词／69读者相等。

3模块fresh trust0/werror、10个直接合同、34个完整type/value依赖闭包全部EXIT0，仅标准Lean三公理，无project axiom／unsafe／sorry／Controls依赖。认证Source／Graph／NN／physics／新epoch500发生均为0。真实写盘、cold decoder执行与资源收益由实际consumer凭据支付；此证书不将静态交换方程充作这些测量。

检查器：[codec完整kernel验收](check_c3_native_key_codec_kernel.py)。证据：[独立摘要](c3-native-key-codec-kernel-summary.json)。权威口：`C3NativeCodec.at400/parse_encode/encode_parse/restore_origin/restore_saveAddress/saved_all_future_readers/savePublished/restore_savedPublished/savedPublished_same_image/savedPublished_whole_six/serialized_minimum_future_kernel/savedPublished_size`。
