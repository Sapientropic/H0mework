# 从原已付前缀继续采集

通用历史续跑读取已存状态与尾段，仅在存储末态启动缺失后缀。生成 C 核验递归分支把同一已存状态与旧尾传下去，唯一的 runFrom 取得存储末态。

原调度运行延伸至准备长度，新生 actor 在每个旧采样格都有完整材料与依赖身份。旧付费拟合给出第二段长度，续跑保留原历史和准备历史。选中格读回原完整令牌，接回原整账、下一拍与双库存写回。

```sh
python3 Verification/no-island/riemann-r-paid-prefix-continuation/certify.py --repo "$PWD" --compiled-root "$CP596_COMPILED_ROOT" --base-lean-path-file "$CP596_LEAN_PATH_FILE" --output "$CP596_AUDIT_DIR"
```

加 `--verify-inputs-only` 核对正式 Main 源码、所选对象、已付父证据与生成 C。
