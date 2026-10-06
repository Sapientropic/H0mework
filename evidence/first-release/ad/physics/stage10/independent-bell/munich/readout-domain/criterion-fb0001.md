# fb0001：完整等概率纤维的硬件范围

本合同消费id0001已认证的regular纤维，在两枚原joint相容证人的完整同law参数域上，
生成八枚canonical gain与e0/e1范围。四个正负尺度分支全部覆盖；canonical代表沿原effect
生成，不替实际仪器选择ideal标签。固定law范围与整个经验置信域的外包各自保持口径。

## 载荷与完整连续域

输入为原`primitive-witness-c0002.json`，源、原序试次、概率、统计函数及预算保持。
不打开事件、生成新统计量或重拟合经验数据。对Alice，坐标为S=s²,T=t²；对Bob，
坐标为U=1/S,V=1/T。每侧两setting的gain²在对应坐标中为线性函数。

令同侧两cone系数为(a_i,b_i,c_i)=(u_i²,z_i²,(1-|mu_i|)²)，
对侧为(p_j,q_j,d_j)。完整正平方纤维满足

```text
S,T > 0
a_i S + b_i T <= c_i       (i=0,1)
p_j/S + q_j/T <= d_j       (j=0,1)
```

本生成器要求全部十二系数严格正。完整S投影由四个配对二次不等式及正分母产生，
T由两个reciprocal下界的最大值直接构造，内核证明两向覆盖。

## 整域对偶与可达精度

目标为sigma*(a_k S+b_k T)，最小端sigma=+1，最大端sigma=-1。
theta_i、lambda_j均非负；C=sigma*a_k+sum(theta*a_i)、D同理均非负，
P=sum(lambda*p_j)、Q=sum(lambda*q_j)，K=sum(theta*c_i)+sum(lambda*d_j)。
有理数r、v满足r,v≥0、r²≤CP、v²≤DQ，则整个连续域满足

```text
sigma*gain² >= 2*(r+v)-K
```

内核从原cone和reciprocal AM–GM生成该界。每个界附一枚严格有理数合法(S,T)，
目标与界的gap必须在[0,1/100000000]内。这同时支付覆盖与近可达性；有限点枚举不承担覆盖。
gain由平方根向外包，e0=(1-gain-mu)/2、e1=(1-gain+mu)/2由同一channel运输。

## 候选生成与独立检查

Python3.12.13、numpy2.2.6、scipy1.13.1的SLSQP仅提议几何端点。
起点(1,1)，提议坐标界[1/1024,4]²，解析梯度，ftol=1e-13、maxiter=1000。
active residual<1e-7时NNLS提议对偶权；权重取40bit有理数，坐标取48bit有理数，
依次用2^-40、2^-36、2^-32、2^-28、2^-24、2^-20向(1,1)作凸组合。
最大gain²的对偶权直接取对应自身cone的1，其他0。
平方根用80bit整数下界；每份primal／dual均经精确Fraction检查，失败原样登记。

独立程序从旧primitive直接重建四cone，不import主模型、边界算法或优化器；
整数Newton平方根及Fraction逐项核全部16端点、八组channel范围与源绑定。
kernel消费原id0001完整纤维与一般连续域界；旧统计prefix由同law恒等继承。

## 冻结与签收

科学程序、合同、一般证明及独立证书先提交，再独占生成主／独立首次结果。
首结果及attempt均不能覆盖。最终consumer只消费冻结证书，不调用优化器或事件解析器。
readiness签收`complete_fixed_law_hardware_ranges_certified`；唯一实际硬件身份仍由原识别口径承担。
