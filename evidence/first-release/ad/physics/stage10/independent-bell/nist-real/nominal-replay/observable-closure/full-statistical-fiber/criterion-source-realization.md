# cs0001：正规协方差坐标的原生光学源生成

完整训练CI已经支付z>0的正规图谱。基本输入只有(m,z,x,r,e)及
m≥0、m²≥z²+x²、z>0、r>0、0<e≤min(1,r)。
输入不携带finished RawSource/Snapshot、角度存在见证、观察概率、coverage或读回等式。
原PF/TC与旧EF源law、sourceclass和冻结输出保持。

## 正向生成

R=√(z²+x²)，delta=arctan(x/z)/2。
从z>0内部生成R>0和cos(2delta)=z/R、sin(2delta)=x/R。
PSD与m≥0内部生成R≤m，随后生成
nH=(m+R)/e、nV=(m-R)/e、etaA=e、etaB=e/r。
全部RawSource物理字段由这些公式与原始不等式证明；不要求nV>0。

生成的baseline精确读回(m,z,x,r,e)，并读回原T2。
原始相位条件k²≤(m²-z²-x²)((m+e)²-z²-x²)
内部转为PF的合法physical k；PF再生成lambda和同一完整Snapshot。
该生成源精确读回原始协方差坐标，并生成全部cell的原Gaussian法则与N5/OR窗口。
T=0时完整合法lambda的读出等价由既有PF消费，pure-mode保留。

## 图谱与消费者

消费者直接消费原始tuple生成的源，不接收独立source endpoint。
全部角的actual local means读回m-z cos(2a)-x sin(2a)，Bob除以同一r；
两个mirror training局部区间的完整membership与原始tuple的八个halfspaces相接。
全部cell、共享phase与N5的直接consumer必须引用同一个生成源。

这是z>0正规图谱的全部合法原始tuple→实际RawSource/phase source producer。
不扩张到z=0退化轴，不自动识别实际仪器epoch或硬件。
一般无限Born/determinant与原统计事件的内核责任保持原范围。

## 验收

合同/来源先提交，candidate与每次修复先commit后compile。
focused trust0/werror验证直接依赖及两个candidate；fresh certify检查target-free原始字段、
内部arctan轴、pure-mode、精确读回和同一源的直接consumer，只接受标准三公理。
原positiveSmoothUnifiedSource、SpinPair.visit10、whole-ledger与tick16→17保持。
新science实现、AST与数值输出不进入证明构造。

<!-- COVARIANCE-SOURCE-FROZEN-BEGIN -->
```json
{
  "version": "p23-covariance-source-realization-cs0001",
  "status": "frozen_before_compilation",
  "primitive_coordinates": ["m", "z", "x", "r", "e"],
  "physical_domain": "m>=0,m*m>=z*z+x*x,z>0,r>0,0<e<=min(1,r)",
  "axis_recipe": "delta=arctan(x/z)/2",
  "caller_angle_witness": false,
  "caller_source_endpoint": false,
  "pure_mode_preserved": true,
  "all_legal_regular_coordinate_tuples_generate_source": true,
  "same_tuple_readback": true,
  "source_generated_phase_and_N5": true,
  "z_zero_chart_claim": false,
  "new_full_Born_kernel_claim": false,
  "new_statistical_coverage_kernel_claim": false,
  "actual_hardware_identity": false,
  "controller_advance": false
}
```
<!-- COVARIANCE-SOURCE-FROZEN-END -->
