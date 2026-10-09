import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiNativeMatchedSource
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceElectricColumns
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceGaugeRadiusMetric
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusAcceleration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiMatchedElectricSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarVirialBulk SourcePhysicalKineticSquare
open SourcePhysicalHamiltonianSquare SourceGaugeRadius SourceGaugeRadiusMetric SourceGaugeRadialCurrent SourceGaugeRadialPair
open GaussQuantumMultiplier
open SourceQuantumResidualGaugeSlice
open SourceElectricColumns SourceCornerWeight SourceClockPhiNativeMatchedSource
open SourceClockAcceleration SourceClockPhiRadiusAcceleration SourceClockPhiCombinedScalePressure
open SourceClockPhiNormalizedScalarBudget SourceClockPhiRadiusResponsePositiveSource
open GaussCoframeForm SourceScalarPositiveBulkWard SourceClockReflectedForm
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open scoped ContDiff InnerProductSpace RealInnerProductSpace Topology
abbrev End:=QuantumTest →ₗ[ℂ] QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev H0:End:=diagonalAction
private abbrev Ggen:End:=SourceGaugeScaleTransport.generator
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction compressionCore defectAction

def electricWeight(z:SourceCoordinateSlice):ℝ:=reciprocalVolume z*SourceGaugeRadiusMetric.electricSquare z
private theorem electric_smooth(z:physicalChart):ContDiffAt ℝ ∞ electricWeight z.val:=
  (reciprocal_volume_smooth z).mul (SourceGaugeRadialCurrent.electric_square_smooth z)
def electricAction:End:=multiply electricWeight electric_smooth

def coframeElectricCurrent:End:=(1/2:ℂ) • bracket GaussCoframeForm.coframeAction electricAction
def fullElectricCurrent:End:=(1/2:ℂ) • bracket H0 electricAction

private theorem electric_formula(z:SourceCoordinateSlice):electricWeight z=
    n/(sourceSigma*(volume z)^2)*gaugeSquare z := by
  unfold electricWeight SourceGaugeRadiusMetric.electricSquare reciprocalVolume
  ring
private theorem real_multiply(c:SourceCoordinateSlice → ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:QuantumTest):
    (multiply c hc f:SourceCoordinateSlice → FockFiber)=(fun z=>c z • f z) := by
  funext z;apply PiLp.ext;intro word
  exact Complex.real_smul.symm
private theorem real_commute(c d:SourceCoordinateSlice → ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val):
    Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_sum_r{ι:Type*}[Fintype ι](f:QuantumTest)(v:ι → QuantumTest):
    sourcePair f (∑i,v i)=∑i,sourcePair f (v i) := by
  simp only [sourcePair,map_sum,inner_sum]
private theorem pair_sum_l{ι:Type*}[Fintype ι](v:ι → QuantumTest)(f:QuantumTest):
    sourcePair (∑i,v i) f=∑i,sourcePair (v i) f := by
  simp only [sourcePair,map_sum,sum_inner]

private theorem electric_pair(f g:QuantumTest):sourcePair f (electricAction g)=sourcePair (electricAction f) g:=
  multiply_pair _ _ _ _
private theorem weight_pair(f g:QuantumTest):sourcePair f (U g)=sourcePair (U f) g:=multiply_pair _ _ _ _
private theorem pair_neg_l(f g:QuantumTest):sourcePair (-f) g= -sourcePair f g:=by
  simp only [sourcePair,map_neg,inner_neg_left]
private theorem ambient_square_smooth(q:Coframe):ContDiff ℝ ∞ (ambientGaugeSquare q):=by
  unfold ambientGaugeSquare
  exact ContDiff.sum (fun i _=>(gaugeRowMap q i).contDiff.inner ℝ (gaugeRowMap q i).contDiff)
private theorem native_electric_derivative(z:physicalChart)(v:Ambient):
    fderiv ℝ electricWeight z.val (direction v z.val)=
      n/(sourceSigma*(volume z.val)^2)*inner ℝ (gaugeGradient z.val) v.2 := by
  let d:=direction v z.val
  let av:Gauge:=((inverseL z.val v).2.2:Gauge)
  have hc:HasDerivAt (fun t:ℝ=>z.val+t • d) d 0:=by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0:ℝ)).smul_const d).const_add z.val
  have he:HasDerivAt (fun t:ℝ=>electricWeight (z.val+t • d))
      (fderiv ℝ electricWeight z.val d) 0:=by
    have h:=((electric_smooth z).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by simp)
    simpa only [zero_smul,add_zero,Function.comp_def] using! h
  have hcurve:(fun t:ℝ=>electricWeight (z.val+t • d))=
      fun t:ℝ=>n/(sourceSigma*(volume z.val)^2)*
        ambientGaugeSquare z.val.1 ((z.val.2.2:Gauge)+t • av) := by
    funext t
    rw [electric_formula,←gauge_square_ambient]
    change n/(sourceSigma*(volume (z.val+t • direction v z.val))^2)*
      ambientGaugeSquare (z.val+t • direction v z.val).1 ((z.val+t • direction v z.val).2.2:Gauge)=_
    simp only [direction,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero,Prod.snd_add,Prod.smul_snd]
    simp only [volume,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero]
    rfl
  have ha:HasDerivAt (fun t:ℝ=>(z.val.2.2:Gauge)+t • av) av 0:=by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0:ℝ)).smul_const av).const_add (z.val.2.2:Gauge)
  have hs:HasDerivAt (fun t:ℝ=>ambientGaugeSquare z.val.1 ((z.val.2.2:Gauge)+t • av))
      (inner ℝ (gaugeGradient z.val) av) 0:=by
    have h:=((ambient_square_smooth z.val.1).differentiable (by simp)).differentiableAt (x:=(z.val.2.2:Gauge))
    have h':=h.hasFDerivAt.comp_hasDerivAt_of_eq 0 ha (by simp)
    simpa only [zero_smul,add_zero,gauge_square_derivative,Function.comp_def] using! h'
  rw [hcurve] at he
  have hh:=he.unique (hs.const_mul (n/(sourceSigma*(volume z.val)^2)))
  change fderiv ℝ electricWeight z.val d= _ at hh
  rw [hh,SourceGaugeRadius.inverse_gauge_gradient z v]

private theorem native_multiplier_jet(c b:SourceCoordinateSlice → ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (v:Ambient)(hd:∀z:physicalChart,fderiv ℝ c z.val (direction v z.val)=b z.val):
    bracket (covariantMomentum v) (multiply c hc)=(-Complex.I) • multiply b hb := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · have he:directional v (multiply c hc f) z=c z • directional v f z+b z • f z := by
      rw [directional_apply,real_multiply,
        fderiv_fun_smul ((hc ⟨z,hz⟩).differentiableAt (by simp))
          (f.contDiff.differentiable (by simp)).differentiableAt]
      change c z • fderiv ℝ f z (direction v z)+fderiv ℝ c z (direction v z) • f z=_
      rw [hd ⟨z,hz⟩]
      rfl
    change (-Complex.I) • (directional v (multiply c hc f) z+
      connection v z ((c z:ℂ) • f z))-(c z:ℂ) •
      ((-Complex.I) • (directional v f z+connection v z (f z)))=(-Complex.I) • ((b z:ℂ) • f z)
    rw [he,map_smul]
    apply PiLp.ext;intro word
    simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,Complex.real_smul,smul_eq_mul]
    ring
  · have hl:bracket (covariantMomentum v) (multiply c hc) f z=0:=
      image_eq_zero_of_notMem_tsupport (fun h=>hz ((bracket (covariantMomentum v) (multiply c hc) f).tsupport_subset h))
    have hr:((-Complex.I) • multiply b hb) f z=0:=by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hz ((((-Complex.I) • multiply b hb) f).tsupport_subset h)
    exact hl.trans hr.symm

private def electricColumnWeight(i:Fin 3)(b:LieIndex)(z:SourceCoordinateSlice):ℝ:=
  2*electricWeight z*logCoefficient i b z
private theorem electric_column_smooth(i:Fin 3)(b:LieIndex)(z:physicalChart):
    ContDiffAt ℝ ∞ (electricColumnWeight i b) z.val:=
  (contDiffAt_const.mul (electric_smooth z)).mul (log_coefficient_smooth i b z)
private def electricColumn(i:Fin 3)(b:LieIndex):End:=multiply (electricColumnWeight i b) (electric_column_smooth i b)
private theorem gauge_pair_coordinate(i:Fin 3)(b:LieIndex)(g:Gauge):
    inner ℝ g (gaugeDirection i b).2=inner ℝ (lieBasis b) (gaugeCoordinates g i) := by
  have h:=PiLp.inner_apply (𝕜:=ℝ) g (WithLp.toLp 2 (Pi.single i (lieBasis b)))
  simp only [Pi.single_apply,apply_ite,inner_zero_right,
    Finset.sum_ite_eq',Finset.mem_univ,if_true] at h
  exact h.trans (real_inner_comm (g.ofLp i) (lieBasis b)).symm
private theorem native_electric_column(i:Fin 3)(b:LieIndex)(z:physicalChart):
    fderiv ℝ electricWeight z.val (direction (gaugeDirection i b) z.val)=electricColumnWeight i b z.val := by
  rw [native_electric_derivative,gauge_pair_coordinate]
  unfold electricColumnWeight logCoefficient
  rw [log_gauge_gradient]
  change n/(sourceSigma*(volume z.val)^2)*inner ℝ (lieBasis b) (gaugeCoordinates (gaugeGradient z.val) i)=
    2*electricWeight z.val*inner ℝ (lieBasis b)
      ((radialWeight z.val/2) • gaugeCoordinates (electricGradient z.val) i)
  rw [real_inner_smul_right]
  unfold SourceGaugeRadiusMetric.electricGradient
  change _=2*electricWeight z.val*((radialWeight z.val/2)*
    inner ℝ (lieBasis b) ((n/(sourceSigma*volume z.val)) • gaugeCoordinates (gaugeGradient z.val) i))
  rw [real_inner_smul_right]
  unfold electricWeight radialWeight reciprocalVolume SourceGaugeRadiusMetric.electricSquare
  have hv:volume z.val≠0:=(volume_pos z).ne'
  have he:gaugeSquare z.val≠0:=(SourceGaugeRadialCurrent.gauge_square_pos z).ne'
  field_simp [hv,source_sigma_nonzero,he]
private theorem gauge_jet(i:Fin 3)(b:LieIndex):bracket (covariantMomentum (gaugeDirection i b)) electricAction=
    (-Complex.I) • electricColumn i b :=
  native_multiplier_jet electricWeight (electricColumnWeight i b) electric_smooth (electric_column_smooth i b)
    (gaugeDirection i b) (native_electric_column i b)
private theorem scalar_jet(i:ScalarIndex):bracket (covariantMomentum (scalarDirection i)) electricAction=0 := by
  have h:=native_multiplier_jet electricWeight (fun _=>0) electric_smooth (fun _=>contDiffAt_const)
    (scalarDirection i) (by intro z;rw [native_electric_derivative];simp [scalarDirection])
  have hz:multiply (fun _ :SourceCoordinateSlice=>0) (fun _=>contDiffAt_const)=(0:End):=by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    change (0:ℂ) • f z=0
    exact zero_smul _ _
  rw [hz,smul_zero] at h
  exact h

private theorem adjoint_multiplier_jet(c b:SourceCoordinateSlice → ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (v:Ambient)(hjet:bracket (covariantMomentum v) (multiply c hc)=(-Complex.I) • multiply b hb):
    bracket (GaussMomentumAdjoint.adjoint v) (multiply c hc)=(-Complex.I) • multiply b hb := by
  apply LinearMap.ext;intro g;apply GaussCoreLabel.pair_separates;intro f
  have h:=congrArg (fun q=>sourcePair q g) (LinearMap.congr_fun hjet f)
  change sourcePair (covariantMomentum v (multiply c hc f)-multiply c hc (covariantMomentum v f)) g=
    sourcePair ((-Complex.I) • multiply b hb f) g at h
  rw [pair_sub_l,pair_smul_l] at h
  simp only [star_neg,Complex.star_def,Complex.conj_I,neg_neg] at h
  change sourcePair f (GaussMomentumAdjoint.adjoint v (multiply c hc g)-
    multiply c hc (GaussMomentumAdjoint.adjoint v g))=sourcePair f ((-Complex.I) • multiply b hb g)
  rw [pair_sub_r,pair_smul_r,adjoint_pair,multiply_pair c hc f,
    adjoint_pair,multiply_pair c hc (covariantMomentum v f),multiply_pair b hb f]
  linear_combination (norm:=ring) -h
private theorem gauge_adjoint_jet(i:Fin 3)(b:LieIndex):
    bracket (GaussMomentumAdjoint.adjoint (gaugeDirection i b)) electricAction=(-Complex.I) • electricColumn i b :=
  adjoint_multiplier_jet electricWeight (electricColumnWeight i b) electric_smooth (electric_column_smooth i b)
    (gaugeDirection i b) (gauge_jet i b)
private theorem scalar_adjoint_commute(i:ScalarIndex):Commute (GaussMomentumAdjoint.adjoint (scalarDirection i)) electricAction := by
  apply LinearMap.ext;intro g;apply GaussCoreLabel.pair_separates;intro f
  have hp:=LinearMap.congr_fun (sub_eq_zero.mp (scalar_jet i)) f
  change covariantMomentum (scalarDirection i) (electricAction f)=electricAction (covariantMomentum (scalarDirection i) f) at hp
  change sourcePair f (GaussMomentumAdjoint.adjoint (scalarDirection i) (electricAction g))=
    sourcePair f (electricAction (GaussMomentumAdjoint.adjoint (scalarDirection i) g))
  rw [adjoint_pair,electric_pair,electric_pair,adjoint_pair,hp]
private theorem scalar_commute:Commute scalarKinetic electricAction := by
  have hp(i:ScalarIndex):Commute (covariantMomentum (scalarDirection i)) electricAction:=sub_eq_zero.mp (scalar_jet i)
  have hw:Commute (multiply scalarWeight scalarWeight_smooth) electricAction:=real_commute _ _ _ _
  unfold scalarKinetic
  apply Commute.smul_left
  exact Commute.sum_left _ _ _ (fun i _=>(scalar_adjoint_commute i).mul_left (hw.mul_left (hp i)))
private theorem electric_column_return(i:Fin 3)(b:LieIndex):electricColumn i b=(2:ℂ) • (electricAction*logColumn i b) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change ((2*electricWeight z*logCoefficient i b z:ℝ):ℂ) • f z=
    (2:ℂ) • ((electricWeight z:ℂ) • ((logCoefficient i b z:ℂ) • f z))
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,smul_smul,mul_assoc]
private theorem electric_metric_row(i:Fin 3)(b:LieIndex):
    (∑j:Fin 3,metricColumn i j*electricColumn j b)=(2:ℂ) • (electricAction*radialColumn i b) := by
  have hc(j:Fin 3):Commute (metricColumn i j) electricAction:=real_commute _ _ _ _
  simp only [electric_column_return,mul_smul_comm,←Finset.smul_sum]
  have he(j:Fin 3):metricColumn i j*(electricAction*logColumn j b)=
      electricAction*(metricColumn i j*logColumn j b):=by rw [←mul_assoc,(hc j).eq,mul_assoc]
  simp_rw [he]
  rw [←Finset.mul_sum,metric_log_columns]
private theorem metric_symmetric(i j:Fin 3):metricColumn i j=metricColumn j i:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (gaugeWeight z i j:ℂ) • f z=(gaugeWeight z j i:ℂ) • f z
  rw [gaugeWeight_symmetric]
private theorem electric_metric_left(j:Fin 3)(b:LieIndex):
    (∑i:Fin 3,electricColumn i b*metricColumn i j)=(2:ℂ) • (electricAction*radialColumn j b) := by
  have he(i:Fin 3):electricColumn i b*metricColumn i j=metricColumn j i*electricColumn i b := by
    rw [metric_symmetric]
    exact (real_commute _ _ _ _).eq
  simp_rw [he]
  exact electric_metric_row j b
private theorem electric_radial_weight:electricAction*radialWeightAction=U := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · change (electricWeight z:ℂ) • ((radialWeight z:ℂ) • f z)=(reciprocalVolume z:ℂ) • f z
    rw [smul_smul,←Complex.ofReal_mul]
    congr 2
    unfold electricWeight radialWeight
    rw [mul_assoc,mul_inv_cancel₀ (SourceGaugeRadialCurrent.electric_square_pos ⟨z,hz⟩).ne',mul_one]
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    change (electricWeight z:ℂ) • ((radialWeight z:ℂ) • f z)=(reciprocalVolume z:ℂ) • f z
    rw [hf,smul_zero,smul_zero,smul_zero]
private def gaugeRight:End:=∑b:LieIndex,∑i:Fin 3,∑j:Fin 3,
  electricColumn i b*metricColumn i j*covariantMomentum (gaugeDirection j b)
private def gaugeLeft:End:=∑b:LieIndex,∑i:Fin 3,∑j:Fin 3,
  GaussMomentumAdjoint.adjoint (gaugeDirection i b)*metricColumn i j*electricColumn j b
private theorem right_return:gaugeRight=(-2*Complex.I) • (U*gaugeEulerAction) := by
  have hrow(b:LieIndex):(∑i:Fin 3,∑j:Fin 3,electricColumn i b*metricColumn i j*covariantMomentum (gaugeDirection j b))=
      (2:ℂ) • (electricAction*(∑j:Fin 3,radialColumn j b*covariantMomentum (gaugeDirection j b))) := by
    rw [Finset.sum_comm]
    simp_rw [←Finset.sum_mul,electric_metric_left]
    simp only [smul_mul_assoc,←Finset.smul_sum,mul_assoc,←Finset.mul_sum]
  have hc:(∑b:LieIndex,∑i:Fin 3,radialColumn i b*covariantMomentum (gaugeDirection i b))=
      (-Complex.I) • radialAction := by
    apply LinearMap.ext;intro f
    simpa only [LinearMap.sum_apply,Module.End.mul_apply,LinearMap.smul_apply,SourceElectricColumns.column] using! radial_column_contraction f
  unfold gaugeRight
  simp_rw [hrow]
  rw [←Finset.smul_sum,←Finset.mul_sum,hc]
  simp only [mul_smul_comm,smul_smul,radialAction,←mul_assoc,electric_radial_weight]
  congr 1
  ring
private theorem left_pair(f g:QuantumTest):sourcePair f (gaugeLeft g)=sourcePair (gaugeRight f) g := by
  simp only [gaugeLeft,gaugeRight,LinearMap.sum_apply,Module.End.mul_apply,pair_sum_r,pair_sum_l]
  apply Finset.sum_congr rfl;intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro i _
  have hw(p q:QuantumTest):sourcePair p (metricColumn i j q)=sourcePair (metricColumn i j p) q:=multiply_pair _ _ _ _
  have hd(p q:QuantumTest):sourcePair p (electricColumn j b q)=sourcePair (electricColumn j b p) q:=multiply_pair _ _ _ _
  rw [adjoint_pair,hw,hd]
  congr 1
  change electricColumn j b (metricColumn i j (covariantMomentum (gaugeDirection i b) f))=
    electricColumn j b (metricColumn j i (covariantMomentum (gaugeDirection i b) f))
  rw [metric_symmetric]

private theorem gauge_inverse:Commute Ggen U := by
  have h:=SourceGaugeScaleTransport.generator_commutator U
  rw [SourceScalarInverseBulk.inverse_gauge] at h
  exact sub_eq_zero.mp h
private theorem gauge_pair(f g:QuantumTest):sourcePair f (Ggen g)= -sourcePair (Ggen f) g := by
  have h:=gauge_euler_pair f g
  rw [gauge_euler_transpose] at h
  simp only [pair_sub_l,pair_smul_l,pair_neg_l] at h
  norm_num only [star_ofNat] at h
  unfold Ggen SourceGaugeScaleTransport.generator
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,pair_add_r,pair_add_l,pair_smul_r,pair_smul_l]
  norm_num only [star_ofNat]
  linear_combination (norm:=ring) h
private theorem weighted_gauge_pair(f g:QuantumTest):sourcePair (U (Ggen f)) g= -sourcePair f (U (Ggen g)) := by
  have hc:=LinearMap.congr_fun gauge_inverse.eq g
  change Ggen (U g)=U (Ggen g) at hc
  rw [←weight_pair,←hc,gauge_pair]
  ring
private theorem gauge_flux_return:gaugeLeft+gaugeRight=(-4*Complex.I) • (U*Ggen) := by
  have hr:gaugeRight=(-2*Complex.I) • (U*Ggen)+(36*Complex.I) • U := by
    rw [right_return]
    unfold Ggen SourceGaugeScaleTransport.generator
    simp only [mul_add,mul_smul_comm,mul_one,smul_add,smul_smul]
    module
  apply LinearMap.ext;intro g;apply GaussCoreLabel.pair_separates;intro f
  simp only [LinearMap.add_apply,pair_add_r,LinearMap.smul_apply,Module.End.mul_apply,pair_smul_r]
  rw [left_pair,hr]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,pair_add_l,pair_add_r,
    pair_smul_l,pair_smul_r,weighted_gauge_pair]
  rw [←weight_pair]
  norm_num only [star_mul,star_neg,star_ofNat,Complex.star_def,Complex.conj_I,neg_neg]
  ring
private theorem product_bracket(A B C:End):bracket (A*B) C=A*bracket B C+bracket A C*B := by
  unfold bracket;noncomm_ring
private theorem gauge_sandwich_jet(i j:Fin 3)(b:LieIndex):
    bracket (sandwich (gaugeDirection i b) (gaugeDirection j b)
      (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j)) electricAction=
    (-Complex.I) • (GaussMomentumAdjoint.adjoint (gaugeDirection i b)*metricColumn i j*electricColumn j b+
      electricColumn i b*metricColumn i j*covariantMomentum (gaugeDirection j b)) := by
  have hw:bracket (metricColumn i j) electricAction=0:=(real_commute _ _ _ _).eq |> sub_eq_zero.mpr
  change bracket (GaussMomentumAdjoint.adjoint (gaugeDirection i b)*
    (metricColumn i j*covariantMomentum (gaugeDirection j b))) electricAction=_
  rw [product_bracket,product_bracket,gauge_jet,gauge_adjoint_jet,hw]
  simp only [zero_mul,add_zero,mul_smul_comm,smul_mul_assoc,←smul_add,mul_assoc]
private theorem gauge_current:bracket gaugeKinetic electricAction=(-2:ℂ) • (U*Ggen) := by
  have he:bracket gaugeKinetic electricAction=(-Complex.I/2) • (gaugeLeft+gaugeRight) := by
    calc
      _=(1/2:ℂ) • ∑b:LieIndex,∑i:Fin 3,∑j:Fin 3,
          bracket (sandwich (gaugeDirection i b) (gaugeDirection j b)
            (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j)) electricAction := by
        unfold gaugeKinetic bracket
        simp only [smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum,smul_sub,Finset.sum_sub_distrib]
      _=_ := by
        simp only [gauge_sandwich_jet,←Finset.smul_sum,Finset.sum_add_distrib,smul_smul]
        unfold gaugeLeft gaugeRight
        congr 1
        ring
  rw [he,gauge_flux_return,smul_smul]
  have hi:(-Complex.I/2)*(-4*Complex.I)=(-2:ℂ):=by
    calc _=2*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [hi]
private theorem quantum_real_commute(B:SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (hB:∀z:physicalChart,ContDiffAt ℝ ∞ B z.val):Commute (localMultiplier B hB) electricAction := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change B z ((electricWeight z:ℂ) • f z)=(electricWeight z:ℂ) • B z (f z)
  exact map_smul (B z) _ _
private theorem matter_commute:Commute GaussMatterCore.matterAction electricAction := by
  unfold GaussMatterCore.matterAction
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro b _
  change Commute (localMultiplier _ _) electricAction
  exact quantum_real_commute _ _
private theorem full_electric_current:bracket H0 electricAction=
    (2:ℂ) • coframeElectricCurrent-(2:ℂ) • (U*Ggen) := by
  have hH:H0=scalarKinetic+gaugeKinetic+GaussCoframeForm.coframeAction+
      GaussMatterCore.matterAction+multiply potential potential_smooth := by
    unfold H0 diagonalAction nativeAction
    abel
  have hb(A B:End):bracket (A+B) electricAction=bracket A electricAction+bracket B electricAction := by
    unfold bracket;noncomm_ring
  have hs:bracket scalarKinetic electricAction=0:=sub_eq_zero.mpr scalar_commute.eq
  have hm:bracket GaussMatterCore.matterAction electricAction=0:=sub_eq_zero.mpr matter_commute.eq
  have hp:bracket (multiply potential potential_smooth) electricAction=0:=
    sub_eq_zero.mpr (real_commute _ _ _ _).eq
  rw [hH,hb,hb,hb,hb,hs,hm,hp,gauge_current]
  unfold coframeElectricCurrent
  simp only [smul_smul,zero_add,add_zero]
  module

private abbrev Dc:End:=dilation
private theorem lapse_nonzero:((sourceTime 0:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos.ne')
private theorem inverse_dilation:Dc*U-U*Dc=(2*Complex.I) • U := by
  have h:=congrArg (fun A:End=>(-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (Dc*U-U*Dc))=(-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only [smul_smul] at h
  have hi:(-2*Complex.I/3)*(3*Complex.I/2)=1 := by
    calc _= -(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1
  congr 1
  ring
private def basePrimitive:End:=(2/(n:ℂ)) • phiSquare-(4/(n:ℂ)) • clock
private theorem base_primitive_current:bracket H0 basePrimitive=
    U*SourceScalarAffineScaleTransport.generator+(3*Complex.I) • (Dc*U)+(3:ℂ) • U := by
  have hr:bracket H0 phiSquare=(n/2:ℂ) • (U*SourceScalarAffineScaleTransport.generator):=original_phi_square_current
  have hc:bracket H0 clock=(-Complex.I) • clockCurrent := by
    unfold clockCurrent bracket
    simp only [smul_smul]
    rw [show (-Complex.I)*Complex.I=1 by rw [neg_mul,Complex.I_mul_I];ring,one_smul]
  have h0:bracket H0 basePrimitive=(2/(n:ℂ)) • bracket H0 phiSquare-(4/(n:ℂ)) • bracket H0 clock := by
    unfold basePrimitive bracket
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
    module
  have hn:(n:ℂ)≠0:=lapse_nonzero
  have hs:(2/(n:ℂ))*((n:ℂ)/2)=1 := by field_simp [hn]
  have ht: -(4/(n:ℂ))*((-Complex.I)*(3*(n:ℂ)/8))=3*Complex.I/2 := by field_simp [hn];ring
  have hc0:bracket H0 basePrimitive=U*SourceScalarAffineScaleTransport.generator+
      (3*Complex.I/2) • (U*Dc+Dc*U) := by
    rw [h0,hr,hc,original_clock_current]
    simp only [smul_smul]
    rw [hs,one_smul,sub_eq_add_neg,←neg_smul]
    change U*SourceScalarAffineScaleTransport.generator+
      (-(4/(n:ℂ)*((-Complex.I)*(3*(n:ℂ)/8)))) • (U*Dc+Dc*U)=_
    have ht2: -(4/(n:ℂ)*((-Complex.I)*(3*(n:ℂ)/8)))=3*Complex.I/2 := by
      exact (neg_mul _ _).symm.trans ht
    rw [ht2]
  have hd:U*Dc=Dc*U-(2*Complex.I) • U := by linear_combination (norm:=module) -inverse_dilation
  rw [hc0,hd]
  simp only [smul_add,smul_sub,smul_smul]
  have hi:(3*Complex.I/2)*(2*Complex.I)=(-3:ℂ) := by
    calc _=3*(Complex.I*Complex.I) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [hi]
  module
/-- The unchanged matched forcing tester is one full-H0 primitive and an explicit gauge remainder. -/
private theorem matched_base_primitive:matchedTester=bracket H0 basePrimitive-
    U*(SourceGaugeScaleTransport.generator+(1:End)) := by
  rw [base_primitive_current]
  change U*(SourceScalarAffineScaleTransport.generator-SourceGaugeScaleTransport.generator)+
    (3*Complex.I) • (Dc*U)+(2:ℂ) • U=
    U*SourceScalarAffineScaleTransport.generator+(3*Complex.I) • (Dc*U)+(3:ℂ) • U-
      U*(SourceGaugeScaleTransport.generator+(1:End))
  noncomm_ring
  module

def electricPrimitive:End:=basePrimitive+(1/2:ℂ) • electricAction
private theorem matched_electric_primitive:matchedTester=bracket H0 electricPrimitive-coframeElectricCurrent-U := by
  have he:bracket H0 electricPrimitive=bracket H0 basePrimitive+(1/2:ℂ) • bracket H0 electricAction := by
    unfold electricPrimitive bracket
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,smul_sub]
    module
  rw [he,full_electric_current,matched_base_primitive]
  simp only [smul_sub,smul_smul]
  norm_num
  simp only [mul_add,mul_one]
  module
private theorem matched_compressed_primitive(F:Index):matchedTester=
    bracket (compressionCore F) electricPrimitive+bracket (defectAction F) electricPrimitive-
      coframeElectricCurrent-U := by
  rw [matched_electric_primitive]
  have hH:H0=compressionCore F+defectAction F:=by
    unfold H0 defectAction
    abel
  rw [hH]
  unfold bracket
  noncomm_ring

def electricForcingWord(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  let w:=normalizedState m ell F z hz g
  (sourcePair w ((bracket combinedConjugate (bracket combinedConjugate (compressionCore F))+
    bracket combinedConjugate (bracket combinedConjugate (defectAction F))+
    (2:ℂ) • (U*GaussMatterCore.matterAction)+(8/5:ℂ) • (U*vacuumConstantAction)) w)).re-
    6*(sourcePair (normalizedForcing m ell F z hz g)
      ((bracket (compressionCore F) electricPrimitive+bracket (defectAction F) electricPrimitive-
        coframeElectricCurrent-U) w)).re+
    6*z.re*(sourcePair w (U w)).re+12*n*spinForm (U w)+12*n*densityForm (U w)-
    12*gaugeForm (U w)-12*spatialForm (U w)
private theorem electric_forcing_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    matchedForcingWord m ell F z hz g=electricForcingWord m ell F z hz g := by
  unfold matchedForcingWord electricForcingWord
  rw [matched_compressed_primitive F]

private theorem gradient_smooth (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (i : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun x => fderiv ℝ c x (GaussCoframeCore.coframeDirection i)) z.val :=
  ((hc z).fderiv_right (by simp)).clm_apply contDiffAt_const

private def electricGradientAction (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (i : Fin 6) : End :=
  multiply (fun x => fderiv ℝ c x (GaussCoframeCore.coframeDirection i)) (gradient_smooth c hc i)

private theorem coframe_multiply_current (i : Fin 6) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    GaussCoframeCore.momentum i*multiply c hc-multiply c hc*GaussCoframeCore.momentum i=
      (-Complex.I) • electricGradientAction c hc i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have he : (multiply c hc f : SourceCoordinateSlice → FockFiber)=fun x => c x • f x := by
      funext x
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    change (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (multiply c hc f) z-
      (c z : ℂ) • ((-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f z)=_
    rw [GaussCoframeCore.derivative_apply,GaussCoframeCore.derivative_apply,he,
      fderiv_fun_smul ((hc ⟨z,hz⟩).differentiableAt (by simp)) (f.contDiff.differentiable (by simp)).differentiableAt]
    change (-Complex.I) • (c z • fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+
      fderiv ℝ c z (GaussCoframeCore.coframeDirection i) • f z)-
      (c z : ℂ) • ((-Complex.I) • fderiv ℝ f z (GaussCoframeCore.coframeDirection i))=
        (-Complex.I) • ((fderiv ℝ c z (GaussCoframeCore.coframeDirection i) : ℂ) • f z)
    apply PiLp.ext
    intro word
    simp only [PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,Complex.real_smul]
    ring
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem coframe_adjoint_multiply_current (i : Fin 6) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    GaussCoframeCore.adjoint i*multiply c hc-multiply c hc*GaussCoframeCore.adjoint i=
      (-Complex.I) • electricGradientAction c hc i := by
  apply LinearMap.ext
  intro g
  apply GaussCoreLabel.pair_separates
  intro f
  have h := congrArg (fun A : End => sourcePair (A f) g) (coframe_multiply_current i c hc)
  change sourcePair (GaussCoframeCore.momentum i (multiply c hc f)-multiply c hc (GaussCoframeCore.momentum i f)) g=
    sourcePair ((-Complex.I) • electricGradientAction c hc i f) g at h
  rw [pair_sub_l,pair_smul_l] at h
  simp only [star_neg,Complex.star_def,Complex.conj_I,neg_neg] at h
  change sourcePair (GaussCoframeCore.momentum i (multiply c hc f)) g-
    sourcePair (multiply c hc (GaussCoframeCore.momentum i f)) g=Complex.I*sourcePair (electricGradientAction c hc i f) g at h
  change sourcePair f (GaussCoframeCore.adjoint i (multiply c hc g)-multiply c hc (GaussCoframeCore.adjoint i g))=
    sourcePair f ((-Complex.I) • electricGradientAction c hc i g)
  rw [pair_sub_r,pair_smul_r]
  rw [GaussCoframeKinetic.adjoint_pair,multiply_pair,multiply_pair,GaussCoframeKinetic.adjoint_pair]
  have hg : sourcePair f (electricGradientAction c hc i g)=sourcePair (electricGradientAction c hc i f) g := multiply_pair _ _ _ _
  rw [hg]
  linear_combination -h

private theorem quantum_multiplier_commute (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ (fun x => quantized (A x)) z.val)
    (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (GaussQuantumMultiplier.action A hA) (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (quantized (A z)) (c z : ℂ) (f z)

private theorem product_current {R : Type*} [Ring R] [Algebra ℂ R] (P W Q M CP CQ : R) (c : ℂ)
    (hP : P*M-M*P=c • CP) (hQ : Q*M-M*Q=c • CQ) (hW : Commute W M) :
    (P*(W*Q))*M-M*(P*(W*Q))=c • (P*(W*CQ)+CP*(W*Q)) := by
  calc
    _=P*(W*(Q*M-M*Q))+(P*M-M*P)*(W*Q) := by
      linear_combination (norm := noncomm_ring) P*hW.eq*Q
    _=_ := by rw [hP,hQ,mul_smul_comm,mul_smul_comm,smul_mul_assoc,smul_add]

private def kineticMetricCurrent (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : End :=
  (-Complex.I) • ∑ i : Fin 6,∑ j : Fin 6,
    (GaussCoframeCore.adjoint i*(multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)*
      electricGradientAction c hc j)+electricGradientAction c hc i*
      (multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)*GaussCoframeCore.momentum j))

private theorem kinetic_metric_current (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    GaussCoframeKinetic.kinetic*multiply c hc-multiply c hc*GaussCoframeKinetic.kinetic=kineticMetricCurrent c hc := by
  have h (i j : Fin 6) : GaussCoframeKinetic.term i j*multiply c hc-multiply c hc*GaussCoframeKinetic.term i j=
      (-Complex.I) • (GaussCoframeCore.adjoint i*(multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)*
        electricGradientAction c hc j)+electricGradientAction c hc i*
        (multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)*GaussCoframeCore.momentum j)) :=
    product_current _ _ _ _ _ _ _ (coframe_adjoint_multiply_current i c hc) (coframe_multiply_current j c hc)
      (real_commute _ _ _ _)
  simp only [GaussCoframeKinetic.kinetic,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib,h,←Finset.smul_sum,kineticMetricCurrent]

private def mixedMetricCurrent (i : Fin 6) (a : Fin 7) (d c : SourceCoordinateSlice → ℝ)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : End :=
  (-Complex.I/2 : ℂ) • (GaussCoframeSpin.current a*(multiply d hd*electricGradientAction c hc i)+
    electricGradientAction c hc i*(multiply d hd*GaussCoframeSpin.current a))

private theorem mixed_metric_current (i : Fin 6) (a : Fin 7) (d c : SourceCoordinateSlice → ℝ)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    GaussCoframeForm.mixed i a d hd*multiply c hc-multiply c hc*GaussCoframeForm.mixed i a d hd=mixedMetricCurrent i a d c hd hc := by
  have hS : GaussCoframeSpin.current a*multiply c hc-multiply c hc*GaussCoframeSpin.current a=(-Complex.I) • (0 : End) := by
    have hs : Commute (GaussCoframeSpin.current a) (multiply c hc) :=
      quantum_multiplier_commute (fun _ => GaussCoframeSpin.full a) (fun _ => contDiffAt_const) c hc
    rw [hs.eq,sub_self,smul_zero]
  have h1 := product_current _ _ _ _ _ _ _ hS (coframe_multiply_current i c hc) (real_commute d c hd hc)
  have h2 := product_current _ _ _ _ _ _ _ (coframe_adjoint_multiply_current i c hc) hS (real_commute d c hd hc)
  change ((1/2 : ℂ) • (GaussCoframeSpin.current a*(multiply d hd*GaussCoframeCore.momentum i)+
    GaussCoframeCore.adjoint i*(multiply d hd*GaussCoframeSpin.current a)))*multiply c hc-
    multiply c hc*((1/2 : ℂ) • (GaussCoframeSpin.current a*(multiply d hd*GaussCoframeCore.momentum i)+
    GaussCoframeCore.adjoint i*(multiply d hd*GaussCoframeSpin.current a)))=_
  simp only [smul_mul_assoc,mul_smul_comm,←smul_sub,add_mul,mul_add]
  rw [show (GaussCoframeSpin.current a*(multiply d hd*GaussCoframeCore.momentum i))*multiply c hc+
      (GaussCoframeCore.adjoint i*(multiply d hd*GaussCoframeSpin.current a))*multiply c hc-
      (multiply c hc*(GaussCoframeSpin.current a*(multiply d hd*GaussCoframeCore.momentum i))+
      multiply c hc*(GaussCoframeCore.adjoint i*(multiply d hd*GaussCoframeSpin.current a)))=
      ((GaussCoframeSpin.current a*(multiply d hd*GaussCoframeCore.momentum i))*multiply c hc-
      multiply c hc*(GaussCoframeSpin.current a*(multiply d hd*GaussCoframeCore.momentum i)))+
      ((GaussCoframeCore.adjoint i*(multiply d hd*GaussCoframeSpin.current a))*multiply c hc-
      multiply c hc*(GaussCoframeCore.adjoint i*(multiply d hd*GaussCoframeSpin.current a))) by abel,h1,h2]
  simp only [zero_mul,mul_zero,add_zero,zero_add,←smul_add,smul_smul,mixedMetricCurrent]
  congr 1
  ring

private def rowTangent(i:Fin 6)(z:SourceCoordinateSlice)(j:Fin 3):NativeLie:=
  !![connectionField z 0,0,0;
    0,connectionField z 0,0;
    0,connectionField z 1,0;
    0,0,connectionField z 0;
    0,0,connectionField z 1;
    0,0,connectionField z 2] i j
private def squareGradient(i:Fin 6)(z:SourceCoordinateSlice):ℝ:=
  2*∑j:Fin 3,inner ℝ (gaugeRow z j) (rowTangent i z j)
private theorem connection_coframe_line(z:SourceCoordinateSlice)(i:Fin 6)(t:ℝ)(j:Fin 3):
    connectionField (z+t • GaussCoframeCore.coframeDirection i) j=connectionField z j:=by
  simp only [connectionField,GaussCoframeCore.coframeDirection,Prod.snd_add,Prod.smul_snd,smul_zero,add_zero]
attribute [local irreducible] connectionField
private def threeRow {V:Type*}[AddCommGroup V][Module ℝ V]
    (q:Fin 6 → ℝ)(A:Fin 3 → V)(j:Fin 3):V:=
  ![q 0 • A 0,q 1 • A 0+q 2 • A 1,q 3 • A 0+q 4 • A 1+q 5 • A 2] j
private def threeTangent {V:Type*}[AddCommGroup V][Module ℝ V]
    (A:Fin 3 → V)(i:Fin 6)(j:Fin 3):V:=
  !![A 0,0,0;0,A 0,0;0,A 1,0;0,0,A 0;0,0,A 1;0,0,A 2] i j
private theorem three_row_line{V:Type*}[AddCommGroup V][Module ℝ V]
    (q:Fin 6 → ℝ)(A:Fin 3 → V)(i:Fin 6)(j:Fin 3)(t:ℝ):
    threeRow (fun k=>q k+t*(if i=k then 1 else 0)) A j=threeRow q A j+t • threeTangent A i j:=by
  fin_cases i <;> fin_cases j <;>
    simp [threeRow,threeTangent,add_smul,add_assoc,add_comm,add_left_comm]
private theorem row_line(i:Fin 6)(j:Fin 3)(z:SourceCoordinateSlice)(t:ℝ):
    gaugeRow (z+t • GaussCoframeCore.coframeDirection i) j=
      gaugeRow z j+t • rowTangent i z j := by
  have hq(k:Fin 6):(z+t • GaussCoframeCore.coframeDirection i).1 k=
      z.1 k+t*(if i=k then 1 else 0):=by
    simp [GaussCoframeCore.coframeDirection,EuclideanSpace.single,eq_comm]
  have h:=three_row_line (fun k=>z.1 k) (connectionField z) i j t
  simpa only [threeRow,threeTangent,gaugeRow,connection_coframe_line,hq,rowTangent] using h
private theorem square_line_derivative(z:SourceCoordinateSlice)(i:Fin 6):
    HasDerivAt (fun t:ℝ=>gaugeSquare (z+t • GaussCoframeCore.coframeDirection i)) (squareGradient i z) 0 := by
  have h(j:Fin 3):HasDerivAt (fun t:ℝ=>gaugeRow (z+t • GaussCoframeCore.coframeDirection i) j)
      (rowTangent i z j) 0:=by
    simpa only [row_line,one_smul,id_eq] using!
      ((hasDerivAt_id (0:ℝ)).smul_const (rowTangent i z j)).const_add (gaugeRow z j)
  have hj(j:Fin 3):HasDerivAt
      (fun t:ℝ=>inner ℝ (gaugeRow (z+t • GaussCoframeCore.coframeDirection i) j)
        (gaugeRow (z+t • GaussCoframeCore.coframeDirection i) j))
      (2*inner ℝ (gaugeRow z j) (rowTangent i z j)) 0:=by
    have ht:inner ℝ (gaugeRow z j) (rowTangent i z j)+
        inner ℝ (rowTangent i z j) (gaugeRow z j)=2*inner ℝ (gaugeRow z j) (rowTangent i z j):=by
      rw [real_inner_comm (gaugeRow z j) (rowTangent i z j)]
      ring
    simpa only [zero_smul,add_zero,ht] using! (h j).inner ℝ (h j)
  simpa only [gaugeSquare,squareGradient,Finset.mul_sum,Finset.sum_apply] using!
    (HasDerivAt.sum (u:=Finset.univ) (fun j _=>hj j))
private def electricCoframeGradient(i:Fin 6)(z:SourceCoordinateSlice):ℝ:=
  n/(sourceSigma*(volume z)^3)*(volume z*squareGradient i z-2*gaugeSquare z*volumeGradient z i)
private theorem electric_coframe_derivative(z:physicalChart)(i:Fin 6):
    fderiv ℝ electricWeight z.val (GaussCoframeCore.coframeDirection i)=electricCoframeGradient i z.val := by
  have hl:HasDerivAt (fun t:ℝ=>z.val+t • GaussCoframeCore.coframeDirection i)
      (GaussCoframeCore.coframeDirection i) 0:=by
    simpa only [one_smul,id_eq] using!
      ((hasDerivAt_id (0:ℝ)).smul_const (GaussCoframeCore.coframeDirection i)).const_add z.val
  have hv:=((volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z.val))
    |>.comp_hasDerivAt_of_eq 0 hl (by simp)
  have he:=((electric_smooth z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 hl (by simp)
  have hV:HasDerivAt (fun t:ℝ=>volume (z.val+t • GaussCoframeCore.coframeDirection i))
      (volumeGradient z.val i) 0:=by
    simpa only [Function.comp_def,volume_coordinate_derivative] using! hv
  have hh:=((hasDerivAt_const (0:ℝ) n).div ((hV.pow 2).const_mul sourceSigma)
    (by simpa only [Pi.pow_apply,zero_smul,add_zero] using mul_ne_zero source_sigma_nonzero (pow_ne_zero 2 (volume_pos z).ne'))).mul
      (square_line_derivative z.val i)
  have he':HasDerivAt (fun t:ℝ=>electricWeight (z.val+t • GaussCoframeCore.coframeDirection i))
      (fderiv ℝ electricWeight z.val (GaussCoframeCore.coframeDirection i)) 0:=by
    simpa only [Function.comp_def] using! he
  simp_rw [electric_formula] at he'
  have hd:=he'.unique hh
  simp only [Pi.pow_apply,Pi.div_apply,zero_smul,add_zero,Nat.cast_ofNat,Nat.reduceSub,pow_one] at hd
  rw [hd,electricCoframeGradient]
  field_simp [(volume_pos z).ne',source_sigma_nonzero]
  ring
private def wedgePolynomial(z:SourceCoordinateSlice):ℝ:=
  (gaugeSquare z)^2-∑i:Fin 3,∑j:Fin 3,(inner ℝ (gaugeRow z i) (gaugeRow z j))^2
private theorem wedge_nonnegative(z:SourceCoordinateSlice):0≤wedgePolynomial z := by
  have h:∀i j:Fin 3,(inner ℝ (gaugeRow z i) (gaugeRow z j))^2≤
      inner ℝ (gaugeRow z i) (gaugeRow z i)*inner ℝ (gaugeRow z j) (gaugeRow z j):=by
    intro i j
    simpa only [pow_two] using real_inner_mul_inner_self_le (gaugeRow z i) (gaugeRow z j)
  have hh:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>
    Finset.sum_le_sum (fun j (_:j∈Finset.univ)=>h i j))
  unfold wedgePolynomial
  apply sub_nonneg.mpr
  simpa only [gaugeSquare,pow_two,Finset.sum_mul,Finset.mul_sum,mul_comm] using hh
private def gaugeGram(z:SourceCoordinateSlice)(i j:Fin 3):ℝ:=inner ℝ (connectionField z i) (connectionField z j)
private def squarePoly(q:Coframe)(G:Fin 3 → Fin 3 → ℝ):ℝ:=
  q 0^2*G 0 0+q 1^2*G 0 0+2*q 1*q 2*G 0 1+q 2^2*G 1 1+
  q 3^2*G 0 0+2*q 3*q 4*G 0 1+2*q 3*q 5*G 0 2+q 4^2*G 1 1+2*q 4*q 5*G 1 2+q 5^2*G 2 2
private def gradientPoly(q:Coframe)(G:Fin 3 → Fin 3 → ℝ):Fin 6 → ℝ:=
  ![2*q 0*G 0 0,2*q 1*G 0 0+2*q 2*G 0 1,2*q 1*G 0 1+2*q 2*G 1 1,
    2*q 3*G 0 0+2*q 4*G 0 1+2*q 5*G 0 2,
    2*q 3*G 0 1+2*q 4*G 1 1+2*q 5*G 1 2,
    2*q 3*G 0 2+2*q 4*G 1 2+2*q 5*G 2 2]
private def wedgePoly(q:Coframe)(G:Fin 3 → Fin 3 → ℝ):ℝ:=
  squarePoly q G^2-((q 0^2*G 0 0)^2+
    (q 1^2*G 0 0+2*q 1*q 2*G 0 1+q 2^2*G 1 1)^2+
    (q 3^2*G 0 0+2*q 3*q 4*G 0 1+2*q 3*q 5*G 0 2+q 4^2*G 1 1+2*q 4*q 5*G 1 2+q 5^2*G 2 2)^2+
    2*(q 0*(q 1*G 0 0+q 2*G 0 1))^2+
    2*(q 0*(q 3*G 0 0+q 4*G 0 1+q 5*G 0 2))^2+
    2*(q 1*q 3*G 0 0+(q 1*q 4+q 2*q 3)*G 0 1+q 1*q 5*G 0 2+q 2*q 4*G 1 1+q 2*q 5*G 1 2)^2)
private theorem square_poly(z:SourceCoordinateSlice):gaugeSquare z=squarePoly z.1 (gaugeGram z) := by
  simp only [gaugeSquare,gaugeRow,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm (connectionField z 0) (connectionField z 1),
    real_inner_comm (connectionField z 0) (connectionField z 2),real_inner_comm (connectionField z 1) (connectionField z 2)]
  unfold squarePoly gaugeGram
  ring
private theorem square_gradient_poly(z:SourceCoordinateSlice)(i:Fin 6):squareGradient i z=gradientPoly z.1 (gaugeGram z) i := by
  fin_cases i <;>
    simp [squareGradient,rowTangent,gaugeRow,gradientPoly,gaugeGram,Fin.sum_univ_three,
      inner_add_right,real_inner_smul_right,real_inner_comm] <;> ring
private theorem wedge_poly(z:SourceCoordinateSlice):wedgePolynomial z=wedgePoly z.1 (gaugeGram z) := by
  rw [wedgePolynomial,square_poly]
  simp only [gaugeRow,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm (connectionField z 0) (connectionField z 1),
    real_inner_comm (connectionField z 0) (connectionField z 2),real_inner_comm (connectionField z 1) (connectionField z 2)]
  unfold wedgePoly gaugeGram
  ring
private theorem scalar_contact_polynomial(q:Coframe)(G:Fin 3 → Fin 3 → ℝ):
    (∑i:Fin 6,∑j:Fin 6,((q 0*q 2*q 5)*gradientPoly q G i-2*squarePoly q G*(![q 2*q 5,0,q 0*q 5,0,0,q 0*q 2]:Fin 6 → ℝ) i)*
      (GaussCoframeKinetic.polynomial q i j*((q 0*q 2*q 5)*gradientPoly q G j-2*squarePoly q G*(![q 2*q 5,0,q 0*q 5,0,0,q 0*q 2]:Fin 6 → ℝ) j)))=
      8*(q 0*q 2*q 5)^2*wedgePoly q G := by
  simp [gradientPoly,squarePoly,wedgePoly,GaussCoframeKinetic.polynomial,Fin.sum_univ_succ]
  ring
private theorem coframe_polynomial_electric(z:SourceCoordinateSlice):
    (∑i:Fin 6,∑j:Fin 6,(volume z*squareGradient i z-2*gaugeSquare z*volumeGradient z i)*
      (GaussCoframeKinetic.polynomial z.1 i j*(volume z*squareGradient j z-2*gaugeSquare z*volumeGradient z j)))=
      8*(volume z)^2*wedgePolynomial z := by
  simp only [square_gradient_poly,square_poly,wedge_poly,volume,volumeGradient]
  exact scalar_contact_polynomial z.1 (gaugeGram z)
private def coframeFirst:End:=kineticMetricCurrent electricWeight electric_smooth+
  mixedMetricCurrent 1 5 (GaussCoframeForm.currentCoefficient 0) electricWeight
    (GaussCoframeForm.currentCoefficient_smooth 0) electric_smooth+
  mixedMetricCurrent 3 3 (GaussCoframeForm.currentCoefficient 1) electricWeight
    (GaussCoframeForm.currentCoefficient_smooth 1) electric_smooth+
  mixedMetricCurrent 3 4 (fun z=>-GaussCoframeForm.currentCoefficient 0 z) electricWeight
    (fun z=>(GaussCoframeForm.currentCoefficient_smooth 0 z).neg) electric_smooth+
  mixedMetricCurrent 4 3 (GaussCoframeForm.currentCoefficient 2) electricWeight
    (GaussCoframeForm.currentCoefficient_smooth 2) electric_smooth
private theorem coframe_first:bracket GaussCoframeForm.coframeAction electricAction=coframeFirst := by
  have hs(j:Fin 7):Commute (spinSquare j) electricAction:=by
    change Commute ((spinWeight j:ℂ) • (GaussCoframeSpin.current j*
      (multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*GaussCoframeSpin.current j))) electricAction
    have hJ:Commute (GaussCoframeSpin.current j) electricAction:=quantum_multiplier_commute _ _ _ _
    exact (hJ.mul_left ((real_commute _ _ _ _).mul_left hJ)).smul_left _
  have hn:Commute numberShift electricAction:=by
    change Commute ((1/2:ℂ) • (number*multiply numberCoefficient numberCoefficient_smooth+
      multiply numberCoefficient numberCoefficient_smooth*number)) electricAction
    have hN:Commute number electricAction:=quantum_multiplier_commute _ _ _ _
    have hM:Commute (multiply numberCoefficient numberCoefficient_smooth) electricAction:=real_commute _ _ _ _
    exact ((hN.mul_left hM).add_left (hM.mul_left hN)).smul_left _
  have hvol:Commute (multiply volumePotential volumePotential_smooth) electricAction:=real_commute _ _ _ _
  have hspin:Commute (∑j:Fin 7,spinSquare j) electricAction:=Commute.sum_left _ _ _ (fun j _=>hs j)
  have hk:=kinetic_metric_current electricWeight electric_smooth
  have h1:=mixed_metric_current 1 5 (currentCoefficient 0) electricWeight (currentCoefficient_smooth 0) electric_smooth
  have h2:=mixed_metric_current 3 3 (currentCoefficient 1) electricWeight (currentCoefficient_smooth 1) electric_smooth
  have h3:=mixed_metric_current 3 4 (fun z=>-currentCoefficient 0 z) electricWeight
    (fun z=>(currentCoefficient_smooth 0 z).neg) electric_smooth
  have h4:=mixed_metric_current 4 3 (currentCoefficient 2) electricWeight (currentCoefficient_smooth 2) electric_smooth
  unfold bracket GaussCoframeForm.coframeAction currentAction coframeFirst
  simp only [add_mul,mul_add]
  simp only [electricAction] at hspin hn hvol ⊢
  linear_combination (norm:=module) hk+h1+h2+h3+h4+hspin.eq+hn.eq+hvol.eq
private theorem bracket_sum_l{ι:Type*}[Fintype ι](X:ι → End)(B:End):
    bracket (∑i,X i) B=∑i,bracket (X i) B:=by
  simp only [bracket,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]
private theorem bracket_sum_r{ι:Type*}[Fintype ι](X:ι → End)(B:End):
    bracket B (∑i,X i)=∑i,bracket B (X i):=by
  simp only [bracket,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]
private theorem bracket_smul_r(c:ℂ)(X B:End):bracket B (c • X)=c • bracket B X:=by
  simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem bracket_smul_l(c:ℂ)(X B:End):bracket (c • X) B=c • bracket X B:=by
  simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem electric_adjoint(i:Fin 6):bracket electricAction (GaussCoframeCore.adjoint i)=
    Complex.I • electricGradientAction electricWeight electric_smooth i := by
  have h:=coframe_adjoint_multiply_current i electricWeight electric_smooth
  change GaussCoframeCore.adjoint i*electricAction-electricAction*GaussCoframeCore.adjoint i=_ at h
  unfold bracket
  linear_combination (norm:=module) -h
private theorem electric_momentum(i:Fin 6):bracket electricAction (GaussCoframeCore.momentum i)=
    Complex.I • electricGradientAction electricWeight electric_smooth i := by
  have h:=coframe_multiply_current i electricWeight electric_smooth
  change GaussCoframeCore.momentum i*electricAction-electricAction*GaussCoframeCore.momentum i=_ at h
  unfold bracket
  linear_combination (norm:=module) -h
private theorem electric_gradient_commute(i:Fin 6):
    Commute electricAction (electricGradientAction electricWeight electric_smooth i):=real_commute _ _ _ _
private theorem electric_coefficient_commute(i j:Fin 6):Commute electricAction
    (multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)):=real_commute _ _ _ _
private theorem coframe_double_row(i j:Fin 6):bracket electricAction
    (GaussCoframeCore.adjoint i*(multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)*
      electricGradientAction electricWeight electric_smooth j)+electricGradientAction electricWeight electric_smooth i*
      (multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)*GaussCoframeCore.momentum j))=
    (2*Complex.I) • (electricGradientAction electricWeight electric_smooth i*
      (multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)*
        electricGradientAction electricWeight electric_smooth j)) := by
  have hb(X Y:End):bracket electricAction (X+Y)=bracket electricAction X+bracket electricAction Y:=by
    unfold bracket;noncomm_ring
  have hg(k:Fin 6):bracket electricAction (electricGradientAction electricWeight electric_smooth k)=0:=
    sub_eq_zero.mpr (electric_gradient_commute k).eq
  have hw:bracket electricAction (multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j))=0:=
    sub_eq_zero.mpr (electric_coefficient_commute i j).eq
  rw [hb]
  have hp(X Y:End):bracket electricAction (X*Y)=bracket electricAction X*Y+X*bracket electricAction Y:=by
    unfold bracket;noncomm_ring
  simp only [hp,hg,hw,electric_adjoint,electric_momentum,
    zero_mul,mul_zero,zero_add,add_zero,mul_smul_comm,smul_mul_assoc]
  module
private theorem mixed_current_commute(i:Fin 6)(j:Fin 7)(d:SourceCoordinateSlice → ℝ)
    (hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val):
    Commute electricAction (mixedMetricCurrent i j d electricWeight hd electric_smooth) := by
  have hJ:Commute electricAction (GaussCoframeSpin.current j):=(quantum_multiplier_commute _ _ _ _).symm
  have hd':Commute electricAction (multiply d hd):=real_commute _ _ _ _
  have hg:=electric_gradient_commute i
  exact ((hJ.mul_right (hd'.mul_right hg)).add_right (hg.mul_right (hd'.mul_right hJ))).smul_right _
private def electricContactWeight(z:SourceCoordinateSlice):ℝ:=
  2*∑i:Fin 6,∑j:Fin 6,fderiv ℝ electricWeight z (GaussCoframeCore.coframeDirection i)*
    (GaussCoframeKinetic.coefficient i j z*fderiv ℝ electricWeight z (GaussCoframeCore.coframeDirection j))
private theorem electric_contact_smooth(z:physicalChart):ContDiffAt ℝ ∞ electricContactWeight z.val:=
  contDiffAt_const.mul (ContDiffAt.sum (fun i _=>ContDiffAt.sum (fun j _=>
    (gradient_smooth electricWeight electric_smooth i z).mul
      ((GaussCoframeKinetic.coefficient_smooth i j z).mul (gradient_smooth electricWeight electric_smooth j z)))))
def wedgeAction:End:=multiply electricContactWeight electric_contact_smooth
private theorem coframe_double:bracket electricAction (bracket GaussCoframeForm.coframeAction electricAction)=wedgeAction := by
  rw [coframe_first]
  have hb(X Y:End):bracket electricAction (X+Y)=bracket electricAction X+bracket electricAction Y:=by
    unfold bracket;noncomm_ring
  have hm(i:Fin 6)(j:Fin 7)(d:SourceCoordinateSlice → ℝ)
      (hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val):
      bracket electricAction (mixedMetricCurrent i j d electricWeight hd electric_smooth)=0:=
    sub_eq_zero.mpr (mixed_current_commute i j d hd).eq
  simp only [coframeFirst,hb,hm,add_zero]
  unfold kineticMetricCurrent
  rw [bracket_smul_r]
  simp only [bracket_sum_r,coframe_double_row,←Finset.smul_sum,smul_smul]
  have hi:(-Complex.I)*(2*Complex.I)=(2:ℂ):=by
    calc _= -2*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [hi]
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z;apply PiLp.ext;intro word
  change (2:ℂ)*(∑i:Fin 6,∑j:Fin 6,
    (fderiv ℝ electricWeight z (GaussCoframeCore.coframeDirection i):ℂ)*
      ((GaussCoframeKinetic.coefficient i j z:ℂ)*
        ((fderiv ℝ electricWeight z (GaussCoframeCore.coframeDirection j):ℂ)*f z word)))=
    ((2*∑i:Fin 6,∑j:Fin 6,fderiv ℝ electricWeight z (GaussCoframeCore.coframeDirection i)*
      (GaussCoframeKinetic.coefficient i j z*fderiv ℝ electricWeight z (GaussCoframeCore.coframeDirection j)):ℝ):ℂ)*f z word
  simp only [Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_ofNat,Finset.mul_sum,Finset.sum_mul,mul_assoc]
private theorem electric_contact_formula(z:physicalChart):electricContactWeight z.val=
    4*n^3/(sourceSigma^2*(volume z.val)^5)*wedgePolynomial z.val := by
  unfold electricContactWeight
  simp only [electric_coframe_derivative,electricCoframeGradient,GaussCoframeKinetic.coefficient]
  have hs:(∑i:Fin 6,∑j:Fin 6,
      (n/(sourceSigma*volume z.val^3)*(volume z.val*squareGradient i z.val-2*gaugeSquare z.val*volumeGradient z.val i))*
      (n/(4*volume z.val)*GaussCoframeKinetic.polynomial z.val.1 i j*
        (n/(sourceSigma*volume z.val^3)*(volume z.val*squareGradient j z.val-2*gaugeSquare z.val*volumeGradient z.val j))))=
      n^3/(4*sourceSigma^2*volume z.val^7)*
        ∑i:Fin 6,∑j:Fin 6,(volume z.val*squareGradient i z.val-2*gaugeSquare z.val*volumeGradient z.val i)*
          (GaussCoframeKinetic.polynomial z.val.1 i j*(volume z.val*squareGradient j z.val-2*gaugeSquare z.val*volumeGradient z.val j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _
    ring
  change 2*_= _
  rw [hs,coframe_polynomial_electric]
  field_simp [(volume_pos z).ne',source_sigma_nonzero]
  ring

private theorem connection_coframe_scale(r:ℝ)(z:SourceCoordinateSlice)(i:Fin 3):
    connectionField (SourceCoframeVolume.scale r z) i=connectionField z i:=by
  unfold connectionField SourceCoframeVolume.scale
  rfl
private theorem electric_coframe_scale(r:ℝ)(hr:r≠0)(z:physicalChart):
    electricWeight (SourceCoframeVolume.scale r z.val)=r^(-4:ℤ)*electricWeight z.val := by
  have hrow(i:Fin 3):gaugeRow (SourceCoframeVolume.scale r z.val) i=r • gaugeRow z.val i:=by
    simp only [gaugeRow,connection_coframe_scale]
    fin_cases i <;> simp [SourceCoframeVolume.scale,smul_smul,smul_add]
  have hT:gaugeSquare (SourceCoframeVolume.scale r z.val)=r^2*gaugeSquare z.val:=by
    simp only [gaugeSquare,hrow,real_inner_smul_left,real_inner_smul_right,pow_two,
      Finset.mul_sum,mul_assoc]
  rw [electric_formula,volume_scale,hT,electric_formula]
  simp only [zpow_neg]
  field_simp [hr,(volume_pos z).ne',source_sigma_nonzero]
private theorem electric_dilation:bracket Dc electricAction=(8*Complex.I/3) • electricAction := by
  have hd(z:physicalChart):fderiv ℝ electricWeight z.val (euler z.val)=(-4:ℝ)*electricWeight z.val:=by
    simpa only [Int.cast_neg,Int.cast_ofNat] using SourceKineticScale.euler_of_scale electricWeight (-4) z (electric_smooth z) (fun r hr=>electric_coframe_scale r hr z)
  have h:=SourceDilationMultiplier.homogeneous_multiplier electricWeight electric_smooth (-4) hd
  change bracket Dc electricAction=((-2*Complex.I/3)*((-4:ℝ):ℂ)) • electricAction at h
  convert h using 1
  congr 1
  norm_num
  ring
private theorem electric_gauge_derivative(z:physicalChart):
    fderiv ℝ electricWeight z.val (gaugeEuler z.val)=2*electricWeight z.val := by
  have hc:=((electric_smooth z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (gauge_scale_derivative z.val 1) (gauge_scale_one z.val).symm
  have hs(r:ℝ):electricWeight (gaugeScale r z.val)=r^2*electricWeight z.val:=by
    unfold electricWeight
    rw [electric_square_scale]
    change reciprocalVolume z.val*(r^2*electricSquare z.val)=_
    ring
  have ht:HasDerivAt (fun r:ℝ=>electricWeight (gaugeScale r z.val)) (2*electricWeight z.val) 1:=by
    simpa only [hs,id_eq,Pi.pow_apply,one_pow,mul_one,Nat.cast_ofNat,Nat.reduceSub] using!
      ((hasDerivAt_id (1:ℝ)).pow 2).mul_const (electricWeight z.val)
  exact hc.unique ht
private theorem electric_gauge:bracket Ggen electricAction=(2:ℂ) • electricAction := by
  have h:bracket gaugeEulerAction electricAction=(2:ℂ) • electricAction:=by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    by_cases hz:z∈physicalChart
    · change gaugeEulerAction (electricAction f) z-(electricWeight z:ℂ) • gaugeEulerAction f z=(2:ℂ) • ((electricWeight z:ℂ) • f z)
      rw [gauge_euler_apply]
      change fderiv ℝ (multiply electricWeight electric_smooth f) z (gaugeEuler z)-_=_
      rw [real_multiply,
        fderiv_fun_smul ((electric_smooth ⟨z,hz⟩).differentiableAt (by simp))
          (f.contDiff.differentiable (by simp)).differentiableAt]
      change electricWeight z • fderiv ℝ f z (gaugeEuler z)+
        fderiv ℝ electricWeight z (gaugeEuler z) • f z-(electricWeight z:ℂ) • gaugeEulerAction f z=_
      rw [electric_gauge_derivative ⟨z,hz⟩,gauge_euler_apply]
      apply PiLp.ext;intro word
      simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,Complex.real_smul,smul_eq_mul]
      push_cast
      ring
    · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
      exact (h0 _).trans (h0 _).symm
  unfold Ggen SourceGaugeScaleTransport.generator bracket at *
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  linear_combination (norm:=module) h
private theorem bracket_jacobi(X Y Z:End):
    bracket (bracket X Y) Z=bracket X (bracket Y Z)-bracket Y (bracket X Z):=by
  unfold bracket;noncomm_ring
private theorem bracket_neg(X Y:End):bracket X Y= -bracket Y X:=by
  unfold bracket;noncomm_ring
private theorem electric_weight_commute:Commute electricAction U:=real_commute _ _ _ _
private theorem electric_clock_commute:Commute electricAction clock:=by
  rw [original_clock]
  exact real_commute _ _ _ _
private theorem electric_full_double:bracket electricAction (bracket H0 electricAction)=
    (4:ℂ) • (U*electricAction)+wedgeAction := by
  have hG:bracket electricAction Ggen=(-2:ℂ) • electricAction:=by
    rw [bracket_neg,electric_gauge,neg_smul]
  have hU:bracket electricAction U=0:=sub_eq_zero.mpr electric_weight_commute.eq
  have hcf:bracket electricAction ((2:ℂ) • coframeElectricCurrent)=wedgeAction:=by
    unfold coframeElectricCurrent
    simp only [smul_smul]
    norm_num
    exact coframe_double
  have hs(X Y:End):bracket electricAction (X-Y)=bracket electricAction X-bracket electricAction Y:=by
    unfold bracket;noncomm_ring
  have hp(X Y:End):bracket electricAction (X*Y)=bracket electricAction X*Y+X*bracket electricAction Y:=by
    unfold bracket;noncomm_ring
  rw [full_electric_current,hs,hcf,bracket_smul_r,hp,hU,hG]
  simp only [zero_mul,zero_add,mul_smul_comm,smul_smul]
  module
private theorem current_volume:bracket fullElectricCurrent volumeAction=(n:ℂ) • electricAction := by
  have hv:bracket H0 volumeAction=(-3*Complex.I*(n:ℂ)/4) • Dc:=SourceHamiltonianVolume.full_source_volume_current
  have he:bracket electricAction volumeAction=0:=sub_eq_zero.mpr (real_commute _ _ _ _).eq
  unfold fullElectricCurrent
  rw [bracket_smul_l,bracket_jacobi,he]
  simp only [bracket,mul_zero,zero_mul,sub_self,zero_sub]
  change (1/2:ℂ) • (-(electricAction*bracket H0 volumeAction-bracket H0 volumeAction*electricAction))=_
  rw [hv]
  change (1/2:ℂ) • (-bracket electricAction ((-3*Complex.I*(n:ℂ)/4) • Dc))=_
  rw [bracket_smul_r,bracket_neg,electric_dilation]
  simp only [smul_neg,neg_neg,smul_smul]
  congr 1
  calc _= -n*(Complex.I*Complex.I):=by ring
       _=_:=by rw [Complex.I_mul_I];ring
private theorem current_clock:bracket fullElectricCurrent clock=(n:ℂ) • (U*electricAction) := by
  have hc:bracket H0 clock=(-Complex.I) • clockCurrent:=by
    unfold clockCurrent bracket
    simp only [smul_smul]
    rw [show (-Complex.I)*Complex.I=1 by rw [neg_mul,Complex.I_mul_I];ring,one_smul]
  have he:bracket electricAction clock=0:=sub_eq_zero.mpr electric_clock_commute.eq
  have hU:bracket electricAction U=0:=sub_eq_zero.mpr electric_weight_commute.eq
  have hD:bracket electricAction Dc=(-8*Complex.I/3) • electricAction:=by
    rw [bracket_neg,electric_dilation]
    rw [←neg_smul]
    congr 1
    ring
  have hp(X Y:End):bracket electricAction (X*Y)=bracket electricAction X*Y+X*bracket electricAction Y:=by
    unfold bracket;noncomm_ring
  have ha(X Y:End):bracket electricAction (X+Y)=bracket electricAction X+bracket electricAction Y:=by
    unfold bracket;noncomm_ring
  have hJ:bracket electricAction clockCurrent=(-2*Complex.I*(n:ℂ)) • (U*electricAction):=by
    rw [original_clock_current,bracket_smul_r,ha]
    simp only [hp,hU,hD,zero_mul,mul_zero,add_zero,zero_add,
      mul_smul_comm,smul_mul_assoc,smul_add,smul_smul]
    rw [electric_weight_commute.eq]
    module
  unfold fullElectricCurrent
  rw [bracket_smul_l,bracket_jacobi,he,hc]
  have hz:bracket H0 (0:End)=0:=by unfold bracket;noncomm_ring
  rw [hz,zero_sub,bracket_smul_r,hJ]
  simp only [smul_neg,smul_smul]
  rw [←neg_smul]
  congr 1
  calc _= -n*(Complex.I*Complex.I):=by ring
       _=_:=by rw [Complex.I_mul_I];ring

def electricLyapunov:End:=electricAction+(2/(n:ℂ)) • clock
private theorem current_lyapunov:bracket fullElectricCurrent electricLyapunov=(-1/2:ℂ) • wedgeAction := by
  have he:bracket fullElectricCurrent electricAction=(-2:ℂ) • (U*electricAction)-(1/2:ℂ) • wedgeAction:=by
    unfold fullElectricCurrent
    rw [bracket_smul_l,bracket_neg (bracket H0 electricAction) electricAction,electric_full_double]
    simp only [smul_neg,smul_add,smul_smul]
    module
  have ha(X Y:End):bracket fullElectricCurrent (X+Y)=bracket fullElectricCurrent X+bracket fullElectricCurrent Y:=by
    unfold bracket;noncomm_ring
  rw [electricLyapunov,ha,he,bracket_smul_r,current_clock,smul_smul]
  have hn:(2/(n:ℂ))*(n:ℂ)=2:=by
    have hn0:(n:ℂ)≠0:=lapse_nonzero
    field_simp [hn0]
  rw [hn]
  module

open MeasureTheory
private theorem wedge_pair_nonnegative(f:QuantumTest):0≤(sourcePair f (wedgeAction f)).re := by
  have hn:0<n:=by
    change 0<sourceTime 0
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hpair:(sourcePair f (wedgeAction f)).re=
      ∫z:SourceCoordinateSlice,(densityPair f (wedgeAction f) z).re ∂GaussHistoryHilbert.configurationMeasure:=by
    rw [sourcePair_integral]
    exact (integral_re (densityPair_integrable f (wedgeAction f))).symm
  rw [hpair]
  apply MeasureTheory.integral_nonneg
  intro z
  change 0≤(densityPair f (wedgeAction f) z).re
  by_cases hz:z∈physicalChart
  · have he:densityPair f (wedgeAction f) z=(electricContactWeight z:ℂ)*densityPair f f z:=inner_smul_right _ _ _
    rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    have hw:0≤electricContactWeight z:=by
      rw [electric_contact_formula ⟨z,hz⟩]
      exact mul_nonneg (by have hv:=volume_pos ⟨z,hz⟩;positivity) (wedge_nonnegative z)
    have hd:0≤(densityPair f f z).re:=by
      have h:=GaussBoundedMultiplier.weighted_square (fun N=>GaussDensityCore.density N z)
        (fun N=>(GaussDensityCore.density_pos N ⟨z,hz⟩).le) (f z)
      exact (sq_nonneg _).trans_eq h.symm
    exact mul_nonneg hw hd
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

/-- The full original R3 word now uses its full-H0 electric primitive, with the same finite-compression defect. -/
theorem actual_matched_electric_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    fullElectricCurrent=coframeElectricCurrent-U*Ggen ∧
    matchedForcingWord m ell F z hz g=electricForcingWord m ell F z hz g ∧
    bracket electricAction (bracket (compressionCore F) electricAction)=
      (4:ℂ) • (U*electricAction)+wedgeAction-bracket electricAction (bracket (defectAction F) electricAction) := by
  refine ⟨?_,electric_forcing_return m ell F z hz g,?_⟩
  · unfold fullElectricCurrent
    rw [full_electric_current]
    simp only [smul_sub,smul_smul]
    norm_num
  · have hH:H0=compressionCore F+defectAction F:=by unfold H0 defectAction;abel
    have hc:=electric_full_double
    rw [hH] at hc
    unfold bracket at hc ⊢
    linear_combination (norm:=noncomm_ring) hc

/-- The actual electric current increases volume and dissipates its dimensionless electric/log-volume quantity. -/
theorem original_electric_positive_current:
    bracket fullElectricCurrent volumeAction=(n:ℂ) • electricAction ∧
    bracket fullElectricCurrent electricLyapunov=(-1/2:ℂ) • wedgeAction ∧
    (∀f:QuantumTest,0≤(sourcePair f (wedgeAction f)).re) ∧
    (∀f:QuantumTest,(sourcePair f ((bracket fullElectricCurrent electricLyapunov) f)).re≤0) := by
  refine ⟨current_volume,current_lyapunov,wedge_pair_nonnegative,?_⟩
  intro f
  rw [current_lyapunov]
  change (sourcePair f ((-1/2:ℂ) • wedgeAction f)).re≤0
  rw [pair_smul_r]
  have hw:=wedge_pair_nonnegative f
  norm_num [Complex.mul_re]
  linarith

end LowEnergy.SourceClockPhiMatchedElectricSource
