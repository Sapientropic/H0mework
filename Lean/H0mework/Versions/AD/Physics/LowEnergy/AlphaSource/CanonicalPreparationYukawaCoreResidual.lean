import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationYukawaSourceRegion

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLocalizedYukawa
open SaturationMonoid.PhysicsCore
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDensityCore GaussFockPair
open GaussYukawaCoefficient GaussYukawaOperator GaussRadialDomain FullYSourceCutoffVolterra GaussNativePotential
open GaussBoundedMultiplier SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge
open PreparationActualFactor PreparationScalarCoordinates CanonicalPreparationCutoff MeasureTheory Set
open scoped BigOperators Topology ContDiff RealInnerProductSpace

def remainderCoefficient (n : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  (1-reciprocal z)^(n+1)*radius z

theorem remainderCoefficient_smooth (n : ℕ) : ContDiff ℝ ∞ (remainderCoefficient n) :=
  ((contDiff_const.sub reciprocal_smooth).pow (n+1)).mul radius_smooth

def remainderFiber (n : ℕ) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (remainderCoefficient n z : ℂ) • normalized z

theorem remainderFiber_smooth (n : ℕ) : ContDiff ℝ ∞ (remainderFiber n) :=
  (Complex.ofRealCLM.contDiff.comp (remainderCoefficient_smooth n)).smul normalized_smooth

theorem remainderFiber_commutes (n : ℕ) (z : SourceCoordinateSlice) (w : ℕ→ℂ) :
    Commute (GaussFockWeights.weight w) (remainderFiber n z) :=
  (normalized_commutes z w).smul_right _

def remainderCore (n : ℕ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (remainderFiber n) (fun _=>(remainderFiber_smooth n).contDiffAt)


theorem residual_power_core (n : ℕ) (f : QuantumTest) :
    ((1-inverseRadius)^n) (embed f)=
      embed (GaussNativeForm.multiply (fun z=>(1-reciprocal z)^n)
        (fun _=>((contDiff_const.sub reciprocal_smooth).pow n).contDiffAt) f) := by
  induction n with
  | zero=>
    simp only [pow_zero,one_apply_eq_self]
    apply congrArg embed
    apply DFunLike.ext
    intro z
    simp only [GaussNativeForm.multiply_apply,Complex.ofReal_one,one_smul]
  | succ n ih=>
    rw [pow_succ']
    change (1-inverseRadius) (((1-inverseRadius)^n) (embed f))=_
    rw [ih]
    simp only [sub_apply,one_apply_eq_self,inverse_core,←map_sub]
    apply congrArg embed
    apply DFunLike.ext
    intro z
    dsimp only [GaussRadialDomain.inverseAction]
    simp only [sub_apply,GaussNativeForm.multiply_apply]
    rw [smul_smul,←sub_smul,pow_succ']
    apply congrArg (fun c : ℂ=>c • f z)
    push_cast
    ring



theorem original_cutoff_core_residual (n : ℕ) (f : QuantumTest) :
    embed (originalAction f)-cutoff n (embed f)=embed (remainderCore n f) := by
  rw [actual_cutoff_graph_residual n _ _ (original_graph f),residual_power_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  rw [GaussNativeForm.multiply_apply]
  change (((1-reciprocal z)^(n+1) : ℝ) : ℂ) • (sourceMap (scalarField z) (f z))=
    (remainderCoefficient n z : ℂ) • (normalized z (f z))
  rw [←radius_return z]
  change (((1-reciprocal z)^(n+1) : ℝ) : ℂ) • ((radius z : ℝ) • (normalized z (f z)))=_
  rw [←IsScalarTower.algebraMap_smul ℂ (radius z),smul_smul]
  simp only [remainderCoefficient,Complex.ofReal_mul]
  rfl



theorem remainderFiber_source_bound (n : ℕ) (z : SourceCoordinateSlice)
    (box : fullCoordinates z∈sourceClosedBox) (f : FockFiber) :
    ‖remainderFiber n z f‖ ≤ sourceCutRate^(n+1)*sourceRadiusBound*bound*‖f‖ := by
  have rate:=source_geometric_rate z box
  have coefficient : 0 ≤ remainderCoefficient n z := mul_nonneg (pow_nonneg rate.1 _) (radius_pos z).le
  have upper : remainderCoefficient n z ≤ sourceCutRate^(n+1)*sourceRadiusBound :=
    mul_le_mul (pow_le_pow_left₀ rate.1 rate.2 _) (source_radius_bound z box)
      (radius_pos z).le (pow_nonneg sourceCutRate_nonnegative _)
  rw [remainderFiber,smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg coefficient]
  calc
    _ ≤ remainderCoefficient n z*(bound*‖f‖) :=
      mul_le_mul_of_nonneg_left (normalized_bound z f) coefficient
    _ ≤ (sourceCutRate^(n+1)*sourceRadiusBound)*(bound*‖f‖) :=
      mul_le_mul_of_nonneg_right upper (mul_nonneg bound_nonneg (norm_nonneg _))
    _ = _ := by ring


theorem original_cutoff_source_core_bound (n : ℕ) (f : QuantumTest)
    (supported : tsupport f ⊆ fullCoordinates ⁻¹' sourceClosedBox) :
    ‖embed (originalAction f)-cutoff n (embed f)‖ ≤
      sourceCutRate^(n+1)*sourceRadiusBound*bound*‖embed f‖ := by
  let C:=sourceCutRate^(n+1)*sourceRadiusBound*bound
  have nonnegative : 0 ≤ C := mul_nonneg
    (mul_nonneg (pow_nonneg sourceCutRate_nonnegative _) sourceRadiusBound_positive.le) bound_nonneg
  let g:=remainderCore n f
  have point (z : SourceCoordinateSlice) : RCLike.re (densityPair g g z) ≤ C^2*RCLike.re (densityPair f f z) := by
    by_cases inside : z∈tsupport f
    · change RCLike.re (inner ℂ (GaussFockWeights.weight (fun N=>(density N z : ℂ))
        (remainderFiber n z (f z))) (remainderFiber n z (f z))) ≤ _
      exact weighted_bound (fun N=>density N z) (fun N=>(density_pos N ⟨z,f.tsupport_subset inside⟩).le)
        (remainderFiber n z) (remainderFiber_commutes n z) C
        (remainderFiber_source_bound n z (supported inside)) (f z)
    · have zero : f z=0 := image_eq_zero_of_notMem_tsupport inside
      have gz : g z=0 := by change remainderFiber n z (f z)=0;rw [zero,map_zero]
      simp only [densityPair,zero,gz,map_zero,inner_zero_left,map_zero,mul_zero,le_refl]
  have square : ‖embed g‖^2 ≤ C^2*‖embed f‖^2 := by
    calc
      _ = ∫ z,RCLike.re (densityPair g g z) ∂GaussHistoryHilbert.configurationMeasure := norm_square_integral g
      _ ≤ ∫ z,C^2*RCLike.re (densityPair f f z) ∂GaussHistoryHilbert.configurationMeasure :=
        integral_mono (densityPair_integrable g g).re ((densityPair_integrable f f).re.const_mul _) point
      _ = _ := by rw [integral_const_mul,←norm_square_integral]
  rw [original_cutoff_core_residual]
  change ‖embed g‖ ≤ C*‖embed f‖
  nlinarith [norm_nonneg (embed g),mul_nonneg nonnegative (norm_nonneg (embed f))]

theorem original_yukawa_source_core_bound (f : QuantumTest)
    (supported : tsupport f ⊆ fullCoordinates ⁻¹' sourceClosedBox) :
    ‖embed (originalAction f)‖ ≤ sourceRadiusBound*bound*‖embed f‖ := by
  have residual := original_cutoff_source_core_bound 0 f supported
  have cut : ‖cutoff 0 (embed f)‖ ≤ bound*‖embed f‖ := by
    change ‖GaussYukawaOperator.bounded (embed f)‖ ≤ _
    exact ((GaussYukawaOperator.bounded).le_opNorm (embed f)).trans
      (mul_le_mul_of_nonneg_right GaussYukawaOperator.bounded_norm (norm_nonneg _))
  calc
    _ = ‖(embed (originalAction f)-cutoff 0 (embed f))+cutoff 0 (embed f)‖ :=
      congrArg norm (sub_add_cancel _ _).symm
    _ ≤ ‖embed (originalAction f)-cutoff 0 (embed f)‖+‖cutoff 0 (embed f)‖ :=
      norm_add_le _ _
    _ ≤ sourceCutRate^(0+1)*sourceRadiusBound*bound*‖embed f‖+bound*‖embed f‖ :=
      add_le_add residual cut
    _ = _ := by norm_num [sourceCutRate,sourceRadiusBound];ring

end LowEnergy.PreparationVacuumLocalizedYukawa
