import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeElectricCurrentGrowth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseElectricCurrentFactor
open GaussHistoryHilbert GaussCoreHilbert GaussCoreDifferential GaussMatterCore GaussNativePotential GaussYukawaCoefficient
open GaussNativeForm GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory GaussQuantumMultiplier GaussFockWeights
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceScalarBalancedForce SourceMixedNativeReturn SourceInverseElectricCurrentForm SourceInverseElectricCurrentCoefficient
open SourceInverseElectricCurrentGrowth SourceScalarPositiveBulkWard SourceCartanCubic
open scoped ContDiff InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

/-- A smooth envelope generated from the original coframe coefficients; no uniform coframe constant is chosen. -/
def contactMajorant (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  ∑ i : Fin 3, ∑ b : Fin 3, Real.sqrt (1+(GaussMatterCore.coefficient i b z)^2)*
    ‖(quantumTerm b).toContinuousLinearMap‖*‖gaugeCoordinate i v.2‖

def coframeEnvelope (sharp : Bool) (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  1+2*contactMajorant v z*‖branchMap sharp‖*(‖vacuum‖+2)

def envelope (sharp : Bool) (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  coframeEnvelope sharp v z*radius z

private theorem majorant_nonneg (v : Ambient) (z : SourceCoordinateSlice) : 0 ≤ contactMajorant v z := by
  unfold contactMajorant
  positivity
private theorem contact_le (v : Ambient) (z : SourceCoordinateSlice) : contactBound v z ≤ contactMajorant v z := by
  unfold contactBound contactMajorant
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro b _
  have h : |GaussMatterCore.coefficient i b z| ≤ Real.sqrt (1+(GaussMatterCore.coefficient i b z)^2) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1+(GaussMatterCore.coefficient i b z)^2 by positivity)
    nlinarith [Real.sqrt_nonneg (1+(GaussMatterCore.coefficient i b z)^2),abs_nonneg (GaussMatterCore.coefficient i b z),sq_abs (GaussMatterCore.coefficient i b z)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h (norm_nonneg ((quantumTerm b).toContinuousLinearMap)))
    (norm_nonneg (gaugeCoordinate i v.2))

theorem envelope_pos (sharp : Bool) (v : Ambient) (z : SourceCoordinateSlice) : 0 < envelope sharp v z := by
  unfold envelope coframeEnvelope
  have h := majorant_nonneg v z
  have hr := radius_pos z
  positivity

theorem envelope_smooth (sharp : Bool) (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (envelope sharp v) z.val := by
  have hM : ContDiffAt ℝ ∞ (contactMajorant v) z.val := by
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro b _
    exact (((contDiffAt_const.add ((coefficient_smooth i b z).pow 2)).sqrt (by positivity)).mul contDiffAt_const).mul contDiffAt_const
  exact (contDiffAt_const.add (((contDiffAt_const.mul hM).mul contDiffAt_const).mul contDiffAt_const)).mul radius_smooth.contDiffAt

private theorem kernel_bound (sharp : Bool) (v : Ambient) (z : SourceCoordinateSlice) :
    ‖currentKernel sharp v z‖ ≤ envelope sharp v z := by
  apply (original_current_growth sharp v z).trans
  apply mul_le_mul_of_nonneg_right _ (radius_pos z).le
  unfold sourceGrowth coframeEnvelope
  have h0 : 2*contactBound v z ≤ 2*contactMajorant v z :=
    mul_le_mul_of_nonneg_left (contact_le v z) (by norm_num)
  have h1 := mul_le_mul_of_nonneg_right h0 (norm_nonneg (branchMap sharp))
  have h2 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ ‖vacuum‖+2 by positivity)
  linarith

private theorem quantized_adjoint (A : Matrix Mode Mode ℂ) : (quantized A).adjoint=quantized A.conjTranspose := by
  apply ContinuousLinearMap.ext
  intro psi
  apply ext_inner_left ℂ
  intro phi
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact SourceQuantumFockGauge.quantizedFiber_adjoint A phi psi

private theorem branch_commutes (sharp : Bool) (phi : Scalar) (w : ℕ → ℂ) :
    Commute (weight w) (branchMap sharp phi) := by
  cases sharp
  · change Commute _ (sourceMap phi)
    rw [source_map_return]
    exact weight_commute _ _
  · change Commute _ (sourceMap phi).adjoint
    rw [source_map_return,quantized_adjoint]
    exact weight_commute _ _

/-- The full contact commutator preserves every original Number-dependent density. -/
theorem original_current_weight (sharp : Bool) (v : Ambient) (z : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (weight w) (currentKernel sharp v z) := by
  have hC : Commute (weight w) (contactFiber v z) := by
    unfold contactFiber
    apply Commute.sum_right
    intro i _
    apply Commute.sum_right
    intro b _
    apply Commute.smul_right
    exact weight_commute _ _
  have hY := branch_commutes sharp (scalarField z) w
  exact ((hC.mul_right hY).sub_right (hY.mul_right hC)).smul_right _

private theorem kernel_smooth (sharp : Bool) (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (currentKernel sharp v) z.val := by
  have hC : ContDiffAt ℝ ∞ (contactFiber v) z.val := by
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro b _
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (coefficient_smooth i b z)).smul contDiffAt_const
  have hY : ContDiffAt ℝ ∞ (fun x => branchMap sharp (scalarField x)) z.val :=
    (branchMap sharp).contDiff.contDiffAt.comp z.val scalarField_smooth.contDiffAt
  exact (contDiffAt_const (c := (-Complex.I))).smul ((hC.mul hY).sub (hY.mul hC))

def normalizedCurrent (sharp : Bool) (v : Ambient) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (((envelope sharp v z)⁻¹ : ℝ) : ℂ) • currentKernel sharp v z

private theorem normalized_smooth (sharp : Bool) (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (normalizedCurrent sharp v) z.val :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
    ((envelope_smooth sharp v z).inv (envelope_pos sharp v z.val).ne')).smul (kernel_smooth sharp v z)
private theorem normalized_commutes (sharp : Bool) (v : Ambient) (z : physicalChart) (w : ℕ → ℂ) :
    Commute (weight w) (normalizedCurrent sharp v z.val) :=
  (original_current_weight sharp v z.val w).smul_right _
private theorem normalized_bound (sharp : Bool) (v : Ambient) (z : physicalChart) (f : FockFiber) :
    ‖normalizedCurrent sharp v z.val f‖ ≤ (1 : ℝ)*‖f‖ := by
  have hp := envelope_pos sharp v z.val
  have hK := kernel_bound sharp v z.val
  have hN : ‖normalizedCurrent sharp v z.val‖ ≤ (1 : ℝ) := by
    rw [normalizedCurrent,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
    exact (mul_le_mul_of_nonneg_left hK (inv_pos.mpr hp).le).trans_eq (inv_mul_cancel₀ hp.ne')
  exact ((normalizedCurrent sharp v z.val).le_opNorm f).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg f))

/-- Same-source bounded factor on the original Number-weighted Hilbert space. -/
def boundedCurrent (sharp : Bool) (v : Ambient) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (normalizedCurrent sharp v) (normalized_smooth sharp v)
    (normalized_commutes sharp v) 1 (by norm_num) (normalized_bound sharp v)

def envelopeAction (sharp : Bool) (v : Ambient) : QuantumTest →ₗ[ℂ] QuantumTest :=
  multiply (envelope sharp v) (envelope_smooth sharp v)

theorem bounded_current_norm (sharp : Bool) (v : Ambient) : ‖boundedCurrent sharp v‖ ≤ 1 :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

theorem actual_current_factor (sharp : Bool) (m ell : ℕ) (v : Ambient) (hv : v.1=0) (f : QuantumTest) :
    boundedCurrent sharp v (embed (envelopeAction sharp v (SourceMixedNativeReturn.thetaAction m ell f)))=
      embed (windowCurrent sharp m ell v f) := by
  rw [boundedCurrent,GaussBoundedMultiplier.extension_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  rw [original_window_current_apply sharp m ell v hv]
  change normalizedCurrent sharp v z (envelopeAction sharp v (SourceMixedNativeReturn.thetaAction m ell f) z)=_
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  change (((envelope sharp v z)⁻¹ : ℝ) : ℂ) • (currentKernel sharp v z
    ((envelope sharp v z : ℂ) • ((SourceNativeCutoffContact.theta m ell z : ℂ) • f z)))=_
  rw [map_smul,map_smul,smul_smul,show (((envelope sharp v z)⁻¹ : ℝ) : ℂ)*(envelope sharp v z : ℂ)=1 by
    exact_mod_cast inv_mul_cancel₀ (envelope_pos sharp v z).ne',one_smul]

/-- No coframe-uniform hypothesis is needed: its actual envelope remains on the same input. -/
theorem actual_current_energy (sharp : Bool) (m ell : ℕ) (v : Ambient) (hv : v.1=0) (f : QuantumTest) :
    ‖embed (windowCurrent sharp m ell v f)‖^2 ≤
      ‖embed (envelopeAction sharp v (SourceMixedNativeReturn.thetaAction m ell f))‖^2 := by
  rw [←actual_current_factor sharp m ell v hv f]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact ((boundedCurrent sharp v).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (bounded_current_norm sharp v) (norm_nonneg _)).trans_eq (one_mul _))

end LowEnergy.SourceInverseElectricCurrentFactor
