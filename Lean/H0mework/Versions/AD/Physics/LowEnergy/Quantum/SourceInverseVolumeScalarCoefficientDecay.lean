import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeScalarTwoLegJoin
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeElectricWindowDecay

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PositiveScalarCoefficientDecay
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussQuantumMultiplier
open GaussLiveMomentum GaussYukawaCoefficient GaussYukawaOperator GaussFockWeights GaussRadialDomain
open SourceMixedNativeReturn SourceNativeCutoffContact SourceInverseElectricWindowDecay
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open PositiveScalarWeakBudget
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem multiply_bound (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (C : ℝ) (hC : 0≤C)
    (hb : ∀ z : physicalChart,|c z.val|≤C) (f : QuantumTest) :
    ‖embed (multiply c hc f)‖≤C*‖embed f‖ := by
  apply GaussBoundedMultiplier.action_bound
    (fun z => (c z : ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun z => (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (hc z)).smul contDiffAt_const)
    (fun _ w => (Commute.one_right (weight w)).smul_right _) C hC _ f
  intro z x
  change ‖(c z.val : ℂ) • x‖≤C*‖x‖
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg x)

/-- The true source radius pays theta, with no choice of a F reader norm. -/
theorem original_theta_radius_bound (m ell : ℕ) (hle : m≤ell) (f : QuantumTest) :
    ‖embed (SourceMixedNativeReturn.thetaAction m ell f)‖≤
      (1/(m+2 : ℝ))*‖embed (radiusAction f)‖ := by
  have he : SourceMixedNativeReturn.thetaAction m ell f=dampingAction m ell (radiusAction f) := by
    apply DFunLike.ext
    intro z
    rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
    change (SourceNativeCutoffContact.theta m ell z : ℂ) • f z=
      ((damping m ell z : ℝ) : ℂ) • ((radius z : ℂ) • f z)
    rw [smul_smul]
    congr 1
    unfold damping reciprocal
    push_cast
    field_simp [(radius_pos z).ne']
  rw [he]
  exact multiply_bound (damping m ell)
    (fun _ => (reciprocal_smooth.mul (SourceNativeCutoffContact.theta_smooth m ell)).contDiffAt)
    (1/(m+2 : ℝ)) (by positivity) (fun z => original_inverse_window_bound m ell hle z.val) _

def derivativeAction (a : ScalarIndex) (m ell : ℕ) : End :=
  multiply (thetaDerivative (scalarDirection a) m ell)
    (fun _ => (theta_derivative_smooth (scalarDirection a) m ell).contDiffAt)

/-- All seventy native directions use the actual derivative bound, including
normal rows; no flat-slice replacement enters the estimate. -/
theorem original_native_derivative_bound (a : ScalarIndex) (m ell : ℕ) (hle : m≤ell) (f : QuantumTest) :
    ‖embed (derivativeAction a m ell f)‖≤(2/(m+2 : ℝ))*‖embed f‖ := by
  apply multiply_bound _ _ _ (by positivity) _ f
  intro z
  have hi : ‖(scalarDirection a).1‖=1 := scalarBasis.orthonormal.norm_eq_one a
  simpa only [hi,mul_one] using theta_derivative_bound (scalarDirection a) m ell hle z.val

private theorem local_full (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    fullAction sharp f z=SourceMixedNativeReturn.branchMap sharp (GaussNativePotential.scalarField z) (f z) := by
  cases sharp <;> rfl

private theorem local_constant (sharp : Bool) (a : ScalarIndex) (f : QuantumTest) (z : SourceCoordinateSlice) :
    constantAction sharp (scalarDirection a).1 f z=
      SourceMixedNativeReturn.branchMap sharp (scalarDirection a).1 (f z) := by
  cases sharp <;> rfl

/-- The contact is joined with the window before the energy estimate. -/
theorem original_coefficient_split (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) (f : QuantumTest) :
    coefficient sharp a m ell f=
      SourceMixedNativeReturn.thetaAction m ell (constantAction sharp (scalarDirection a).1 f)+
        derivativeAction a m ell (fullAction sharp f) := by
  apply DFunLike.ext
  intro z
  simp only [coefficient,LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,Pi.add_apply,Pi.smul_apply]
  change (constantAction sharp (scalarDirection a).1 (SourceMixedNativeReturn.thetaAction m ell f)) z+
    Complex.I • (fullAction sharp (contactAction (scalarDirection a) m ell f)) z=
    (SourceMixedNativeReturn.thetaAction m ell (constantAction sharp (scalarDirection a).1 f)) z+
    (derivativeAction a m ell (fullAction sharp f)) z
  rw [local_constant,local_full]
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  simp only [SourceNativeCutoffContact.thetaAction,multiply_apply,local_constant,local_full,derivativeAction,map_smul]
  change (theta m ell z : ℂ) • branchMap sharp (scalarDirection a).1 (f z)+
    Complex.I • branchMap sharp (GaussNativePotential.scalarField z)
      (((-Complex.I)*(thetaDerivative (scalarDirection a) m ell z : ℂ)) • f z)=
    (theta m ell z : ℂ) • branchMap sharp (scalarDirection a).1 (f z)+
    (thetaDerivative (scalarDirection a) m ell z : ℂ) • branchMap sharp (GaussNativePotential.scalarField z) (f z)
  have hi : Complex.I*((-Complex.I)*(thetaDerivative (scalarDirection a) m ell z : ℂ))=
      (thetaDerivative (scalarDirection a) m ell z : ℂ) := by
    calc _=-(Complex.I*Complex.I)*(thetaDerivative (scalarDirection a) m ell z : ℂ) := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [map_smul,smul_smul,hi]

/-- A cutoff-independent, source-owned pair of actual radius-Y/Y readers pays
Z at every native row and either dual branch. -/
theorem original_coefficient_energy (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) (hle : m≤ell) (f : QuantumTest) :
    ‖embed (coefficient sharp a m ell f)‖^2≤
      (2/(m+2 : ℝ)^2)*(‖embed (radiusAction (constantAction sharp (scalarDirection a).1 f))‖^2+
        4*‖embed (fullAction sharp f)‖^2) := by
  rw [original_coefficient_split,map_add]
  have h1 := original_theta_radius_bound m ell hle (constantAction sharp (scalarDirection a).1 f)
  have h2 := original_native_derivative_bound a m ell hle (fullAction sharp f)
  have hn := norm_add_le (embed (SourceMixedNativeReturn.thetaAction m ell (constantAction sharp (scalarDirection a).1 f)))
    (embed (derivativeAction a m ell (fullAction sharp f)))
  have hp : 0<(m+2 : ℝ) := by positivity
  have hs1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hs2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hsum := sq_nonneg (‖embed (SourceMixedNativeReturn.thetaAction m ell (constantAction sharp (scalarDirection a).1 f))‖-
    ‖embed (derivativeAction a m ell (fullAction sharp f))‖)
  field_simp at hs1 hs2 ⊢
  nlinarith

end LowEnergy.PositiveScalarCoefficientDecay
