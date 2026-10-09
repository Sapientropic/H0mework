import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeForcingPressurePayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentPressureReserve
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceClockPhiRadiusSourceCurrent SourcePhysicalKineticSquare
open FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier FirstCurrentJointBudget
open ReverseNativeClock ReverseNativeFrequencyWard ReverseBalancedForcePayer
open FirstCurrentJointDifference FirstCurrentMatchedPressure FirstCurrentJointForceLoss
open SourceLocalizedInverseFormPayment SourceResolventBandLimit
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev n:ℝ:=sourceTime 0
private abbrev S:End:=phiInverseAction
attribute [local irreducible] embed sourcePair wholeClockState wholeSourceNext clockSourcePair
  jointForceVector completedMatchedSource sourcePressureVector differenceJointLoss sourcePressurePayment
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private def beta:ℝ:=7*n^2/32
private def kappa(a:ℝ):ℝ:=42*n*a
private theorem beta_positive:0<beta:=by unfold beta;have hn:=n_pos;positivity

def pressureReserveCoefficient(a:ℝ):ℝ:=(2/(21*n))/(beta+(kappa a)^2)
def pressureReserveVector(a:ℝ)(u v:QuantumTest):QuantumTest:=
  (kappa a:ℂ) • u-(beta:ℂ) • S v

def radialMatchedReserve(v:QuantumTest):ℝ:=
  (n/12)*∑i:ScalarIndex,‖embed (phiDirectionAction (scalarBasis i) v)‖^2

/-- The radial complement uses the original full ambient scalar Parseval, including the broken directions. -/
theorem actual_radial_matched_reserve(v:QuantumTest):
    radialMatchedReserve v=(n/48)*(‖embed v‖^2-‖embed (S v)‖^2) ∧ 0≤radialMatchedReserve v:=by
  have h:=original_phi_gradient_energy (embed v)
  simp only [original_phi_direction_core] at h
  have hs:phiInverseBounded (embed v)=embed (S v):=by
    unfold S phiInverseAction
    exact GaussBoundedMultiplier.extension_core _ _ _ _ _ _ v
  rw [hs] at h
  constructor
  · unfold radialMatchedReserve
    rw [h]
    ring
  · unfold radialMatchedReserve
    have hn:=n_pos
    positivity

private theorem norm_add_real(u v:H)(k:ℝ):
    ‖u+(k:ℂ) • v‖^2=‖u‖^2+k^2*‖v‖^2+2*k*(inner ℂ u v).re:=by
  rw [norm_add_sq (𝕜:=ℂ)]
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_right,
    RCLike.re_eq_complex_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring
private theorem norm_reserve(u v:H)(k b:ℝ):
    ‖(k:ℂ) • u-(b:ℂ) • v‖^2=k^2*‖u‖^2+b^2*‖v‖^2-2*k*b*(inner ℂ u v).re:=by
  rw [norm_sub_sq (𝕜:=ℂ)]
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_left,inner_smul_right,
    RCLike.re_eq_complex_re,Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  ring

def pressureReserve(a:ℝ)(u v:QuantumTest):ℝ:=
  pressureReserveCoefficient a*‖embed (pressureReserveVector a u v)‖^2+radialMatchedReserve v

/-- The two physical negative squares retain their exact Schur complement and radial matched reserve, with all ordered interference. -/
theorem actual_exact_pressure_reserve(a:ℝ)(u v:QuantumTest):
    pressureCoefficient a*‖embed (u+((42*n*a:ℝ):ℂ) • S v)‖^2+pressureReserve a u v=
      (2/(21*n))*‖embed u‖^2+(n/48)*‖embed v‖^2 ∧ 0≤pressureReserve a u v:=by
  constructor
  · unfold pressureReserve
    rw [(actual_radial_matched_reserve v).1]
    simp only [pressureReserveVector,map_sub,map_add,map_smul]
    rw [norm_add_real,norm_reserve]
    unfold pressureReserveCoefficient pressureCoefficient beta kappa
    have hp:0<1+8064*a^2:=by positivity
    have hd:0<7*n^2/32+(42*n*a)^2:=by have hn:=n_pos;positivity
    field_simp [n_pos.ne',hp.ne',hd.ne']
    ring
  · unfold pressureReserve pressureReserveCoefficient
    have hb:=beta_positive
    have hn:=n_pos
    exact add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (actual_radial_matched_reserve v).2

def wholePressureReserve(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  pressureReserve (reverseNoetherFactor half)
    (jointForceVector s hs half advanced m ell F g x q) (completedMatchedSource s hs half advanced m ell F g x q)

/-- The source reserve is part of the same original two-square resource; no additional matched payment is introduced. -/
theorem actual_whole_pressure_reserve_balance(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    sourcePressurePayment s hs half advanced m ell F g x q+wholePressureReserve s hs half advanced m ell F g x q=
      differenceJointLoss s hs half advanced m ell F g x q+matchedSquarePrice s hs half advanced m ell F g x q ∧
      0≤wholePressureReserve s hs half advanced m ell F g x q:=by
  have h:=actual_exact_pressure_reserve (reverseNoetherFactor half)
    (jointForceVector s hs half advanced m ell F g x q) (completedMatchedSource s hs half advanced m ell F g x q)
  refine ⟨?_,h.2⟩
  rw [actual_pressure_vector_return] at h
  unfold sourcePressurePayment wholePressureReserve differenceJointLoss jointForceInputLoss matchedSquarePrice
  simp only [jointForceVector,map_add,map_smul] at h ⊢
  linarith only [h.1]
end LowEnergy.FirstCurrentPressureReserve
