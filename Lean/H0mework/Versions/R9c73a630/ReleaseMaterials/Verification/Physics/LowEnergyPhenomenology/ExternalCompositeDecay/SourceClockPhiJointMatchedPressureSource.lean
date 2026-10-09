import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeJointDifferencePayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWeightedDifferenceMatchedSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentMatchedPressure
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourcePhysicalKineticSquare
open SourceClockPhiRadiusSourceCurrent SourceClockPhiMatchedElectricSource SourceClockPhiNativeMatchedSource
open FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier FirstCurrentJointBudget ReverseNativeClock
open ReverseNativeFrequencyWard ReverseScalarGaugeWard
open ReverseBalancedForcePayer FirstCurrentJointDifference FirstCurrentJointForceLoss JointDifferenceMatchedSource
open SourceLocalizedInverseFormPayment SourceResolventBandLimit
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev S:End:=phiInverseAction
private abbrev U:End:=inverseVolumeAction
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] embed sourcePair wholeClockState wholeSourceNext clockSourcePair jointDifference
  matchedTester matchedDifferenceRemainder balancedCompressionForce reverseNoetherFactor
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem inverse_radius_contraction(f:QuantumTest):‖embed (S f)‖ ≤ ‖embed f‖:=by
  have he:phiInverseBounded (embed f)=embed (S f):=by
    unfold S phiInverseAction
    exact GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
  have hn:‖phiInverseBounded‖ ≤ 1:=GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
  rw [←he]
  exact (phiInverseBounded.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (one_mul _))

def pressureCoefficient(a:ℝ):ℝ:=2/(21*n*(1+8064*a^2))
private theorem coefficient_positive(a:ℝ):0<pressureCoefficient a:=by unfold pressureCoefficient;have hn:=n_pos;positivity

/-- The original inverse-radius contraction couples the two physical squares for every real a. No small-a hypothesis is used. -/
theorem actual_two_matched_squares(a:ℝ)(u v:QuantumTest):
    pressureCoefficient a*‖embed (u+((42*n*a:ℝ):ℂ) • S v)‖^2 ≤
      (2/(21*n))*‖embed u‖^2+(n/48)*‖embed v‖^2:=by
  let β:ℝ:=7*n^2/32
  let k:ℝ:=42*n*a
  let x:ℝ:=‖embed u‖
  let y:ℝ:=‖embed v‖
  have hβ:0<β:=by dsimp only [β];have hn:=n_pos;positivity
  have hxy:0 ≤ x+|k| *y:=by dsimp only [x,y];positivity
  have hn:‖embed (u+(k:ℂ) • S v)‖ ≤ x+|k| *y:=by
    rw [map_add,map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    have h:=mul_le_mul_of_nonneg_left (inverse_radius_contraction v) (abs_nonneg k)
    dsimp only [x,y]
    linarith only [h]
  have hsq:=sq_le_sq₀ (norm_nonneg _) hxy |>.mpr hn
  have hreal:β*(x+|k| *y)^2 ≤ (β+k^2)*(x^2+β*y^2):=by
    rw [←sq_abs k]
    nlinarith only [sq_nonneg (|k| *x-β*y)]
  have hp:=mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hsq hβ.le).trans hreal) (coefficient_positive a).le
  have hc:pressureCoefficient a*(β+k^2)=(2/(21*n))*β:=by
    dsimp only [pressureCoefficient,β,k]
    field_simp [n_pos.ne',(show 0<1+8064*a^2 by positivity).ne']
    ring
  apply (mul_le_mul_iff_right₀ hβ).mp
  calc
    _=pressureCoefficient a*(β*‖embed (u+(k:ℂ) • S v)‖^2):=by ring
    _ ≤ pressureCoefficient a*((β+k^2)*(x^2+β*y^2)):=hp
    _=β*((2/(21*n))*‖embed u‖^2+(n/48)*‖embed v‖^2):=by
      rw [←mul_assoc,hc]
      dsimp only [β,x,y]
      field_simp [n_pos.ne']
      ring

def completedMatchedSource(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  matchedTester (wholeClockState s hs half advanced m ell F g x q)+(144/(n:ℂ)) •
    (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2
def jointForceVector(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  phiRadiusAction (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q))+
    ((14*n*reverseNoetherFactor half:ℝ):ℂ) • S (U (jointDifference s hs half advanced m ell F g x q))
def sourcePressureVector(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  phiRadiusAction (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q))+
    ((14*n*reverseNoetherFactor half:ℝ):ℂ) • matchedDifferenceRemainder s hs half advanced m ell F g x q

theorem actual_pressure_vector_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    jointForceVector s hs half advanced m ell F g x q+
      ((42*n*reverseNoetherFactor half:ℝ):ℂ) • S (completedMatchedSource s hs half advanced m ell F g x q)=
        sourcePressureVector s hs half advanced m ell F g x q:=by
  have h:S (U (jointDifference s hs half advanced m ell F g x q))+
      (3:ℂ) • S (completedMatchedSource s hs half advanced m ell F g x q)=matchedDifferenceRemainder s hs half advanced m ell F g x q:=by
    simpa only [jointDifference,completedMatchedSource] using actual_whole_matched_difference_source s hs half advanced m ell F g x q
  unfold jointForceVector sourcePressureVector
  linear_combination (norm:=(push_cast;module)) ((14*n*reverseNoetherFactor half:ℝ):ℂ) • h

def sourcePressurePayment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  pressureCoefficient (reverseNoetherFactor half)*‖embed (sourcePressureVector s hs half advanced m ell F g x q)‖^2+
    (sourcePair (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q))
      (electricAction (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q)))).re/42

/-- Both original negative completions pay one actual full-forcing/native pressure vector, with the electric force energy retained. -/
theorem actual_joint_matched_pressure_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    0 ≤ sourcePressurePayment s hs half advanced m ell F g x q ∧
    sourcePressurePayment s hs half advanced m ell F g x q ≤
      differenceJointLoss s hs half advanced m ell F g x q+(n/48)*‖embed (completedMatchedSource s hs half advanced m ell F g x q)‖^2:=by
  have h:=actual_two_matched_squares (reverseNoetherFactor half)
    (jointForceVector s hs half advanced m ell F g x q) (completedMatchedSource s hs half advanced m ell F g x q)
  rw [actual_pressure_vector_return] at h
  constructor
  · unfold sourcePressurePayment
    have hE:=JointElectricSource.actual_electric_energy_nonnegative (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q))
    exact add_nonneg (mul_nonneg (coefficient_positive _).le (sq_nonneg _)) (div_nonneg hE (by norm_num))
  · unfold sourcePressurePayment differenceJointLoss jointForceInputLoss
    simp only [jointForceVector,map_add,map_smul] at h
    linarith only [h]
end LowEnergy.FirstCurrentMatchedPressure
