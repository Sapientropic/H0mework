import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedClockReducedPencil
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedReducedQuantumCofactor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterAuxiliaryPiReturn
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedAuxiliaryClockRows
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedEMTensorClock
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedFourClockCarrier
open ActualSourcePreparedReducedQuantumCofactor ActualSourcePreparedNoetherPi
open ActualPreparedMatterAuxiliary ActualDressedEMNativeAuxiliary
open ActualDressedUniformMaterialCoefficients ActualDressedOrderedStatic ActualDressedZeroDamping
open scoped Matrix BigOperators
attribute [local irreducible] sourceFourClockResponseNumerator sourceFourClockDenominator
  sourceClockReducedPencil sourceClockReducedNumerator sourcePreparedPiEntry

private theorem positive_real_polynomial_zero (P : ℂ[X])
    (zero : ∀ s : ℝ, 0<s → P.eval (s : ℂ)=0) : P=0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have injective : Function.Injective (fun k : ℕ => ((k+1 : ℕ) : ℂ)) := by
    intro a b same
    change ((a+1 : ℕ) : ℂ)=((b+1 : ℕ) : ℂ) at same
    have natural : a+1=b+1 := by exact_mod_cast same
    omega
  refine (Set.infinite_range_of_injective injective).mono ?_
  rintro z ⟨k,rfl⟩
  change P.eval ((k+1 : ℕ) : ℂ)=0
  have point : (((k : ℝ)+1 : ℝ) : ℂ)=((k+1 : ℕ) : ℂ) := by push_cast;rfl
  rw [←point]
  exact zero ((k : ℝ)+1) (by positivity)

private theorem clock_polynomial_zero (P : (ℂ[X])[X])
    (zero : ∀ eps sigma : ℝ, 0<sigma → sourceClockEval eps sigma P=0) : P=0 := by
  have specialized (eps : ℝ) : clockSpecialize eps P=0 :=
    positive_real_polynomial_zero _ (fun sigma positive => zero eps sigma positive)
  apply Polynomial.ext
  intro k
  rw [coeff_zero]
  apply positive_real_polynomial_zero
  intro eps _
  have coefficient := congrArg (fun Q : ℂ[X] => Q.coeff k) (specialized eps)
  simpa only [clockSpecialize,Polynomial.coe_mapRingHom,coeff_map,coeff_zero,
    Polynomial.coe_evalRingHom] using coefficient

/-- The original all-transfer auxiliary Pi zero is cleared by the same
source clock denominator. Its two-variable polynomial row is therefore zero. -/
theorem source_auxiliary_clock_response_row_zero (event : DressedEvent) (n : PhysicalMomentum)
    (pair : Fin 6 × Fin 12) (j : Fin 289) :
    sourceFourClockResponseNumerator event n (gaugeAuxiliaryIndex pair) j=0 := by
  apply clock_polynomial_zero
  intro eps sigma positive
  have source := source_clock_reduced_pi_clear event n eps sigma positive (gaugeAuxiliaryIndex pair) j
  have real_positive : 0<(sigma : ℂ).re := by simpa only [Complex.ofReal_re] using positive
  rw [actual_prepared_auxiliary_pi_row event (eps^2 • n) (sigma : ℂ) real_positive pair j,
    mul_zero] at source
  exact source.symm

/-- The full auxiliary rows are retained: their quantum numerator vanishes,
and their original Jacobi row carries exactly the shared cubic clock factor. -/
theorem source_auxiliary_clock_pencil_row (event : DressedEvent) (n : PhysicalMomentum)
    (pair : Fin 6 × Fin 12) (j : Fin 289) :
    sourceClockReducedPencil event n (gaugeAuxiliaryIndex pair) j=
      (X^3*sourceFourClockDenominator event n)*
        staticIRClockSlice (commonJacobi n (gaugeAuxiliaryIndex pair) j) := by
  unfold sourceClockReducedPencil sourceClockReducedNumerator
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.map_apply,
    source_auxiliary_clock_response_row_zero,sub_zero]

/-- The row factor is an original source polynomial, generated nonzero by
the paid positive-clock clearing; no Green chart or field normalization enters. -/
theorem source_auxiliary_clock_factor_nonzero (event : DressedEvent) (n : PhysicalMomentum) :
    (X^3*sourceFourClockDenominator event n : (ℂ[X])[X])≠0 := by
  have denominator : sourceFourClockDenominator event n≠0 := by
    have paid := source_reduced_clock_denominator_nonzero event n 0 1 (by norm_num)
    intro zero
    exact paid (by rw [zero,map_zero])
  exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) denominator

end LowEnergy.GaussComposite.ActualSourcePreparedAuxiliaryClockRows
