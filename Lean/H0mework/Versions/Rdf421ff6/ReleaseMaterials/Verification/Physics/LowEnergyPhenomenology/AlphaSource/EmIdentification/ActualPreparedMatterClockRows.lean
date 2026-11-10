import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterSupportPi
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedAuxiliaryClockRows
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterSupportNative
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualPreparedMatterClock
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedEMTensorClock
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedFourClockCarrier
open ActualSourcePreparedReducedQuantumCofactor ActualSourcePreparedNoetherPi
open ActualSourcePreparedAuxiliaryClockRows
open ActualPreparedMatterAuxiliary ActualPreparedMatterSupport ActualDressedEMNativeAuxiliary
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

/-- The original all-transfer inactive Pi zero is cleared by the same source
clock denominator. Its two-variable polynomial row is therefore zero for every
one of the 192 source-inactive coordinates. -/
theorem source_matter_clock_response_row_zero (event : DressedEvent) (n : PhysicalMomentum)
    (i : Fin 289) (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val) (j : Fin 289) :
    sourceFourClockResponseNumerator event n i j=0 := by
  apply clock_polynomial_zero
  intro eps sigma positive
  have source := source_clock_reduced_pi_clear event n eps sigma positive i j
  have real_positive : 0<(sigma : ℂ).re := by simpa only [Complex.ofReal_re] using positive
  rw [actual_prepared_inactive_pi_row event (eps^2 • n) (sigma : ℂ) real_positive i outside j,
    mul_zero] at source
  exact source.symm

/-- Each source-inactive original Jacobi row carries exactly the shared cubic
clock factor after the zero response row is subtracted. -/
theorem source_matter_clock_pencil_row (event : DressedEvent) (n : PhysicalMomentum)
    (i : Fin 289) (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val) (j : Fin 289) :
    sourceClockReducedPencil event n i j=
      (X^3*sourceFourClockDenominator event n)*
        staticIRClockSlice (commonJacobi n i j) := by
  unfold sourceClockReducedPencil sourceClockReducedNumerator
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.map_apply,
    source_matter_clock_response_row_zero event n i outside j,sub_zero]

end LowEnergy.GaussComposite.ActualPreparedMatterClock
