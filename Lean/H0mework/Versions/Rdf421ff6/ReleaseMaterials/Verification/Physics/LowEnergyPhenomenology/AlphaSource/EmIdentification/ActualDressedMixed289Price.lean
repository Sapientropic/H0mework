import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMixedResponsePrice
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualSourceMixed289ResponseOwn
open GaussCoreHilbert GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse
open PreparationVacuumFullFieldRiesz PreparationVacuumSourcePreparedResponse
open PreparationVacuumJointFieldResponse PreparationVacuumActionFieldLift
open ActualQuantitativePreparedFrameOwn ActualNativePreparedLegPriceOwn
open GaussComposite.ActualDressedNoether GaussComposite.ActualDressedFullCoulomb GaussComposite.ActualDressedSourcePreparation
open CanonicalPreparationCore.Completed GaussComposite.SourceGraph
open scoped Topology InnerProductSpace BigOperators Matrix
attribute [local irreducible] dressedEulerObserver sourceDressedUnit sourceProfile actualPrepared jointVertex mixedVertex

private theorem unit_pair_price {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (P : ℝ) (paid : ‖A‖ ≤ P) (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖-inner ℂ x (A x) + inner ℂ y (A y)‖ ≤ 2 * P := by
  have ax : ‖A x‖ ≤ P := by
    simpa only [hx, mul_one] using (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right paid (norm_nonneg x))
  have ay : ‖A y‖ ≤ P := by
    simpa only [hy, mul_one] using (A.le_opNorm y).trans (mul_le_mul_of_nonneg_right paid (norm_nonneg y))
  have first := (norm_inner_le_norm (𝕜 := ℂ) x (A x)).trans (mul_le_mul_of_nonneg_left ax (norm_nonneg x))
  have second := (norm_inner_le_norm (𝕜 := ℂ) y (A y)).trans (mul_le_mul_of_nonneg_left ay (norm_nonneg y))
  rw [hx, one_mul] at first
  rw [hy, one_mul] at second
  exact ((norm_add_le (-inner ℂ x (A x)) (inner ℂ y (A y))).trans
    (add_le_add (by simpa only [norm_neg] using first) second)).trans_eq (by ring)

private theorem original_dressed_observer_price (event : DressedEvent) (A : H →L[ℂ] H)
    (P : ℝ) (paid : ‖A‖ ≤ P) : ‖dressedEulerObserver event A‖ ≤ 2 * P := by
  have unit := source_dressed_unit_norm event.epsilon event.precision
  have background : ‖prepared (sourceProfile event.epsilon event.precision)‖ = 1 := by
    simpa only [actualPrepared] using actualPrepared_norm event.epsilon event.precision
  rw [dressed_euler_observer_original]
  exact unit_pair_price A P paid _ _ unit background

-- The event retains its original momentum, frame, nonreal energy, unit excitation and background.
def actualDressedMixed289Array (event : DressedEvent) (transfer : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => dressedEulerObserver event
    (mixedVertex (fieldUnit i) (fieldUnit j) event.momentum (-transfer) event.frame event.energy event.energy)

theorem actualDressedMixed289Array_generated (event : DressedEvent) (transfer : PhysicalMomentum) (i j : Fin 289) :
    HasDerivAt (fun r : ℝ => dressedEulerObserver event
      (jointVertex (fieldUnit j) event.momentum (-transfer) event.frame event.energy event.energy (r • fieldUnit i)))
      (actualDressedMixed289Array event transfer i j) 0 :=
  ((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (mixedVertex_generated (fieldUnit i) (fieldUnit j) event.momentum (-transfer) event.frame event.energy event.energy
      event.nonreal event.nonreal)

theorem actualDressedMixed289Array_entry_price (event : DressedEvent) (transfer : PhysicalMomentum) (i j : Fin 289) :
    ‖actualDressedMixed289Array event transfer i j‖ ≤
      2 * originalMixedResponsePrice (fieldUnit i) (fieldUnit j) event.momentum (-transfer) event.frame event.energy event.energy :=
  original_dressed_observer_price event _ _
    (originalMixedResponse_price (fieldUnit i) (fieldUnit j) event.momentum (-transfer) event.frame event.energy event.energy
      event.nonreal event.nonreal)

end LowEnergy.ActualSourceMixed289ResponseOwn
