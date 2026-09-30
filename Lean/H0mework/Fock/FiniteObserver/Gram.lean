import H0mework.Fock.HistoryConditional.WindowPosteriorMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObserverCalculation

open SourceCopyProgram (Index)
open SourceGeneratedAcquisitionContinuation
open SourceCopyTimeModel (hilbert mass)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

theorem physical_gram (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (left right : Nat) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index left, SourceColumnForcing.column (inventoryBound runtime) index right⟫_ℂ =
      (if left = right then 1 else 0) + 1 +
        (((index.val + 1 : Nat) : ℂ) ^ 2 * ((left + 1 : Nat) : ℂ) * ((right + 1 : Nat) : ℂ)) := by
  have source := (SourceCopyGraph.action (inventoryBound runtime) index).adjoint_inner_left
    (SourceJointClockGraph.read (Finsupp.single right (1 : ℂ)))
    (SourceColumnForcing.column (inventoryBound runtime) index left)
  change ⟪SourceWindowPrecision.cotest runtime index left, SourceJointClockGraph.read (Finsupp.single right (1 : ℂ))⟫_ℂ =
    ⟪SourceColumnForcing.column (inventoryBound runtime) index left, SourceColumnForcing.column (inventoryBound runtime) index right⟫_ℂ at source
  rw [← source, SourceWindowPrecision.cotest_pairing]
  change SourceSuccessorBoundary.readWord (Finsupp.single right (1 : ℂ)) left +
    SourceSuccessorBoundary.mass ℂ (Finsupp.single right (1 : ℂ)) +
      (((index.val + 1 : Nat) : ℂ) ^ 2 * ((left + 1 : Nat) : ℂ)) * SourceClockComplex.clock (Finsupp.single right (1 : ℂ)) = _
  rw [SourceSuccessorBoundary.readWord_coordinate, SourceSuccessorBoundary.mass_single, SourceClockComplex.clock_single, one_mul]
  simp only [Finsupp.single_apply, SourceClockModel.rawClock, Int.cast_add, Int.cast_natCast, Int.cast_one]
  by_cases same : left = right
  · subst right
    simp
  · simp [same, Ne.symm same]

end
end SourceFiniteObserverCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
