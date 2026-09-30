import H0mework.Realization.Operations.SuccessorBoundary
import H0mework.Probability.SourceShift.Laplacian

/-! The original complex finite word reads into the already generated successor Hilbert action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceSuccessorBoundary

open SourceOwnedObservationHistory.SourceShift

noncomputable section

def readWord : (Nat →₀ ℂ) →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ basis

theorem readWord_single (index : Nat) (scalar : ℂ) :
    readWord (Finsupp.single index scalar) = scalar • basis index :=
  Finsupp.linearCombination_single _ _ _

theorem readWord_unit : readWord (Finsupp.single 0 (1 : ℂ)) = basis 0 := by
  rw [readWord_single, one_smul]

theorem readWord_coordinate (word : Nat →₀ ℂ) (index : Nat) : readWord word index = word index := by
  induction word using Finsupp.induction with
  | zero => simp
  | @single_add source scalar word notMem nonzero inductionHypothesis =>
      simp only [map_add, lp.coeFn_add, Pi.add_apply, Finsupp.add_apply, inductionHypothesis]
      congr 1
      simp [readWord, basis, lp.single_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

theorem readWord_injective : Function.Injective readWord := by
  intro left right equality
  apply Finsupp.ext
  intro index
  have coordinate := congrArg (fun value : H => value index) equality
  simpa only [readWord_coordinate] using coordinate

theorem readWord_push (word : Nat →₀ ℂ) : readWord (push ℂ word) = shift (readWord word) := by
  change Finsupp.linearCombination ℂ basis (Finsupp.mapDomain Nat.succ word) =
    shift.toLinearMap (Finsupp.linearCombination ℂ basis word)
  rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
  congr 1
  exact congrArg (Finsupp.linearCombination ℂ) (funext fun index => (shift_basis index).symm)

theorem readWord_boundary (word : Nat →₀ ℂ) :
    readWord (boundary ℂ word) = difference (readWord word) := by
  change readWord (push ℂ word - word) = shift (readWord word) - readWord word
  rw [map_sub, readWord_push]

end
end SourceSuccessorBoundary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
