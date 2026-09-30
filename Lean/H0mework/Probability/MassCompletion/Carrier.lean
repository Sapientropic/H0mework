import H0mework.Probability.SourceShift.Word
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! One source word supplies both its Hilbert read and its original mass in the existing product carrier. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMassCompletion

open SourceOwnedObservationHistory.SourceShift SourceSuccessorBoundary

noncomputable section

abbrev Joint := WithLp 2 (H × ℂ)

def jointRead : (Nat →₀ ℂ) →ₗ[ℂ] Joint :=
  (WithLp.linearEquiv 2 ℂ (H × ℂ)).symm.toLinearMap.comp (readWord.prod (mass ℂ))

theorem jointRead_apply (word : Nat →₀ ℂ) :
    jointRead word = WithLp.toLp 2 (readWord word, mass ℂ word) := rfl

def firstRead : Joint →L[ℂ] H := WithLp.fstL 2 ℂ H ℂ

def massRead : Joint →L[ℂ] ℂ := WithLp.sndL 2 ℂ H ℂ

theorem firstRead_source (word : Nat →₀ ℂ) : firstRead (jointRead word) = readWord word := rfl

theorem massRead_source (word : Nat →₀ ℂ) : massRead (jointRead word) = mass ℂ word := rfl

theorem jointRead_single (index : Nat) (scalar : ℂ) :
    jointRead (Finsupp.single index scalar) = WithLp.toLp 2 (scalar • basis index, scalar) := by
  rw [jointRead_apply, readWord_single, mass_single]

theorem jointRead_injective : Function.Injective jointRead := by
  intro left right equality
  exact readWord_injective (congrArg firstRead equality)

end
end SourceMassCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
