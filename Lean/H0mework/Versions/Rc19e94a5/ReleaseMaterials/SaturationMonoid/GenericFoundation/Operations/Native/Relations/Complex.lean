import H0mework.Versions.Rc19e94a5.Realization.Operations.Relations.Source
import H0mework.Realization.Operations.Substitution.Complex

/-! Actual paired witness, expression and value actions commute in the original presentation complex. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Relations

open CategoryTheory SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarPresentation

noncomputable section

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}

def complexMorphism (runtime : LivingRuntimeState process) :
    presentationComplex (R := ℤ) (s := PUnit.unit) (pairedEnvironment runtime.tick.next) ⟶
      presentationComplex (R := ℤ) (s := PUnit.unit) (pairedEnvironment runtime) where
  τ₁ := ModuleCat.ofHom (relationWords runtime)
  τ₂ := ModuleCat.ofHom (substitution (R := ℤ) pairedBinding)
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply ModuleCat.hom_ext
    exact boundary_square runtime
  comm₂₃ := by
    apply ModuleCat.hom_ext
    change (evaluation (R := ℤ) (s := PUnit.unit) (pairedEnvironment runtime)).comp
      (substitution (R := ℤ) pairedBinding) =
        evaluation (R := ℤ) (pairedEnvironment runtime.tick.next)
    rw [evaluation_substitution]
    exact congrArg (evaluation (R := ℤ) (s := PUnit.unit)) (actual_environment runtime)

end
end SourceOperationNative.Relations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
