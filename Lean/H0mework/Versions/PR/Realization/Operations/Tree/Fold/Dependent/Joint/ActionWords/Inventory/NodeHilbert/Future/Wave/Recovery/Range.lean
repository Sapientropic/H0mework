import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Full.Consumer
import Lean.LibrarySuggestions.Basic
-- Preserve explicit APIs while excluding complete runtime mouths from suggestion export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceFullRecovery"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace GeneratedRangeAction
universe v
variable {I J : Type v} [AddCommGroup I] [AddCommGroup J]
def advance (read : I →+ J) (source : I →+ I) (action : J →+ J)
    (square : ∀ value, action (read value)=read (source value)) :
    (LinearMap.range read.toIntLinearMap) →ₗ[ℤ] (LinearMap.range read.toIntLinearMap) :=
  ({ toFun := fun value => ⟨action value.val, by
       obtain ⟨point,same⟩ := value.property
       exact ⟨source point, (square point).symm.trans (congrArg action same)⟩⟩
     map_zero' := by apply Subtype.ext; exact action.map_zero
     map_add' := by intro left right; apply Subtype.ext; exact action.map_add _ _ } :
     (LinearMap.range read.toIntLinearMap) →+ (LinearMap.range read.toIntLinearMap)).toIntLinearMap
end GeneratedRangeAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
