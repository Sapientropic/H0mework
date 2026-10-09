import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Branch.Recovery
import H0mework.Realization.Operations.Substitution.Complex
import Lean.LibrarySuggestions.Basic
-- Complete relation/query signatures use a local suggestion metadata exclusion.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceIncidenceRelations"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualRelationSubstitution
universe v
open SourceOperationEffects SourceOperationScalarPresentation SourceOperationScalarRelations
variable {S : Type v} {A X : S → Type v} [∀ s,AddCommGroup (A s)]
variable (binding : ∀ s,X s → Expr A X s) (before after : Env A X)
variable (same : SourceSubstitution.sourceEnvironment binding before=after)
private def retarget {s : S} (generator : RelationIndex ℤ after s) : RelationIndex ℤ (SourceSubstitution.sourceEnvironment binding before) s := same.symm ▸ generator
private theorem boundary {s : S} (generator : RelationIndex ℤ after s) :
    relation (R:=ℤ) (SourceSubstitution.sourceEnvironment binding before) (retarget binding before after same generator)=
      relation (R:=ℤ) after generator := by cases same; rfl
def index {s : S} (generator : RelationIndex ℤ after s) : RelationIndex ℤ before s :=
 SourceSubstitution.index binding before (retarget binding before after same generator)
theorem index_boundary {s : S} (generator : RelationIndex ℤ after s) :
    relation (R:=ℤ) before (index binding before after same generator)=
      substitution (R:=ℤ) binding (relation (R:=ℤ) after generator) :=
 (SourceSubstitution.index_boundary binding before (retarget binding before after same generator)).trans
   (congrArg (substitution (R:=ℤ) binding) (boundary binding before after same generator))
end ActualRelationSubstitution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
