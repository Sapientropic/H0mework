import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Words.Consumer
import Lean.LibrarySuggestions.Basic
-- Complete family runtime mouths use the same narrowly scoped suggestion metadata policy.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceFullOrbit"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointActionWords.Input
universe v
variable {L I H Q T : Type v} [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q] [AddCommGroup T]
def withRead (input : SourceGeneratedJointActionWords.Input L I H Q) (readMap : H →ₗ[ℤ] T)
    (actions : L → T →ₗ[ℤ] T) : SourceGeneratedJointActionWords.Input L I T Q :=
  ⟨input.integralAction,actions,input.measurementAction,readMap.comp input.coherentRead,input.measurementRead⟩
def ambientMap (input : SourceGeneratedJointActionWords.Input L I H Q) (readMap : H →ₗ[ℤ] T)
    (actions : L → T →ₗ[ℤ] T) : input.Ambient →ₗ[ℤ] (input.withRead readMap actions).Ambient :=
 ((AddMonoidHom.fst _ _).prod
   (((readMap.toAddMonoidHom.comp (AddMonoidHom.fst _ _)).prod (AddMonoidHom.snd _ _)).comp (AddMonoidHom.snd _ _))).toIntLinearMap
theorem ambientMap_word (input : SourceGeneratedJointActionWords.Input L I H Q) (readMap : H →ₗ[ℤ] T)
    (actions : L → T →ₗ[ℤ] T) (square : ∀ letter value, readMap (input.coherentAction letter value)=actions letter (readMap value))
    (word : List L) (value : input.Ambient) :
    input.ambientMap readMap actions (SourceGeneratedActionWords.run input.ambientAction word value)=
      SourceGeneratedActionWords.run (input.withRead readMap actions).ambientAction word (input.ambientMap readMap actions value) := by
 induction word generalizing value with
 | nil => rfl
 | cons first rest previous =>
   have one : input.ambientMap readMap actions (input.ambientAction first value)=
       (input.withRead readMap actions).ambientAction first (input.ambientMap readMap actions value) := by
     apply Prod.ext
     · rfl
     · apply Prod.ext
       · exact square first value.2.1
       · rfl
   exact (previous (input.ambientAction first value)).trans (congrArg (SourceGeneratedActionWords.run (input.withRead readMap actions).ambientAction rest) one)
theorem ambientMap_mem (input : SourceGeneratedJointActionWords.Input L I H Q) (readMap : H →ₗ[ℤ] T)
    (actions : L → T →ₗ[ℤ] T) (square : ∀ letter value, readMap (input.coherentAction letter value)=actions letter (readMap value))
    (value : input.Carrier) : input.ambientMap readMap actions value ∈ (input.withRead readMap actions).carrier := by
 refine Submodule.span_induction (p:=fun candidate _ => input.ambientMap readMap actions candidate ∈ (input.withRead readMap actions).carrier) ?_ ?_ ?_ ?_ value.2
 · rintro _ ⟨⟨word,event⟩,rfl⟩
   rw [generator,ambientMap_word input readMap actions square]
   exact Submodule.subset_span ⟨(word,event),rfl⟩
 · simp
 · intro left right _ _ hl hr; simpa using Submodule.add_mem _ hl hr
 · intro coefficient point _ hp; simpa using Submodule.smul_mem _ coefficient hp
def carrierMap (input : SourceGeneratedJointActionWords.Input L I H Q) (readMap : H →ₗ[ℤ] T)
    (actions : L → T →ₗ[ℤ] T) (square : ∀ letter value, readMap (input.coherentAction letter value)=actions letter (readMap value)) :
    input.Carrier →ₗ[ℤ] (input.withRead readMap actions).Carrier :=
 ((input.ambientMap readMap actions).comp input.carrier.subtype).codRestrict _ (input.ambientMap_mem readMap actions square)
end SourceGeneratedJointActionWords.Input
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
