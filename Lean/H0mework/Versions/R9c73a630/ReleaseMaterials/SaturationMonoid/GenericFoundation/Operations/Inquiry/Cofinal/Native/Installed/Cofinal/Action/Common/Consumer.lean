import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualCofinalCommonAction"

/-! The already generated future-invariant model consumes the original common
source action. It restricts to the existing native joint completion and
retains the actual receiver word square and complete source span. Static
native observation kernels need no assumed action stability. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalCommonAction
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual CategoryTheory
namespace I
export SourceInquiryCofinalDiagram.Admission (source_span)
end I
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target,AddCommGroup (W target)] {s : Sorts}
local instance consumerGroups (grade : Nat) (target : Sorts) : AddCommGroup (T.Value W grade target) := T.groups W grade target
variable (factory : T.Factory W X s)
variable (initial : T.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : T.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

/-- Future invisibility includes the original current native observations. -/
private theorem future_kernel_native
 (word : T.CommonWords factory initial cfg language)
 (invisible : word ∈ LinearMap.ker
  (SourceGeneratedActionObservationHistory.sourceMap
   (actions factory initial cfg language PUnit.unit)
   (SourceGeneratedActionWords.inventory (actions factory initial cfg language)
    (jointObserver factory initial cfg language)))) :
 (T.sourceMap factory initial cfg language).hom word = 0 := by
 rw [SourceGeneratedActionWords.original_kernel] at invisible
 have every := LinearMap.mem_ker.mp invisible
 apply (T.completion_zero_iff factory initial cfg language word).mpr
 intro ordinal
 exact congrFun (congrFun every []) ordinal

/-- The generated model keeps a lawful restriction to the original full joint fibre. -/
def nativeRestriction : Model factory initial cfg language →ₗ[ℤ]
 ActualCofinalNativeTower.Completion factory initial cfg language :=
 (LinearMap.ker (SourceGeneratedActionObservationHistory.sourceMap
  (actions factory initial cfg language PUnit.unit)
  (SourceGeneratedActionWords.inventory (actions factory initial cfg language)
   (jointObserver factory initial cfg language)))).liftQ
  (T.sourceMap factory initial cfg language).hom (fun word invisible =>
   (LinearMap.mem_ker.mpr (future_kernel_native factory initial cfg language word invisible)))

theorem native_restriction_source (word : T.CommonWords factory initial cfg language) :
 nativeRestriction factory initial cfg language (projection factory initial cfg language word) =
 (T.sourceMap factory initial cfg language).hom word := rfl

/-- The next native residual is read from the generated model action, without descending a static kernel. -/
theorem model_action_native (word : T.CommonWords factory initial cfg language) :
 nativeRestriction factory initial cfg language
  (modelAction factory initial cfg language (projection factory initial cfg language word)) =
 (T.sourceMap factory initial cfg language).hom (action factory initial cfg language word) := by
 rw [model_action_source,native_restriction_source]

/-- The actual source acts on every full word, while the original complete state follows its whole span. -/
theorem actual_source_word_step (ordinal : Nat)
 (word : T.Words factory initial cfg language ordinal)
 (member : WordInInventory (site factory initial cfg language ordinal) word) :
 type_of% (I.source_span factory initial cfg language ordinal) ∧
 WordInInventory (site factory initial cfg language (ordinal+1))
  (siteAction factory initial cfg language ordinal word) ∧
 modelAction factory initial cfg language
  (projection factory initial cfg language (DFinsupp.single ordinal word)) =
 projection factory initial cfg language
  (DFinsupp.single (ordinal+1) (siteAction factory initial cfg language ordinal word)) ∧
 receiverRead factory initial cfg language ordinal
  (T.component factory initial cfg language (ordinal+1)
   (action factory initial cfg language (DFinsupp.single ordinal word))) =
 updateInventory (R := ℤ) (A.receiverOld factory (site factory initial cfg language ordinal))
  (A.receiverIncrement factory (site factory initial cfg language ordinal)) word := by
 refine ⟨I.source_span factory initial cfg language ordinal,
  site_action_inventory factory initial cfg language ordinal word member,?_,?_⟩
 · rw [model_action_source,action_source_word]
 · rw [action_next_component]
   exact actual_receiver_square factory initial cfg language ordinal word

/-- The original allowed-action-word consumer reads every actual future source operation. -/
def modelRead (word : List PUnit.{u+1}) :=
 SourceGeneratedActionWords.readout (actions factory initial cfg language)
  (jointObserver factory initial cfg language) PUnit.unit word

theorem model_read_source (history : List PUnit.{u+1})
 (word : T.CommonWords factory initial cfg language) (ordinal : Nat) :
 modelRead factory initial cfg language history (projection factory initial cfg language word) ordinal =
 T.stageInventory factory initial cfg language ordinal
  (SourceGeneratedActionWords.run (actions factory initial cfg language) history word) :=
 congrFun (SourceGeneratedActionWords.readout_source _ _ _ history word) ordinal

theorem model_read_action (history : List PUnit.{u+1})
 (value : Model factory initial cfg language) (ordinal : Nat) :
 modelRead factory initial cfg language history (modelAction factory initial cfg language value) ordinal =
 modelRead factory initial cfg language (PUnit.unit :: history) value ordinal :=
 congrFun (SourceGeneratedActionWords.letter_readout _ _ _ PUnit.unit history value) ordinal

end ActualCofinalCommonAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
