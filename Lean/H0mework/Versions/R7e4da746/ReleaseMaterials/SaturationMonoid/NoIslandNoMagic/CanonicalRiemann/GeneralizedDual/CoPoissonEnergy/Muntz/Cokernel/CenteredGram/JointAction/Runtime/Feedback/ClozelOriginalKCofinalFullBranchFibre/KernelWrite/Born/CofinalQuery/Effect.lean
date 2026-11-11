import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.RootConsumer.Consumer
import H0mework.Realization.Operations.Execution.Cochain.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint.WrittenCofinal
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open SourceGeneratedScalarDifferentialResidual
namespace CA
export ActualCofinalCommonAction
 (site siteAction receiverRead actions projection modelAction modelRead model_fibre
  model_action_source action_source_word actual_source_word_step actual_receiver_square model_read_source)
end CA
namespace F
export ActualCofinalCommonAction.T (Factory Frame Programme NativeValue Words CommonWords Value groups stageInventory)
end F
namespace Native
export ActualCofinalSourceAction (receiverOld receiverIncrement)
end Native
namespace CC
export SourceOperationExecution.Cochain (trace generated_boundary complete_charge)
end CC
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance actionGroups (grade : Nat) : ∀ target,AddCommGroup (F.Value W grade target) := F.groups W grade
variable (factory : F.Factory W X ())
variable (initial : F.Frame (Value:=W) (Var:=X) (sort:=()))
variable (cfg : F.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=()))
variable (language : cfg.LowVar=X) (ordinal : Nat)
variable (word : F.Words factory initial cfg language ordinal)

abbrev sourceOld := Native.receiverOld factory (CA.site factory initial cfg language ordinal)
abbrev sourceIncrement := Native.receiverIncrement factory (CA.site factory initial cfg language ordinal)

/-- The existing mixed-term compiler executes the complete word at this actual source receiver. -/
def sourceEffectCode := Coefficients.terms
 ((Coefficients.expression word).mixedTerms.map (fun term=>(term,(1:ℤ))))
abbrev sourceEffectEnvironment := mixedEnvironment
 (sourceOld factory initial cfg language ordinal) (sourceIncrement factory initial cfg language ordinal)
abbrev sourceEffectValue := (sourceEffectCode factory initial cfg language ordinal word).eval
 (sourceEffectEnvironment factory initial cfg language ordinal)
abbrev sourceEffectTrace := execution (sourceEffectEnvironment factory initial cfg language ordinal)
 (sourceEffectCode factory initial cfg language ordinal word)

theorem source_effect_value : sourceEffectValue factory initial cfg language ordinal word=
 effectEvaluator (R:=ℤ) (sourceOld factory initial cfg language ordinal)
  (sourceIncrement factory initial cfg language ordinal) word := by
 unfold sourceEffectValue sourceEffectCode
 rw [Coefficients.terms_eval]
 simp only [List.map_map,Function.comp_def,one_zsmul]
 exact ((Coefficients.expression word).mixedTerms_sum _ _).trans (Coefficients.expression_effect _ _ _)

theorem source_receiver_inventory :
 CA.receiverRead factory initial cfg language ordinal (CA.siteAction factory initial cfg language ordinal word)=
 (evaluation (R:=ℤ) (sourceOld factory initial cfg language ordinal) word,
  sourceEffectValue factory initial cfg language ordinal word) := by
 rw [CA.actual_receiver_square,source_effect_value]
 rfl

theorem source_inventory_inverse :
 (residualEquivRange
  (updateInventory (R:=ℤ) (sourceOld factory initial cfg language ordinal)
   (sourceIncrement factory initial cfg language ordinal))
  (canonicalResidual
   (updateInventory (R:=ℤ) (sourceOld factory initial cfg language ordinal)
    (sourceIncrement factory initial cfg language ordinal)) word)).val=
 CA.receiverRead factory initial cfg language ordinal (CA.siteAction factory initial cfg language ordinal word) :=
 (CA.actual_receiver_square factory initial cfg language ordinal word).symm

/-- No representative is discarded from the complete old/effect inverse fibre. -/
theorem source_inventory_fibre (candidate : F.Words factory initial cfg language ordinal) :
 canonicalResidual (updateInventory (R:=ℤ) (sourceOld factory initial cfg language ordinal)
  (sourceIncrement factory initial cfg language ordinal)) candidate=
 canonicalResidual (updateInventory (R:=ℤ) (sourceOld factory initial cfg language ordinal)
  (sourceIncrement factory initial cfg language ordinal)) word ↔
 evaluation (R:=ℤ) (sourceOld factory initial cfg language ordinal) candidate=
  evaluation (R:=ℤ) (sourceOld factory initial cfg language ordinal) word ∧
 effectEvaluator (R:=ℤ) (sourceOld factory initial cfg language ordinal)
  (sourceIncrement factory initial cfg language ordinal) candidate=
  sourceEffectValue factory initial cfg language ordinal word := by
 have fibre:=canonicalResidual_eq_zero_iff
  (updateInventory (R:=ℤ) (sourceOld factory initial cfg language ordinal)
   (sourceIncrement factory initial cfg language ordinal)) (candidate-word)
 simp only [map_sub,sub_eq_zero] at fibre
 exact fibre.trans (by
  change (evaluation (R:=ℤ) (sourceOld factory initial cfg language ordinal) candidate,
   effectEvaluator (R:=ℤ) (sourceOld factory initial cfg language ordinal)
    (sourceIncrement factory initial cfg language ordinal) candidate)=
   (evaluation (R:=ℤ) (sourceOld factory initial cfg language ordinal) word,
    effectEvaluator (R:=ℤ) (sourceOld factory initial cfg language ordinal)
     (sourceIncrement factory initial cfg language ordinal) word) ↔ _
  simp only [Prod.mk.injEq,source_effect_value])

theorem source_updated_residual :
 (residualEquivRange (evaluation (R:=ℤ)
   (sourceOld factory initial cfg language ordinal+sourceIncrement factory initial cfg language ordinal))
  (canonicalResidual (evaluation (R:=ℤ)
    (sourceOld factory initial cfg language ordinal+sourceIncrement factory initial cfg language ordinal)) word)).val=
 evaluation (R:=ℤ) (sourceOld factory initial cfg language ordinal) word+
  sourceEffectValue factory initial cfg language ordinal word := by
 rw [source_effect_value]
 exact updated_residual_readout _ _ _

abbrev sourceCochain := CC.trace (sourceOld factory initial cfg language ordinal)
 (sourceIncrement factory initial cfg language ordinal) word

theorem source_cochain_boundary : type_of% (CC.generated_boundary
 (sourceOld factory initial cfg language ordinal) (sourceIncrement factory initial cfg language ordinal) word) :=
 CC.generated_boundary _ _ _

theorem source_model_action :
 CA.modelAction factory initial cfg language
  (CA.projection factory initial cfg language (DFinsupp.single ordinal word))=
 CA.projection factory initial cfg language
  (DFinsupp.single (ordinal+1) (CA.siteAction factory initial cfg language ordinal word)) := by
 rw [CA.model_action_source,CA.action_source_word]

/-- The complete original Model reads every future history and every real native site after this action. -/
theorem source_model_future (history : List PUnit.{1}) (target : Nat) :
 CA.modelRead factory initial cfg language history
  (CA.modelAction factory initial cfg language
   (CA.projection factory initial cfg language (DFinsupp.single ordinal word))) target=
 F.stageInventory factory initial cfg language target
  (SourceGeneratedActionWords.run (CA.actions factory initial cfg language) history
   (DFinsupp.single (ordinal+1) (CA.siteAction factory initial cfg language ordinal word))) := by
 rw [source_model_action]
 exact CA.model_read_source _ _ _ _ _ _ _

/-- The original future-invariant Model, rather than a static kernel, supplies the entire future fibre. -/
theorem source_model_fibre (candidate : F.CommonWords factory initial cfg language) :
 CA.projection factory initial cfg language candidate=
 CA.modelAction factory initial cfg language
  (CA.projection factory initial cfg language (DFinsupp.single ordinal word)) ↔
 ∀ history : List PUnit.{1},∀ target,
 F.stageInventory factory initial cfg language target
  (SourceGeneratedActionWords.run (CA.actions factory initial cfg language) history candidate)=
 F.stageInventory factory initial cfg language target
  (SourceGeneratedActionWords.run (CA.actions factory initial cfg language) history
   (DFinsupp.single (ordinal+1) (CA.siteAction factory initial cfg language ordinal word))) := by
 rw [source_model_action]
 exact CA.model_fibre _ _ _ _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint.WrittenCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
