import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalRResidualInverse.Qualification
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Relations.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Calc
export OriginalKDirectRCofinalCalculatedSource
 (calculationRoot calculationCurrent calculationReader originalNormal originalFrontier calculatedState calculatedValue
  calculated_full_R_branches actual_material_calculated_state actual_material_calculated_history)
end Calc
namespace Own
export RootGeneratedDebtActivationJointSource.OwnerFree (raw mathFace runtimeCurrent)
namespace Rel
export RootGeneratedDebtActivationJointSource.OwnerFree.Relations
 (sourceFace current exposure evaluator history evaluationFace relations_sound word_read disposition OutputAt output
  coversAt_factorizes tick_equation_and_whole_next)
end Rel
end Own
namespace D
export OriginalKCombFirstFullSourceDynamics (packet input)
end D
namespace CF
export OriginalKCombFullResidualAction.CF (collapseValue)
end CF
namespace L
export OriginalKCombFirstFullSourceDynamics.L (Value groups)
end L
namespace C
export OriginalKCombReceiptFeedback (Value)
end C
local instance relationGroups (grade : Nat) : ∀ target,
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

abbrev sourceRoot := Calc.calculationRoot observation nontrivial half depth ordinal
abbrev sourceCurrent := Calc.calculationCurrent observation nontrivial half depth ordinal
abbrev sourceReader := Calc.calculationReader observation nontrivial half depth ordinal
abbrev sourceRuntime : RootGeneratedDebtActivationJointSource.OwnerFree.Runtime
 (sourceRoot observation nontrivial half depth ordinal) (sourceCurrent observation nontrivial half depth ordinal)
 (sourceReader observation nontrivial half depth ordinal) :=
 (Calc.originalNormal observation nontrivial half depth ordinal).targetRuntime

/-- This is the relation coordinate already installed in the actual calculation runtime. -/
abbrev sourceFace := Own.Rel.sourceFace (sourceRoot observation nontrivial half depth ordinal)
 (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)
 (sourceRuntime observation nontrivial half depth ordinal)
abbrev sourceHistory := Own.Rel.history (sourceRoot observation nontrivial half depth ordinal)
 (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)
 (sourceRuntime observation nontrivial half depth ordinal)
abbrev sourceEvaluation := Own.Rel.evaluationFace (sourceRoot observation nontrivial half depth ordinal)
 (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)
 (sourceRuntime observation nontrivial half depth ordinal)

theorem sourceSound : GeneratedRelationSoundnessAt (sourceEvaluation observation nontrivial half depth ordinal) := by
 cases (sourceEvaluation observation nontrivial half depth ordinal).settleRelations with
 | sound receipt => exact receipt
 | unsound obstruction =>
  exact False.elim (obstruction.notSound
   (Own.Rel.relations_sound (sourceRoot observation nontrivial half depth ordinal)
    (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)
    (sourceRuntime observation nontrivial half depth ordinal)))

def collapseLinear (grade : Nat) :
 PairValue (L.Value (PairValue C.Value) grade) () →ₗ[ℤ] Branches :=
 AddMonoidHom.toIntLinearMap {
  toFun := CF.collapseValue grade
  map_zero' := by
   induction grade with
   | zero => rfl
   | succ grade previous =>
    change CF.collapseValue grade (0+0)=0
    simpa only [add_zero] using previous
  map_add' := OriginalRResidualInverse.collapse_add grade }

abbrev SourceCompletion := (sourceHistory observation nontrivial half depth ordinal).CompletionCarrier

/-- The map consumes the source face's sound evaluator. No target value or quotient equivalence is supplied. -/
def factor : SourceCompletion observation nontrivial half depth ordinal →ₗ[ℤ]
 SourceModel observation nontrivial half :=
 ((H.projection (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)).restrictScalars ℤ).comp
  (((branchReadback observation nontrivial half).restrictScalars ℤ).comp
   ((collapseLinear (D.packet observation nontrivial half depth ordinal).1).comp
    ((sourceEvaluation observation nontrivial half depth ordinal).completionEvaluation
     (sourceSound observation nontrivial half depth ordinal))))

theorem factor_source_word (word : (sourceHistory observation nontrivial half depth ordinal).generatorClosure) :
 factor observation nontrivial half depth ordinal
  ((sourceHistory observation nontrivial half depth ordinal).completionProjection word)=
 H.projection (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)
  (branchReadback observation nontrivial half
   (CF.collapseValue (D.packet observation nontrivial half depth ordinal).1
    (evaluation (R:=ℤ)
     (Own.raw (sourceRoot observation nontrivial half depth ordinal)
      (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)).environment word.val))) := by
 change H.projection _ _ (branchReadback _ _ _
  (CF.collapseValue _ ((sourceEvaluation observation nontrivial half depth ordinal).completionEvaluation
   (sourceSound observation nontrivial half depth ordinal) (Submodule.Quotient.mk word))))=_
 rw [completionEvaluation_mk]
 change H.projection _ _ (branchReadback _ _ _
  (CF.collapseValue _ ((sourceEvaluation observation nontrivial half depth ordinal).freeEvaluation word.val)))=_
 rw [Own.Rel.word_read]

theorem source_generator_mem :
 Finsupp.single
  (Own.raw (sourceRoot observation nontrivial half depth ordinal)
   (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)).expression (1:ℤ) ∈
 (sourceHistory observation nontrivial half depth ordinal).generatorClosure := by
 classical
 apply (sourceHistory observation nontrivial half depth ordinal).generatorStage_le_closure 0
 apply Finsupp.single_mem_supported
 change _ ∈ (sourceHistory observation nontrivial half depth ordinal).generatorSupport 0
 simp only [CofinalHistorySettlement.RootGeneratedCofinalHistoryAt.generatorSupport,
  List.mem_toFinset,List.mem_flatMap]
 refine ⟨PresentedRelationEventAt.generator
  (Own.raw (sourceRoot observation nontrivial half depth ordinal)
   (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)).expression,?_,?_⟩
 · change PresentedRelationEventAt.generator
    (Own.raw (sourceRoot observation nontrivial half depth ordinal)
     (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)).expression ∈
    PresentedRelationEventAt.generator
    (Own.raw (sourceRoot observation nontrivial half depth ordinal)
     (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)).expression :: _
   exact List.mem_cons_self
 · simp only [PresentedRelationEventAt.support,Finset.mem_toList,Finset.mem_singleton]

def sourceGenerator : (sourceHistory observation nontrivial half depth ordinal).generatorClosure :=
 ⟨Finsupp.single
  (Own.raw (sourceRoot observation nontrivial half depth ordinal)
   (sourceCurrent observation nontrivial half depth ordinal) (sourceReader observation nontrivial half depth ordinal)).expression 1,
  source_generator_mem observation nontrivial half depth ordinal⟩
def sourceClass : SourceCompletion observation nontrivial half depth ordinal :=
 (sourceHistory observation nontrivial half depth ordinal).completionProjection
  (sourceGenerator observation nontrivial half depth ordinal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
