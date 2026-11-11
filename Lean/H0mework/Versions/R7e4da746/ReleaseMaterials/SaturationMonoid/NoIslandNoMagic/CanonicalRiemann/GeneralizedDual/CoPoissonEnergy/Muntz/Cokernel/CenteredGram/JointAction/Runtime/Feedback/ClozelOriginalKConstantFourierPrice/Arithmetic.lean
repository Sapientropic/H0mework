import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierPrice.Cursor
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveActionSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceOccurrenceTransport

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierPriceArithmetic
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
namespace C
export OriginalKCombReceiptFeedback
  (Value Var receipt arithmeticSourceTrace arithmeticSourceBinding arithmeticSourceInventory bFiniteSourceTrace bSelfSourceTrace
   priorSourceCalculationInventory wholeDebtRCalculationInventory waveSourceCalculationInventory
   wholeDebtRSourceTrace wholeDebtRWaveSourceTrace sourceCalculationPriorSegment sourceCalculationInventory sourcePaidInventory)
end C
namespace Ext
export OriginalKExteriorArithmeticCalculation (Base reader code columnCode sourceAction fixedShift)
end Ext
namespace Cut
export OriginalConstantFourierPriceCursor (child cursor index occurrence occurrence_word storedValue stored_value path)
end Cut
namespace PT
export SourceOperationPaidRelations (exposure)
end PT
namespace Seg
export SourceInventoryTraceSegment (left right trans)
end Seg
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
  (native beforeStock relationTransport)
end WN
namespace ST
export OriginalKSourceOccurrenceTransport (actualSourceOccurrence actualSourceOccurrence_word)
end ST
namespace D
export OriginalKCombFirstFullSourceDynamics (factory)
end D
namespace Born
export OriginalKBFiniteCalculation.BornInventory (packetAt)
end Born
namespace R
export OriginalWholeDebtRSourceReceiptConsumer (wordMapAt)
end R
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR
namespace NW
export NativeSigma.Writeback (admissionWord)
end NW
open private relationTransport_word from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveRootSource
open private decodeMap physical_word physical_native_word from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRootSource
open private physicalValue from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextSource
attribute [local instance] OriginalKPairedWaveRootSource.levelGroups
attribute [local irreducible] AS.nativeAfterAdmission physicalValue

private theorem result_expression {N:WorldRelationNetwork} {V:Vocabulary}
    {Value Var:Unit→Type} [∀ sort,AddCommGroup (Value sort)]
    (old:SourceNativeAuthoritativeRootClosure N V)
    (read : {now : V.Current} → old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=()))
    {now:V.Current} (point:old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now) :
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt old read point).2.1.1=
      .const ((RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt old read point).2.2.1) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression old now (fun _=>read point)

namespace Cast
variable {environment:Env C.Value C.Var} {before after source target:Expr C.Value C.Var ()}
def trace (actual:Trace environment before after) (left:before=source) (right:after=target) :
    Trace environment source target := Eq.mp (congrArg₂ (Trace environment) left right) actual
theorem exposure (actual:Trace environment before after) (left:before=source) (right:after=target) :
    PT.exposure (trace actual left right)=PT.exposure actual := by
  cases left
  cases right
  rfl
def segment (actual:Trace environment before after) (left:before=source) (right:after=target) :
    SourceInventoryTraceSegment (PT.exposure (trace actual left right)) (PT.exposure actual) :=
  ⟨[],[],by rw [exposure];simp only [List.nil_append,List.append_nil]⟩
end Cast

private theorem code_closed (c:BurnolCompletedMellinCoordinate) (h:ℝ) (column:Fin 2) (cutoff:Nat)
    (binding:∀ sort,C.Var sort→Expr C.Value C.Var sort) :
    (Ext.code c h column.castSucc 0 cutoff).subst binding=Ext.code c h column.castSucc 0 cutoff := by
  fin_cases column <;> rfl
private theorem code_shape (c:BurnolCompletedMellinCoordinate) (h:ℝ) (column:Fin 2) (cutoff:Nat) :
    Ext.code c h column.castSucc 0 cutoff=
      .linear (s:=()) (t:=()) (Ext.sourceAction cutoff 0).toLinearMap.toAddMonoidHom
        (OriginalKBFiniteCalculation.lossCode h (Ext.columnCode c column)) := by
  fin_cases column <;> rfl

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat, observation.coordinate = -2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth:Nat) (column:Fin 2)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h" => Ext.fixedShift
local notation "rawTrace" => C.arithmeticSourceTrace observation nontrivial depth half column.castSucc 0
local notation "binding" => C.arithmeticSourceBinding observation nontrivial depth half column.castSucc 0
private abbrev sourceResult := runtimeExteriorArithmeticCalculationResultAt observation nontrivial depth half column.castSucc 0 depth

private theorem source_endpoint : (sourceResult observation nontrivial half depth column).2.1.1=
    .const (sourceResult observation nontrivial half depth column).2.2.1 := by
  rw [sourceResult,runtimeExteriorArithmeticCalculationResultAt_source]
  exact result_expression Ext.Base (Ext.reader observation nontrivial half column.castSucc 0 depth)
    (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence
private theorem bound_endpoint :
    ((sourceResult observation nontrivial half depth column).2.1.1.subst binding)=
      .const (sourceResult observation nontrivial half depth column).2.2.1 :=
  congrArg (fun expression=>expression.subst binding) (source_endpoint observation nontrivial half depth column)
private theorem source_raw : (sourceResult observation nontrivial half depth column).1.expression=
    Ext.code c h column.castSucc 0 depth := by
  rw [sourceResult,runtimeExteriorArithmeticCalculationResultAt_source]
  rfl
private theorem bound_raw : ((sourceResult observation nontrivial half depth column).1.expression.subst binding)=
    .linear (s:=()) (t:=()) (Ext.sourceAction depth 0).toLinearMap.toAddMonoidHom
      (OriginalKBFiniteCalculation.lossCode h (Ext.columnCode c column)) :=
  ((congrArg (fun expression=>expression.subst binding)
    (source_raw observation nontrivial half depth column)).trans
      (code_closed c h column depth binding)).trans (code_shape c h column depth)

def actualTrace := Cast.trace rawTrace (bound_raw observation nontrivial half depth column)
  (bound_endpoint observation nontrivial half depth column)
def actualChild := Cut.child h (Ext.columnCode c column) (Ext.sourceAction depth 0).toLinearMap.toAddMonoidHom
  (actualTrace observation nontrivial half depth column)
def actualCursor := Cut.cursor h (Ext.columnCode c column) (Ext.sourceAction depth 0).toLinearMap.toAddMonoidHom
  (actualTrace observation nontrivial half depth column)

private abbrev block (kind:Fin 3) (side:Fin 2) := PT.exposure (C.arithmeticSourceTrace observation nontrivial depth half kind side)
private def arithmeticSegment : SourceInventoryTraceSegment (block observation nontrivial half depth column.castSucc 0)
    (C.arithmeticSourceInventory observation nontrivial depth half) := by
  refine Fin.cases ?_ (fun index=>Fin.cases ?_ (fun impossible=>Fin.elim0 impossible) index) column
  · exact (Seg.left (block observation nontrivial half depth 0 0) (block observation nontrivial half depth 0 1)).trans
      (Seg.left
        (SourceHistoryCommon.seed (block observation nontrivial half depth 0 0) (block observation nontrivial half depth 0 1))
        (SourceHistoryCommon.seed
          (SourceHistoryCommon.seed (block observation nontrivial half depth 1 0) (block observation nontrivial half depth 1 1))
          (SourceHistoryCommon.seed (block observation nontrivial half depth 2 0) (block observation nontrivial half depth 2 1))))
  · exact ((Seg.left (block observation nontrivial half depth 1 0) (block observation nontrivial half depth 1 1)).trans
      (Seg.left
        (SourceHistoryCommon.seed (block observation nontrivial half depth 1 0) (block observation nontrivial half depth 1 1))
        (SourceHistoryCommon.seed (block observation nontrivial half depth 2 0) (block observation nontrivial half depth 2 1)))).trans
      (Seg.right
        (SourceHistoryCommon.seed (block observation nontrivial half depth 0 0) (block observation nontrivial half depth 0 1))
        (SourceHistoryCommon.seed
          (SourceHistoryCommon.seed (block observation nontrivial half depth 1 0) (block observation nontrivial half depth 1 1))
          (SourceHistoryCommon.seed (block observation nontrivial half depth 2 0) (block observation nontrivial half depth 2 1))))
def sourceSegment : SourceInventoryTraceSegment (PT.exposure (actualTrace observation nontrivial half depth column))
    (C.sourcePaidInventory observation nontrivial depth half) :=
  (Cast.segment rawTrace (bound_raw observation nontrivial half depth column) (bound_endpoint observation nontrivial half depth column)).trans
    ((arithmeticSegment observation nontrivial half depth column).trans
      ((Seg.right (SourceHistoryCommon.seed
        (PT.exposure (C.bFiniteSourceTrace observation nontrivial depth half))
        (PT.exposure (C.bSelfSourceTrace observation nontrivial depth half)))
        (C.arithmeticSourceInventory observation nontrivial depth half)).trans
        ((Seg.left (C.priorSourceCalculationInventory observation nontrivial depth half)
          (PT.exposure (C.wholeDebtRSourceTrace observation nontrivial depth half))).trans
          ((Seg.left (C.wholeDebtRCalculationInventory observation nontrivial depth half)
            (PT.exposure (C.wholeDebtRWaveSourceTrace observation nontrivial depth half))).trans
            ((C.sourceCalculationPriorSegment observation nontrivial depth half).trans
              (Seg.right (PT.exposure (C.receipt observation nontrivial depth half).2.1.2)
                (C.sourceCalculationInventory observation nontrivial depth half)))))))
def sourcePoint := (Cut.occurrence h (Ext.columnCode c column)
  (Ext.sourceAction depth 0).toLinearMap.toAddMonoidHom (actualTrace observation nontrivial half depth column)).transport
    (sourceSegment observation nontrivial half depth column)

variable (ordinal:Nat)
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "packet" => Born.packetAt observation nontrivial half depth
def actualOccurrence : WR.RelationOccurrence (WN.beforeStock native) :=
  WN.relationTransport (AS.bornAfterNative native).2.2.2.down.symm
    (ST.actualSourceOccurrence observation nontrivial half depth (sourcePoint observation nontrivial half depth column) ordinal)
theorem actual_word : (actualOccurrence observation nontrivial half depth column ordinal).word=
    ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm
      (NW.admissionWord factory (packet (ordinal+1))
        (liftMap (R:=ℤ) (R.wordMapAt observation nontrivial half depth (ordinal+1)
          (sourcePoint observation nontrivial half depth column).word))) := by
  rw [actualOccurrence,relationTransport_word,ST.actualSourceOccurrence_word]
def storedValue : BurnolL2 := physicalValue (AS.bornAfterNative native).1
  (decodeMap (remaining (actualCursor observation nontrivial half depth column).beforeExpr) Cut.path
    (actualOccurrence observation nontrivial half depth column ordinal).word)
theorem stored_child : storedValue observation nontrivial half depth column ordinal=
    (actualChild observation nontrivial half depth column).value := by
  have word := actual_word observation nontrivial half depth column ordinal
  refine (congrArg (fun item=>physicalValue (AS.bornAfterNative native).1
    (decodeMap (remaining (actualCursor observation nontrivial half depth column).beforeExpr) Cut.path item)) word).trans ?_
  refine (physical_native_word (remaining (actualCursor observation nontrivial half depth column).beforeExpr) Cut.path factory
    (packet (ordinal+1)) (R.wordMapAt observation nontrivial half depth (ordinal+1)
      (sourcePoint observation nontrivial half depth column).word)).trans ?_
  refine (physical_word observation nontrivial half depth
    (remaining (actualCursor observation nontrivial half depth column).beforeExpr) Cut.path
    (sourcePoint observation nontrivial half depth column).word (ordinal+1)).trans ?_
  exact Cut.stored_value h (Ext.columnCode c column) (Ext.sourceAction depth 0).toLinearMap.toAddMonoidHom
    (actualTrace observation nontrivial half depth column)

end OriginalConstantFourierPriceArithmetic
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierPriceArithmetic"
