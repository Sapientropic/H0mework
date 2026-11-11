import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierPrice.Arithmetic

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCompleteFeeKernelReceipt
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
namespace P
export OriginalKPrimitiveMobiusSourceCalculation (Value Var code spread)
end P
namespace BS
export OriginalKCoefficientBSelfCalculation (sourceKernelCode)
end BS
namespace C
export OriginalKCombReceiptFeedback
  (Value Var receipt wholeDebtRPrimitiveMobiusSourceCode wholeDebtRPrimitiveMobiusSourceTrace
   wholeDebtRPrimitiveMobiusSourceValue primitiveMobiusSourceSegment sourcePaidInventory)
end C
namespace PT
export SourceOperationPaidRelations (words complete_steps stepOccurrence stepOccurrence_word exposure)
end PT
namespace Cast
export OriginalConstantFourierPriceArithmetic.Cast (trace segment)
end Cast
open private childAt decodeMap physical_word physical_native_word from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRootSource
open private last_before left_before word_at from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierPrice.Cursor
open private relationTransport_word from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveRootSource
open private physicalValue from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextSource
attribute [local instance] OriginalKPairedWaveRootSource.levelGroups
attribute [local irreducible] AS.nativeAfterAdmission physicalValue

namespace Traced
variable (c:BurnolCompletedMellinCoordinate)
variable {env:Env P.Value P.Var} {total:BurnolL2}
variable (actual:Trace env (P.code c 2) (.const total))
noncomputable def outer := Trace.splitAdd actual
noncomputable def mobius := Trace.splitLinear (outer c actual).leftTrace
noncomputable def dilation := Trace.splitLinear (mobius c actual).trace
noncomputable def unit := Trace.splitAdd (dilation c actual).trace
noncomputable def constantUnit := Trace.splitLinear (unit c actual).leftTrace
noncomputable def fourier := Trace.splitLinear (constantUnit c actual).trace
noncomputable def child : Trace.SourceReceipt actual (BS.sourceKernelCode c) :=
  ⟨(fourier c actual).input,(fourier c actual).trace,
    .left (outer c actual) (.linear (mobius c actual) (.linear (dilation c actual)
      (.left (unit c actual) (.linear (constantUnit c actual)
        (.linear (fourier c actual) (.refl _))))))⟩
noncomputable def cursor : Trace.Cursor actual :=
  (outer c actual).interleaving.leftCursor
    ((mobius c actual).interleaving.liftCursor
      ((dilation c actual).interleaving.liftCursor
        ((unit c actual).interleaving.leftCursor
          ((constantUnit c actual).interleaving.liftCursor
            (fourier c actual).interleaving.lastCursor))))
def path : List Bool := [false,false,false,false,false,false]
set_option backward.isDefEq.respectTransparency false in
theorem cursor_stored : childAt path (cursor c actual).beforeExpr=.const (child c actual).value := by
  unfold cursor
  rw [left_before,Trace.LinearInterleaving.liftCursor_before,
    Trace.LinearInterleaving.liftCursor_before,left_before,
    Trace.LinearInterleaving.liftCursor_before,last_before]
  rfl
noncomputable def index : Fin (PT.words actual).length :=
  ⟨(cursor c actual).position,by rw [PT.complete_steps];exact (cursor c actual).position_lt⟩
noncomputable def occurrence := PT.stepOccurrence actual (index c actual)
theorem occurrence_word : (occurrence c actual).word=relation (R:=ℤ) env
    (.inl ⟨(cursor c actual).beforeExpr,(cursor c actual).afterExpr,(cursor c actual).paidStep.toDerivation⟩) :=
  word_at (cursor c actual)
noncomputable def storedValue : BurnolL2 := decodeMap (remaining (cursor c actual).beforeExpr) path
  (occurrence c actual).word
theorem stored_value : storedValue c actual=(child c actual).value := by
  unfold storedValue
  rw [occurrence_word]
  exact OriginalConstantFourierPriceCursor.CursorRead.decode_before (cursor c actual).paidStep path
    (child c actual).value (cursor_stored c actual)
theorem child_address : (child c actual).retained.address=[0,2,2,0,2,2] := rfl
end Traced

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

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth:Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "rawTrace" => C.wholeDebtRPrimitiveMobiusSourceTrace observation nontrivial depth half 2
private theorem raw_source : C.wholeDebtRPrimitiveMobiusSourceCode observation nontrivial depth half 2=P.code c 2 := rfl
noncomputable def actualTrace := Cast.trace rawTrace (raw_source observation nontrivial half depth) rfl
noncomputable def actualChild := Traced.child c (actualTrace observation nontrivial half depth)
noncomputable def actualCursor := Traced.cursor c (actualTrace observation nontrivial half depth)
noncomputable def sourceSegment : SourceInventoryTraceSegment (PT.exposure (actualTrace observation nontrivial half depth))
    (C.sourcePaidInventory observation nontrivial depth half) :=
  (Cast.segment rawTrace (raw_source observation nontrivial half depth) rfl).trans
    (C.primitiveMobiusSourceSegment observation nontrivial depth half 2)
noncomputable def sourcePoint := (Traced.occurrence c (actualTrace observation nontrivial half depth)).transport
  (sourceSegment observation nontrivial half depth)

variable (ordinal:Nat)
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "packet" => Born.packetAt observation nontrivial half depth
noncomputable def actualOccurrence : WR.RelationOccurrence (WN.beforeStock native) :=
  WN.relationTransport (AS.bornAfterNative native).2.2.2.down.symm
    (ST.actualSourceOccurrence observation nontrivial half depth (sourcePoint observation nontrivial half depth) ordinal)
theorem actual_word : (actualOccurrence observation nontrivial half depth ordinal).word=
    ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm
      (NW.admissionWord factory (packet (ordinal+1))
        (liftMap (R:=ℤ) (R.wordMapAt observation nontrivial half depth (ordinal+1)
          (sourcePoint observation nontrivial half depth).word))) := by
  rw [actualOccurrence,relationTransport_word,ST.actualSourceOccurrence_word]
noncomputable def storedValue : BurnolL2 := physicalValue (AS.bornAfterNative native).1
  (decodeMap (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path
    (actualOccurrence observation nontrivial half depth ordinal).word)
theorem stored_child : storedValue observation nontrivial half depth ordinal=
    (actualChild observation nontrivial half depth).value := by
  have word:=actual_word observation nontrivial half depth ordinal
  refine (congrArg (fun item=>physicalValue (AS.bornAfterNative native).1
    (decodeMap (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path item)) word).trans ?_
  refine (physical_native_word (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path factory
    (packet (ordinal+1)) (R.wordMapAt observation nontrivial half depth (ordinal+1)
      (sourcePoint observation nontrivial half depth).word)).trans ?_
  refine (physical_word observation nontrivial half depth
    (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path
    (sourcePoint observation nontrivial half depth).word (ordinal+1)).trans ?_
  exact Traced.stored_value c (actualTrace observation nontrivial half depth)

end OriginalCompleteFeeKernelReceipt
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalCompleteFeeKernelReceipt"
