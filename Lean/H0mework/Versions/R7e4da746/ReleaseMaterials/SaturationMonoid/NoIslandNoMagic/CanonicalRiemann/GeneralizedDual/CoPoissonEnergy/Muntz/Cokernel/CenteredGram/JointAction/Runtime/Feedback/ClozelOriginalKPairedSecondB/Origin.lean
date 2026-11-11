import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSecondBContact.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompleteContactPrice.KernelReceipt
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJointMobiusSourceFields

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalPairedSecondBOrigin
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation
open CofinalHistorySettlement
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
namespace P
export OriginalKJointMobiusSourceCalculation (Value Var code sourceCode fixedShift)
end P
namespace BS
export OriginalKCoefficientBSelfCalculation (sourceKernelCode)
end BS
namespace C
export OriginalKCombReceiptFeedback
  (Value Var receipt wholeDebtRJointMobiusSourceCode wholeDebtRJointMobiusSourceTrace jointMobiusSourceSegment sourcePaidInventory)
end C
namespace PT
export SourceOperationPaidRelations (words complete_steps stepOccurrence stepOccurrence_word exposure)
end PT
namespace JOcc
export OriginalKJointMobiusSourceOccurrences (actualOccurrence actual_word actual_before_length)
end JOcc
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
  (native beforeStock relationTransport)
end WN
namespace Born
export OriginalKBFiniteCalculation.BornInventory (packetAt)
end Born
namespace D
export OriginalKCombFirstFullSourceDynamics (factory)
end D
namespace R
export OriginalWholeDebtRSourceReceiptConsumer (wordMapAt)
end R
namespace NW
export NativeSigma.Writeback (admissionWord)
end NW
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR
open private childAt decodeMap physical_word physical_native_word from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRootSource
open private last_before word_at from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierPrice.Cursor
open private relationTransport_word from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveRootSource
open private physicalValue from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextSource
attribute [local instance] OriginalKPairedWaveRootSource.levelGroups
attribute [local irreducible] AS.nativeAfterAdmission physicalValue

namespace RightCut
variable {environment:Env P.Value P.Var}
private def cursor {left right:Expr P.Value P.Var ()} {total leftValue rightValue:BurnolL2}
    {actual:Trace environment (.add left right) (.const total)}
    {leftTrace:Trace environment left (.const leftValue)} {rightTrace:Trace environment right (.const rightValue)}
    (interleaving:Trace.AddInterleaving environment actual leftTrace rightTrace)
    (inside:Trace.Cursor rightTrace) : Trace.Cursor actual :=
  match interleaving,inside with
  | .last _ _, impossible => nomatch impossible
  | .left paid tail, inner => .there (.addLeft paid) _ (cursor tail inner)
  | .right paid tail, .here _ _ => .here (.addRight paid) _
  | .right paid tail, .there _ _ inner => .there (.addRight paid) _ (cursor tail inner)
private def leftAt {left right:Expr P.Value P.Var ()} {total leftValue rightValue:BurnolL2}
    {actual:Trace environment (.add left right) (.const total)}
    {leftTrace:Trace environment left (.const leftValue)} {rightTrace:Trace environment right (.const rightValue)}
    (interleaving:Trace.AddInterleaving environment actual leftTrace rightTrace)
    (inside:Trace.Cursor rightTrace) : Expr P.Value P.Var () :=
  match interleaving,inside with
  | .last _ _, impossible => nomatch impossible
  | .left _ tail, inner => leftAt tail inner
  | .right (left:=left) _ _, .here _ _ => left
  | .right _ tail, .there _ _ inner => leftAt tail inner
private theorem before {left right:Expr P.Value P.Var ()} {total leftValue rightValue:BurnolL2}
    {actual:Trace environment (.add left right) (.const total)}
    {leftTrace:Trace environment left (.const leftValue)} {rightTrace:Trace environment right (.const rightValue)}
    (interleaving:Trace.AddInterleaving environment actual leftTrace rightTrace) (inside:Trace.Cursor rightTrace) :
    (cursor interleaving inside).beforeExpr=.add (leftAt interleaving inside) inside.beforeExpr := by
  induction interleaving with
  | last => cases inside
  | left paid tail previous => exact previous inside
  | right paid tail previous =>
      cases inside with
      | here => rfl
      | there _ _ inner => exact previous inner
private theorem step {left right:Expr P.Value P.Var ()} {total leftValue rightValue:BurnolL2}
    {actual:Trace environment (.add left right) (.const total)}
    {leftTrace:Trace environment left (.const leftValue)} {rightTrace:Trace environment right (.const rightValue)}
    (interleaving:Trace.AddInterleaving environment actual leftTrace rightTrace) (inside:Trace.Cursor rightTrace) :
    HEq (cursor interleaving inside).paidStep (Step.addRight (left:=leftAt interleaving inside) inside.paidStep) := by
  induction interleaving with
  | last => cases inside
  | left paid tail previous => exact previous inside
  | right paid tail previous =>
      cases inside with
      | here => rfl
      | there _ _ inner => exact previous inner
private theorem position {left right:Expr P.Value P.Var ()} {total leftValue rightValue:BurnolL2}
    {actual:Trace environment (.add left right) (.const total)}
    {leftTrace:Trace environment left (.const leftValue)} {rightTrace:Trace environment right (.const rightValue)}
    (interleaving:Trace.AddInterleaving environment actual leftTrace rightTrace) (inside:Trace.Cursor rightTrace) :
    (cursor interleaving inside).position=interleaving.rightPositions[inside.position]'(by
      rw [interleaving.rightPositions_length];exact inside.position_lt) := by
  induction interleaving with
  | last => cases inside
  | left paid tail previous =>
      simp only [cursor,Trace.Cursor.position,Trace.AddInterleaving.rightPositions,List.getElem_map]
      exact congrArg Nat.succ (previous inside)
  | right paid tail previous =>
      cases inside with
      | here => rfl
      | there _ _ inner =>
          simp only [cursor,Trace.Cursor.position,Trace.AddInterleaving.rightPositions,
            List.getElem_cons_succ,List.getElem_map]
          exact congrArg Nat.succ (previous inner)
end RightCut

namespace Traced
def path : List Bool := [false,true,false]
def pairedCode (c:BurnolCompletedMellinCoordinate) : Expr P.Value P.Var () := childAt path (P.code c)
variable (c:BurnolCompletedMellinCoordinate) {env:Env P.Value P.Var} {total:BurnolL2}
variable (actual:Trace env (P.code c) (.const total))
noncomputable def outer := Trace.splitLinear actual
noncomputable def boundary := Trace.splitAdd (outer c actual).trace
noncomputable def negative := Trace.splitLinear (boundary c actual).rightTrace
noncomputable def half := Trace.splitLinear (negative c actual).trace
noncomputable def sum := Trace.splitAdd (half c actual).trace
noncomputable def plus := Trace.splitLinear (sum c actual).leftTrace
noncomputable def minus := Trace.splitLinear (sum c actual).rightTrace
noncomputable def boundaryReceipt : Trace.SourceReceipt actual (P.sourceCode c) :=
  ⟨(outer c actual).input,(outer c actual).trace,.linear (outer c actual) (.refl _)⟩
noncomputable def child : Trace.SourceReceipt actual (pairedCode c) :=
  ⟨(negative c actual).input,(negative c actual).trace,
    .linear (outer c actual) (.right (boundary c actual) (.linear (negative c actual) (.refl _)))⟩
noncomputable def plusKernel : Trace.SourceReceipt actual (BS.sourceKernelCode c) :=
  ⟨(plus c actual).input,(plus c actual).trace,
    .linear (outer c actual) (.right (boundary c actual) (.linear (negative c actual)
      (.linear (half c actual) (.left (sum c actual) (.linear (plus c actual) (.refl _))))))⟩
noncomputable def minusKernel : Trace.SourceReceipt actual (BS.sourceKernelCode c) :=
  ⟨(minus c actual).input,(minus c actual).trace,
    .linear (outer c actual) (.right (boundary c actual) (.linear (negative c actual)
      (.linear (half c actual) (.right (sum c actual) (.linear (minus c actual) (.refl _))))))⟩
noncomputable def cursor : Trace.Cursor actual :=
  (outer c actual).interleaving.liftCursor
    (RightCut.cursor (boundary c actual).interleaving (negative c actual).interleaving.lastCursor)
set_option backward.isDefEq.respectTransparency false in
theorem cursor_stored : childAt path (cursor c actual).beforeExpr=.const (child c actual).value := by
  unfold cursor
  rw [Trace.LinearInterleaving.liftCursor_before,RightCut.before,last_before]
  rfl
noncomputable def index : Fin (PT.words actual).length :=
  ⟨(cursor c actual).position,by rw [PT.complete_steps];exact (cursor c actual).position_lt⟩
noncomputable def occurrence := PT.stepOccurrence actual (index c actual)
theorem occurrence_word : (occurrence c actual).word=relation (R:=ℤ) env
    (.inl ⟨(cursor c actual).beforeExpr,(cursor c actual).afterExpr,(cursor c actual).paidStep.toDerivation⟩) :=
  word_at (cursor c actual)
noncomputable def storedValue : BurnolL2 := decodeMap (remaining (cursor c actual).beforeExpr) path (occurrence c actual).word
theorem stored_value : storedValue c actual=(child c actual).value := by
  unfold storedValue
  rw [occurrence_word]
  exact OriginalConstantFourierPriceCursor.CursorRead.decode_before (cursor c actual).paidStep path
    (child c actual).value (cursor_stored c actual)
theorem child_address : (child c actual).retained.address=[2,1,2] := rfl
theorem plus_kernel_actual : (plusKernel c actual).value=(burnolCompletedMellinRieszVector c:BurnolL2) :=
  OriginalCompleteFeeInput.Kernel.kernel_actual c (plusKernel c actual).trace
theorem minus_kernel_actual : (minusKernel c actual).value=(burnolCompletedMellinRieszVector c:BurnolL2) :=
  OriginalCompleteFeeInput.Kernel.kernel_actual c (minusKernel c actual).trace
theorem child_actual : (child c actual).value=OriginalKPairedBEulerJunctionSource.sourceAction c := by
  have read : (child c actual).value=pairedBurnolMultiplicativeDilation P.fixedShift
      ((BS.sourceKernelCode c).eval env) := (child c actual).trace.sound.symm
  exact read.trans (congrArg (pairedBurnolMultiplicativeDilation P.fixedShift)
    ((plusKernel c actual).trace.sound.trans (plus_kernel_actual c actual)))
variable {value:BurnolL2} {whole part:Expr P.Value P.Var ()}
variable {trace:Trace env whole (.const value)}
private noncomputable def repoint (receipt:Trace.SourceReceipt trace part) (point:BurnolL2)
    (same:point=receipt.value) : Trace.SourceReceipt trace part := by
  refine ⟨point,Eq.mp (congrArg (fun v=>Trace env part (.const v)) same.symm) receipt.trace,?_⟩
  cases same
  exact receipt.retained
private theorem repoint_value (receipt:Trace.SourceReceipt trace part) (point:BurnolL2)
    (same:point=receipt.value) : (repoint receipt point same).value=point := rfl
end Traced
run_cmd IO.eprintln "paired-B Origin: generic stored child complete"

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ) (N:Nat)
local notation "c"=>OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "rawTrace"=>C.wholeDebtRJointMobiusSourceTrace observation nontrivial depth half 0
local notation "native"=>WN.native observation nontrivial half depth ordinal
local notation "factory"=>D.factory observation nontrivial half
local notation "packet"=>Born.packetAt observation nontrivial half depth
noncomputable def parentTrace : Trace (C.receipt observation nontrivial depth half).1.environment (P.code c)
    (.const (OriginalKJointMobiusSourceWriteback.actualValue observation nontrivial half depth 0)) := rawTrace
noncomputable def boundaryReceipt := Traced.boundaryReceipt c (parentTrace observation nontrivial half depth)
noncomputable def actualChild := Traced.child c (parentTrace observation nontrivial half depth)
noncomputable def plusKernelReceipt := Traced.plusKernel c (parentTrace observation nontrivial half depth)
noncomputable def minusKernelReceipt := Traced.minusKernel c (parentTrace observation nontrivial half depth)
noncomputable def actualCursor := Traced.cursor c (parentTrace observation nontrivial half depth)
noncomputable def actualIndex : OriginalKJointMobiusSourceOccurrences.Index observation nontrivial half depth 0 :=
  Traced.index c (parentTrace observation nontrivial half depth)
theorem actual_index_position : (actualIndex observation nontrivial half depth).val=(actualCursor observation nontrivial half depth).position := rfl
noncomputable def actualOccurrence : WR.RelationOccurrence (WN.beforeStock native) :=
  WN.relationTransport (AS.bornAfterNative native).2.2.2.down.symm
    (JOcc.actualOccurrence observation nontrivial half depth ordinal 0 (actualIndex observation nontrivial half depth))
noncomputable abbrev actual_word : (actualOccurrence observation nontrivial half depth ordinal).word=
    ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm
      (NW.admissionWord factory (packet (ordinal+1))
        (liftMap (R:=ℤ) (R.wordMapAt observation nontrivial half depth (ordinal+1)
          ((PT.words rawTrace).get (actualIndex observation nontrivial half depth))))) := by
  rw [actualOccurrence,relationTransport_word,JOcc.actual_word]
noncomputable def storedValue : BurnolL2 := physicalValue (AS.bornAfterNative native).1
  (decodeMap (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path
    (actualOccurrence observation nontrivial half depth ordinal).word)
theorem stored_child : storedValue observation nontrivial half depth ordinal=(actualChild observation nontrivial half depth).value := by
  have word:=actual_word observation nontrivial half depth ordinal
  let originalWord := (PT.words rawTrace).get (actualIndex observation nontrivial half depth)
  refine (congrArg (fun item=>physicalValue (AS.bornAfterNative native).1
    (decodeMap (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path item)) word).trans ?_
  refine (physical_native_word (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path factory
    (packet (ordinal+1)) (R.wordMapAt observation nontrivial half depth (ordinal+1) originalWord)).trans ?_
  refine (physical_word observation nontrivial half depth
    (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path originalWord (ordinal+1)).trans ?_
  exact Traced.stored_value c (parentTrace observation nontrivial half depth)
run_cmd IO.eprintln "paired-B Origin: original ordered occurrence complete"

namespace A
export OriginalSecondBGammaAction (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader actualFrame actualOriginFace target_source_payload)
end A
namespace Old
export OriginalConstantFourierNativeOrigin (originPayload)
end Old
open private targetRoot targetVisit frame_root frame_visit from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource
open private cast_same payloadHistory occurrence_receipt from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierPrice.Origin
open private same_payload from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSecondBContact.Origin
local notation "root"=>A.sourceRoot observation nontrivial half depth ordinal t N
local notation "visit"=>A.sourceVisit observation nontrivial half depth ordinal t N
local notation "u7"=>A.sourceU7 observation nontrivial half depth ordinal t N
local notation "calculus"=>A.sourceCalculus observation nontrivial half depth ordinal t N
local notation "reader"=>A.sourceReader observation nontrivial half depth ordinal t N
noncomputable def sourceRoot := targetRoot root visit u7 calculus reader
noncomputable def sourceVisit := targetVisit root visit u7 calculus reader
noncomputable def sourceFrame := A.actualFrame observation nontrivial half depth ordinal t N
noncomputable abbrev source_frame_root := frame_root root visit u7 calculus reader
noncomputable abbrev source_frame_visit := frame_visit root visit u7 calculus reader
noncomputable def inputFace := OriginalSecondBGammaConsumer.nextFace observation nontrivial half depth ordinal t N
noncomputable abbrev inputState := OriginalSecondBGammaConsumer.nextState observation nontrivial half depth ordinal t N
noncomputable abbrev inputTrace := OriginalSecondBGammaConsumer.nextTrace observation nontrivial half depth ordinal t N
noncomputable abbrev input_state_source := OriginalSecondBGammaConsumer.next_state_source observation nontrivial half depth ordinal t N
noncomputable abbrev input_trace_source := OriginalSecondBGammaConsumer.next_trace_source observation nontrivial half depth ordinal t N
noncomputable def originFace := A.actualOriginFace observation nontrivial half depth ordinal t N
private noncomputable abbrev retained_payload :=
  (A.target_source_payload observation nontrivial half depth ordinal t N).trans
    (same_payload observation nontrivial half depth ordinal t N)
noncomputable def originPayload : type_of% (Old.originPayload observation nontrivial half depth ordinal) :=
  Eq.mp (type_eq_of_heq (retained_payload observation nontrivial half depth ordinal t N))
    (originFace observation nontrivial half depth ordinal t N).rootRead
noncomputable abbrev origin_source := cast_same
  (originFace observation nontrivial half depth ordinal t N).rootRead
  (Old.originPayload observation nontrivial half depth ordinal)
  (retained_payload observation nontrivial half depth ordinal t N)
private noncomputable def historyReceipt := payloadHistory observation nontrivial half depth ordinal
  (originPayload observation nontrivial half depth ordinal t N) (origin_source observation nontrivial half depth ordinal t N)
noncomputable def currentHistory := (historyReceipt observation nontrivial half depth ordinal t N).val
noncomputable abbrev history_source := (historyReceipt observation nontrivial half depth ordinal t N).property
private noncomputable def wordReceipt := occurrence_receipt (historyReceipt observation nontrivial half depth ordinal t N)
  (actualOccurrence observation nontrivial half depth ordinal)
noncomputable def pairedWord := (wordReceipt observation nontrivial half depth ordinal t N).val
noncomputable abbrev paired_word_source := (wordReceipt observation nontrivial half depth ordinal t N).property
/-- Decode only the already-stored constant selected by the original paid Step. -/
noncomputable def pairedValue : BurnolL2 := physicalValue (AS.bornAfterNative native).1
  (decodeMap (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path
    (pairedWord observation nontrivial half depth ordinal t N))
theorem paired_value_source : pairedValue observation nontrivial half depth ordinal t N=(actualChild observation nontrivial half depth).value :=
  (congrArg (fun word=>physicalValue (AS.bornAfterNative native).1
    (decodeMap (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path word))
      (paired_word_source observation nontrivial half depth ordinal t N)).trans
    (stored_child observation nontrivial half depth ordinal)
noncomputable def pairedReceipt : Trace.SourceReceipt (parentTrace observation nontrivial half depth) (Traced.pairedCode c) :=
  Traced.repoint (actualChild observation nontrivial half depth)
    (pairedValue observation nontrivial half depth ordinal t N)
    (paired_value_source observation nontrivial half depth ordinal t N)
noncomputable def pairedTrace := (pairedReceipt observation nontrivial half depth ordinal t N).trace
noncomputable abbrev paired_receipt_read := Traced.repoint_value (actualChild observation nontrivial half depth)
  (pairedValue observation nontrivial half depth ordinal t N)
  (paired_value_source observation nontrivial half depth ordinal t N)
noncomputable abbrev paired_address := Traced.child_address c (parentTrace observation nontrivial half depth)
noncomputable abbrev plus_kernel_actual := Traced.plus_kernel_actual c (parentTrace observation nontrivial half depth)
noncomputable abbrev minus_kernel_actual := Traced.minus_kernel_actual c (parentTrace observation nontrivial half depth)
theorem paired_actual : pairedValue observation nontrivial half depth ordinal t N=OriginalKPairedBEulerJunctionSource.sourceAction c :=
  (paired_value_source observation nontrivial half depth ordinal t N).trans
    (Traced.child_actual c (parentTrace observation nontrivial half depth))
run_cmd IO.eprintln "paired-B Origin: actual target stored paired source complete"
end OriginalPairedSecondBOrigin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalPairedSecondBOrigin"
