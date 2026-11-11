import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedSecondB.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompleteContactPrice.KernelReceipt
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJointMobiusSourceFields

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalBoundaryGammaOrigin
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

namespace Traced
def path : List Bool := [false]
variable (c:BurnolCompletedMellinCoordinate) {env:Env P.Value P.Var} {total:BurnolL2}
variable (actual:Trace env (P.code c) (.const total))
noncomputable def outer := Trace.splitLinear actual
noncomputable def boundary := Trace.splitAdd (outer c actual).trace
noncomputable def positive := Trace.splitLinear (boundary c actual).leftTrace
noncomputable def child : Trace.SourceReceipt actual (P.sourceCode c) :=
  ⟨(outer c actual).input,(outer c actual).trace,.linear (outer c actual) (.refl _)⟩
noncomputable def leftKernel : Trace.SourceReceipt actual (BS.sourceKernelCode c) :=
  ⟨(positive c actual).input,(positive c actual).trace,
    .linear (outer c actual) (.left (boundary c actual) (.linear (positive c actual) (.refl _)))⟩
noncomputable def plusKernel := OriginalPairedSecondBOrigin.Traced.plusKernel c actual
noncomputable def minusKernel := OriginalPairedSecondBOrigin.Traced.minusKernel c actual
noncomputable def cursor : Trace.Cursor actual := (outer c actual).interleaving.lastCursor
set_option backward.isDefEq.respectTransparency false in
theorem cursor_stored : childAt path (cursor c actual).beforeExpr=.const (child c actual).value := by
  unfold cursor
  rw [last_before]
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
theorem child_address : (child c actual).retained.address=[2] := rfl
theorem left_kernel_address : (leftKernel c actual).retained.address=[2,0,2] := rfl
theorem left_kernel_actual : (leftKernel c actual).value=(burnolCompletedMellinRieszVector c:BurnolL2) :=
  OriginalCompleteFeeInput.Kernel.kernel_actual c (leftKernel c actual).trace
theorem plus_kernel_actual : (plusKernel c actual).value=(burnolCompletedMellinRieszVector c:BurnolL2) :=
  OriginalPairedSecondBOrigin.Traced.plus_kernel_actual c actual
theorem minus_kernel_actual : (minusKernel c actual).value=(burnolCompletedMellinRieszVector c:BurnolL2) :=
  OriginalPairedSecondBOrigin.Traced.minus_kernel_actual c actual
theorem child_actual : (child c actual).value=
    pairedMellinTranslationCharacter c.value P.fixedShift • (burnolCompletedMellinRieszVector c:BurnolL2)-
    OriginalKPairedBEulerJunctionSource.sourceAction c := by
  have read := (child c actual).trace.sound.symm
  have kernel := (leftKernel c actual).trace.sound.trans (left_kernel_actual c actual)
  change (child c actual).value=pairedMellinTranslationCharacter c.value P.fixedShift •
    ((BS.sourceKernelCode c).eval env)+(-1:ℂ) •
      (pairedBurnolMultiplicativeDilation P.fixedShift ((BS.sourceKernelCode c).eval env)) at read
  rw [kernel] at read
  change (child c actual).value=pairedMellinTranslationCharacter c.value P.fixedShift •
    (burnolCompletedMellinRieszVector c:BurnolL2)-
    pairedBurnolMultiplicativeDilation P.fixedShift (burnolCompletedMellinRieszVector c:BurnolL2)
  simpa only [neg_one_smul,sub_eq_add_neg] using read

theorem child_projected (zero:riemannZeta c.value=0) :
    burnolEvenAmbientProjection (child c actual).value=burnolZeroPairedFixedAnnulusBoundary c zero P.fixedShift := by
  rw [child_actual,map_sub,map_smul]
  have fixed : burnolEvenAmbientProjection (burnolCompletedMellinRieszVector c:BurnolL2)=burnolCompletedMellinRieszVector c :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [fixed]
  have pairedProjection : burnolEvenAmbientProjection (OriginalKPairedBEulerJunctionSource.sourceAction c)=
      burnolPairedAmbientCompression P.fixedShift (burnolCompletedMellinRieszVector c) := by
    unfold OriginalKPairedBEulerJunctionSource.sourceAction pairedBurnolMultiplicativeDilation burnolPairedAmbientCompression
    simp only [smul_apply,add_apply,map_smul,map_add]
    rfl
  rw [pairedProjection]
  rfl
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
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ) (N:Nat)
local notation "c"=>OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "oldTrace"=>C.wholeDebtRJointMobiusSourceTrace observation nontrivial depth half 0
local notation "native"=>WN.native observation nontrivial half depth ordinal
local notation "factory"=>D.factory observation nontrivial half
local notation "packet"=>Born.packetAt observation nontrivial half depth
noncomputable def parentTrace : Trace (C.receipt observation nontrivial depth half).1.environment (P.code c)
    (.const (OriginalKJointMobiusSourceWriteback.actualValue observation nontrivial half depth 0)) := oldTrace
noncomputable def boundaryReceipt := Traced.child c (parentTrace observation nontrivial half depth)
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
          ((PT.words oldTrace).get (actualIndex observation nontrivial half depth))))) := by
  rw [actualOccurrence,relationTransport_word,JOcc.actual_word]
noncomputable def storedValue : BurnolL2 := physicalValue (AS.bornAfterNative native).1
  (decodeMap (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path
    (actualOccurrence observation nontrivial half depth ordinal).word)
theorem stored_child : storedValue observation nontrivial half depth ordinal=(actualChild observation nontrivial half depth).value := by
  have word:=actual_word observation nontrivial half depth ordinal
  let originalWord := (PT.words oldTrace).get (actualIndex observation nontrivial half depth)
  refine (congrArg (fun item=>physicalValue (AS.bornAfterNative native).1
    (decodeMap (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path item)) word).trans ?_
  refine (physical_native_word (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path factory
    (packet (ordinal+1)) (R.wordMapAt observation nontrivial half depth (ordinal+1) originalWord)).trans ?_
  refine (physical_word observation nontrivial half depth
    (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path originalWord (ordinal+1)).trans ?_
  exact Traced.stored_value c (parentTrace observation nontrivial half depth)

namespace A
export OriginalPairedSecondBAction (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader actualFrame actualOriginFace target_source_payload)
end A
namespace Old
export OriginalConstantFourierNativeOrigin (originPayload)
end Old
open private targetRoot targetVisit frame_root frame_visit from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource
open private cast_same payloadHistory occurrence_receipt from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierPrice.Origin
open private retained_payload from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedSecondB.Origin
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
noncomputable def inputFace := OriginalPairedSecondBConsumer.nextFace observation nontrivial half depth ordinal t N
noncomputable abbrev inputState := OriginalPairedSecondBConsumer.nextState observation nontrivial half depth ordinal t N
noncomputable abbrev inputTrace := OriginalPairedSecondBConsumer.nextTrace observation nontrivial half depth ordinal t N
noncomputable abbrev input_state_source := OriginalPairedSecondBConsumer.next_state_source observation nontrivial half depth ordinal t N
noncomputable abbrev input_trace_source := OriginalPairedSecondBConsumer.next_trace_source observation nontrivial half depth ordinal t N
noncomputable def originFace := A.actualOriginFace observation nontrivial half depth ordinal t N
private noncomputable abbrev source_payload :=
  (A.target_source_payload observation nontrivial half depth ordinal t N).trans
    (retained_payload observation nontrivial half depth ordinal t N)
noncomputable def originPayload : type_of% (Old.originPayload observation nontrivial half depth ordinal) :=
  Eq.mp (type_eq_of_heq (source_payload observation nontrivial half depth ordinal t N))
    (originFace observation nontrivial half depth ordinal t N).rootRead
noncomputable abbrev origin_source := cast_same
  (originFace observation nontrivial half depth ordinal t N).rootRead
  (Old.originPayload observation nontrivial half depth ordinal)
  (source_payload observation nontrivial half depth ordinal t N)
private noncomputable def historyReceipt := payloadHistory observation nontrivial half depth ordinal
  (originPayload observation nontrivial half depth ordinal t N) (origin_source observation nontrivial half depth ordinal t N)
noncomputable def currentHistory := (historyReceipt observation nontrivial half depth ordinal t N).val
noncomputable abbrev history_source := (historyReceipt observation nontrivial half depth ordinal t N).property
private noncomputable def wordReceipt := occurrence_receipt (historyReceipt observation nontrivial half depth ordinal t N)
  (actualOccurrence observation nontrivial half depth ordinal)
noncomputable def rawWord := (wordReceipt observation nontrivial half depth ordinal t N).val
noncomputable abbrev raw_word_source := (wordReceipt observation nontrivial half depth ordinal t N).property
/-- Decode only the already-stored constant selected by the original paid Step. -/
noncomputable def rawValue : BurnolL2 := physicalValue (AS.bornAfterNative native).1
  (decodeMap (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path
    (rawWord observation nontrivial half depth ordinal t N))
theorem raw_value_source : rawValue observation nontrivial half depth ordinal t N=(actualChild observation nontrivial half depth).value :=
  (congrArg (fun word=>physicalValue (AS.bornAfterNative native).1
    (decodeMap (remaining (actualCursor observation nontrivial half depth).beforeExpr) Traced.path word))
      (raw_word_source observation nontrivial half depth ordinal t N)).trans
    (stored_child observation nontrivial half depth ordinal)
noncomputable def rawReceipt : Trace.SourceReceipt (parentTrace observation nontrivial half depth) (P.sourceCode c) :=
  Traced.repoint (actualChild observation nontrivial half depth)
    (rawValue observation nontrivial half depth ordinal t N)
    (raw_value_source observation nontrivial half depth ordinal t N)
noncomputable def rawTrace := (rawReceipt observation nontrivial half depth ordinal t N).trace
noncomputable abbrev raw_receipt_read := Traced.repoint_value (actualChild observation nontrivial half depth)
  (rawValue observation nontrivial half depth ordinal t N)
  (raw_value_source observation nontrivial half depth ordinal t N)
noncomputable abbrev raw_address := Traced.child_address c (parentTrace observation nontrivial half depth)
noncomputable abbrev plus_kernel_actual := Traced.plus_kernel_actual c (parentTrace observation nontrivial half depth)
noncomputable abbrev minus_kernel_actual := Traced.minus_kernel_actual c (parentTrace observation nontrivial half depth)
noncomputable abbrev raw_actual :=
  (raw_value_source observation nontrivial half depth ordinal t N).trans
    (Traced.child_actual c (parentTrace observation nontrivial half depth))
noncomputable abbrev projected_actual (zero:riemannZeta (c).value=0) :=
  (congrArg burnolEvenAmbientProjection (raw_value_source observation nontrivial half depth ordinal t N)).trans
    (Traced.child_projected c (parentTrace observation nontrivial half depth) zero)
noncomputable abbrev leftKernelReceipt := Traced.leftKernel c (parentTrace observation nontrivial half depth)
noncomputable abbrev left_kernel_actual := Traced.left_kernel_actual c (parentTrace observation nontrivial half depth)
noncomputable abbrev originalPairedReceipt := OriginalPairedSecondBConsumer.sourcePairedReceipt observation nontrivial half depth ordinal t N
noncomputable abbrev originalPairedTrace := OriginalPairedSecondBConsumer.sourcePairedTrace observation nontrivial half depth ordinal t N
noncomputable def boundaryB0 : ℂ := burnolConstantGapCoefficient burnolUnscaledCommonGapRadius
  (burnolEvenAmbientProjection (rawValue observation nontrivial half depth ordinal t N))
end OriginalBoundaryGammaOrigin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env=>Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalBoundaryGammaOrigin"
