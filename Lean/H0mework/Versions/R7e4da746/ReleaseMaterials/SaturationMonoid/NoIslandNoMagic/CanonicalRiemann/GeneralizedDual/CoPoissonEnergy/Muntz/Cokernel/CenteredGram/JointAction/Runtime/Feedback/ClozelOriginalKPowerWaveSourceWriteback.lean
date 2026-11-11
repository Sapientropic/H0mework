import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRSourceReceiptConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPowerWaveSourceOccurrences
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Word.ConstantInverse

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPowerWaveSourceWriteback
open Complex BurnolPhysicalState RootInquiryCompletion
open OriginalKPairedBEulerJunctionSource
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
local instance levelGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue OriginalKCombReceiptFeedback.Value) grade target) :=
  L.groups (PairValue OriginalKCombReceiptFeedback.Value) grade target
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
  (native oldStock oldEnvironment beforeStock beforeEnvironment sourceFrame sourceBase packetAdmission admissions)
end WN
namespace AR
export SourceInventoryExecutionFeed.AdmissionReceipt (Admission)
end AR
namespace Engine
export ActualNativeRelationTransport.AS (stockScalar)
end Engine
namespace C
export OriginalKCombReceiptFeedback
  (receipt wholeDebtRWaveSourceCode wholeDebtRWaveSourceTrace whole_debt_R_wave_source_preserved)
end C
namespace Prog
export OriginalKPowerWaveSourceCalculation (code sourceEnvironment code_environment)
end Prog
namespace R
export OriginalWholeDebtRSourceReceiptConsumer (bornWordMap wordMapAt)
end R
namespace Born
export OriginalKBFiniteCalculation.BornInventory
  (packetAt sourceBornHistory actualBornHistory actual_source_relations_in_born)
end Born
namespace NW
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback (admissionWord)
end NW
namespace PT
export SourceOperationPaidRelations (words exposure paid_boundary events_trace complete_steps)
end PT
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative
  (request generatedAction nextOriginFace sourceWord nextFullValue actualMaterial
   source_effect source_inverse same_ledger same_visit compiles whole_first canonical_next next_source_occurrences)
end SN

private theorem source_word_append {V X : Unit → Type} [∀ target, AddCommGroup (V target)]
    (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
      (Value := PairValue V) (Var := X) (sort := ()))
    (base : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
      (PhysicalValue := PairValue V) (PhysicalVar := X) (sort := ()))
    (before : SourceInventoryExecutionFeed.Inventory (V := V) (X := X) (s := ()))
    (old fresh : List (AR.Admission before (Engine.stockScalar frame base))) :
    SN.sourceWord (V := V) frame base before (old ++ fresh) =
      SN.sourceWord (V := V) frame base before old +
        SN.sourceWord (V := V) frame base before fresh := by
  change liftMap (R := ℤ) ((old ++ fresh).map (fun admitted => admitted.1.word)).sum =
    liftMap (R := ℤ) (old.map (fun admitted => admitted.1.word)).sum +
      liftMap (R := ℤ) (fresh.map (fun admitted => admitted.1.word)).sum
  rw [List.map_append, List.sum_append, map_add]

open private born_word_relation from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRSourceReceiptConsumer
open private born_inventory from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Native
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "raw" => C.wholeDebtRWaveSourceCode observation nontrivial depth half
local notation "trace" => C.wholeDebtRWaveSourceTrace observation nontrivial depth half
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "frame" => WN.sourceFrame factory native
local notation "base" => WN.sourceBase factory native
local notation "before" => WN.beforeStock native
local notation "oldEnv" => WN.beforeEnvironment native
local notation "packet" => Born.packetAt observation nontrivial half depth (ordinal+1)

theorem bound_code_value (environment : Env OriginalKPowerWaveSourceCalculation.Value
    OriginalKPowerWaveSourceCalculation.Var) :
    (raw).eval environment = (Prog.code c junctionShift).eval Prog.sourceEnvironment := by
  unfold C.wholeDebtRWaveSourceCode
  rw [Expr.eval_subst]
  change (Prog.code c junctionShift).eval _ = _
  exact Prog.code_environment c junctionShift _ _

def actualValue : BurnolL2 :=
  (raw).eval (C.receipt observation nontrivial depth half).1.environment

theorem actual_value_runtime : actualValue observation nontrivial half depth =
    (runtimePowerWaveCalculationResultAt observation nontrivial depth half).2.2.1 := by
  rw [actualValue, bound_code_value, runtimePowerWaveCalculationResultAt_source]
  exact (OriginalKWholeDebtRCalculationFace.wave_result_value observation nontrivial half
    (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence).symm

def boundary : Formal ℤ OriginalKPowerWaveSourceCalculation.Value OriginalKPowerWaveSourceCalculation.Var () :=
  relationMap (R := ℤ) (C.receipt observation nontrivial depth half).1.environment (trace).relationWords

theorem actual_boundary : boundary observation nontrivial half depth =
    Finsupp.single (raw) (1 : ℤ) -
      Finsupp.single (.const (actualValue observation nontrivial half depth)) 1 :=
  (trace).relation_boundary (R := ℤ)

def oldAdmissions : List (AR.Admission before (Engine.stockScalar frame base)) := WN.admissions factory native

def waveAdmissions : List (AR.Admission before (Engine.stockScalar frame base)) := List.ofFn fun index =>
  WN.packetAdmission factory (AS.bornAfterNative native) (WN.oldStock native)
    (WN.oldEnvironment native) (born_inventory native)
    (OriginalKPowerWaveSourceOccurrences.actualOccurrence observation nontrivial half depth ordinal index)

theorem wave_admissions_steps :
    (waveAdmissions observation nontrivial half depth ordinal).length = remaining raw ∧
      0 < (waveAdmissions observation nontrivial half depth ordinal).length := by
  have count : (waveAdmissions observation nontrivial half depth ordinal).length = remaining raw := by
    rw [waveAdmissions, List.length_ofFn]
    exact (PT.complete_steps trace).trans (trace).length_to_const
  refine ⟨count, ?_⟩
  rw [count]
  change 0 < remaining
    ((Expr.add (OriginalKPowerWaveSourceCalculation.singleCode c junctionShift)
      (OriginalKPowerWaveSourceCalculation.singleCode c (-junctionShift))).subst
        (OriginalKCombReceiptFeedback.bSelfSourceBinding observation nontrivial depth half)) + 1
  omega

def waveWords := List.ofFn fun index : OriginalKPowerWaveSourceOccurrences.Index observation nontrivial half depth =>
  ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm
    (NW.admissionWord factory packet
      (liftMap (R := ℤ) (R.wordMapAt observation nontrivial half depth (ordinal+1)
        ((PT.words trace).get index))))

theorem wave_admissions_words :
    (waveAdmissions observation nontrivial half depth ordinal).map (fun admitted => admitted.1.word) =
      waveWords observation nontrivial half depth ordinal := by
  unfold waveAdmissions waveWords
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  exact (OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative.packet_admission_word
    factory (AS.bornAfterNative native) (WN.oldStock native) (WN.oldEnvironment native)
      (born_inventory native) (OriginalKPowerWaveSourceOccurrences.actualOccurrence
        observation nontrivial half depth ordinal index)).trans
    (congrArg (ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm)
      (OriginalKPowerWaveSourceOccurrences.actual_word observation nontrivial half depth ordinal index))

theorem wave_words_sum : (waveWords observation nontrivial half depth ordinal).sum =
    ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm
      (NW.admissionWord factory packet
        (liftMap (R := ℤ) (R.wordMapAt observation nontrivial half depth (ordinal+1)
          (boundary observation nontrivial half depth)))) := by
  let action :=
    (ActualCofinalSourceAction.wordTransport (AS.bornAfterNative native).2.2.2.down.symm).toLinearMap.comp
      ((NW.admissionWord factory packet).comp
        ((liftMap (R := ℤ)).comp (R.wordMapAt observation nontrivial half depth (ordinal+1))))
  have indexed : (List.ofFn fun index : OriginalKPowerWaveSourceOccurrences.Index
      observation nontrivial half depth => (PT.words trace).get index) = PT.words trace :=
    List.ofFn_get _
  have transformed := congrArg (List.map action) indexed
  rw [List.map_ofFn] at transformed
  have listed : waveWords observation nontrivial half depth ordinal = (PT.words trace).map action :=
    transformed
  rw [listed, ← map_list_sum, PT.paid_boundary]
  rfl

def admissions : List (AR.Admission before (Engine.stockScalar frame base)) :=
  oldAdmissions observation nontrivial half depth ordinal ++
  waveAdmissions observation nontrivial half depth ordinal

theorem old_admissions_prefix :
    (admissions observation nontrivial half depth ordinal).take
      (oldAdmissions observation nontrivial half depth ordinal).length =
        oldAdmissions observation nontrivial half depth ordinal := by
  simp only [admissions, List.take_left]

def request := SN.request (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv (admissions observation nontrivial half depth ordinal)
def generatedAction := SN.generatedAction (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv (admissions observation nontrivial half depth ordinal)
def nextFace := SN.nextOriginFace (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv (admissions observation nontrivial half depth ordinal)
def sourceWord := SN.sourceWord (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before (admissions observation nontrivial half depth ordinal)
def nextFullValue := SN.nextFullValue (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv (admissions observation nontrivial half depth ordinal)

theorem source_word_split : sourceWord observation nontrivial half depth ordinal =
    SN.sourceWord (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before (oldAdmissions observation nontrivial half depth ordinal) +
      SN.sourceWord (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before (waveAdmissions observation nontrivial half depth ordinal) :=
  source_word_append
    (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1)
    (X := (AS.bornAfterNative native).2.2.1.LowVar) frame base before
    (oldAdmissions observation nontrivial half depth ordinal)
    (waveAdmissions observation nontrivial half depth ordinal)

def bornBoundary := R.bornWordMap observation nontrivial half depth ordinal
  (boundary observation nontrivial half depth)

theorem born_boundary_written : bornBoundary observation nontrivial half depth ordinal ∈
    (Born.sourceBornHistory observation nontrivial half depth ordinal).relationClosure := by
  have each (word) (belongs : word ∈ PT.words trace) :=
    born_word_relation observation nontrivial half depth word
      (C.whole_debt_R_wave_source_preserved observation nontrivial depth half
        (.relation word) (by
          apply List.mem_cons_of_mem
          change .relation word ∈ RootedAccountedUnfolding.traceBranches
            (SourceOperationPaidRelations.events trace)
          rw [PT.events_trace]
          exact List.mem_map.mpr ⟨word, belongs, rfl⟩)) ordinal
  have sum_mem : ∀ items : List (Formal ℤ OriginalKPowerWaveSourceCalculation.Value
      OriginalKPowerWaveSourceCalculation.Var ()),
      (∀ word ∈ items, R.bornWordMap observation nontrivial half depth ordinal word ∈
        (Born.sourceBornHistory observation nontrivial half depth ordinal).relationClosure) →
      R.bornWordMap observation nontrivial half depth ordinal items.sum ∈
        (Born.sourceBornHistory observation nontrivial half depth ordinal).relationClosure := by
    intro items
    induction items with
    | nil => intro _; rw [List.sum_nil, map_zero]; exact Submodule.zero_mem _
    | cons head tail previous =>
        intro all
        rw [List.sum_cons, map_add]
        exact Submodule.add_mem _ (all head List.mem_cons_self)
          (previous (fun word belongs => all word (List.mem_cons_of_mem head belongs)))
  unfold bornBoundary boundary
  rw [← PT.paid_boundary]
  exact sum_mem (PT.words trace) each

theorem actual_born_kernel :
    (Born.actualBornHistory observation nontrivial half depth ordinal).completionProjection
      ((Submodule.inclusion
        (Born.actualBornHistory observation nontrivial half depth ordinal).relationClosure_le_generatorClosure)
        ⟨bornBoundary observation nontrivial half depth ordinal,
          Born.actual_source_relations_in_born observation nontrivial half depth ordinal
            (born_boundary_written observation nontrivial half depth ordinal)⟩) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2
    (Born.actual_source_relations_in_born observation nontrivial half depth ordinal
      (born_boundary_written observation nontrivial half depth ordinal))

theorem actual_canonical_next : type_of% (SN.canonical_next (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := SN.canonical_next (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)

theorem source_occurrences : (nextFace observation nontrivial half depth ordinal).rootRead.source.occurrences =
    admissions observation nontrivial half depth ordinal :=
  SN.next_source_occurrences (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)

theorem actual_compiles : type_of% (SN.compiles (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := SN.compiles (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem actual_source_effect : type_of% (SN.source_effect (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := SN.source_effect (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem actual_source_inverse : type_of% (SN.source_inverse (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := SN.source_inverse (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem actual_inverse_certificate : type_of% (ActualSourceConstantInverse.actual_next_certificate (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := ActualSourceConstantInverse.actual_next_certificate (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem actual_whole_next : type_of% (ActualSourceConstantInverse.original_whole_next (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := ActualSourceConstantInverse.original_whole_next (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem actual_same_ledger : type_of% (SN.same_ledger (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := SN.same_ledger (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)
theorem actual_same_visit : type_of% (SN.same_visit (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)) := SN.same_visit (V := L.Value (PairValue OriginalKCombReceiptFeedback.Value) (AS.bornAfterNative native).1) frame base before oldEnv
    (admissions observation nontrivial half depth ordinal)

end OriginalKPowerWaveSourceWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
