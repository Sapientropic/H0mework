import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveAction
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Prefix
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Occurrence

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option pp.deepTerms.threshold 24
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedWaveNativeStockSource
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution BurnolPhysicalState
open CofinalHistorySettlement
open private mp_heq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource
namespace A
export OriginalKPairedWaveAction
  (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader actualTarget actualFrame canonical_next)
end A
namespace S
export OriginalKPairedWaveActionSource (reader environment code result trace trace_heq rInput r_equation paid)
end S
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var)
end Prog
namespace Adapter
export OriginalKPaNativeCayleyNextPrefixSource.Adapter (targetFace state terminalValue)
end Adapter
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw raw Current)
end O
namespace OC
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer
  (targetState trace value target_expression paid_history)
end OC
namespace MS
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (endpointState endpoint_source_state packet residualTarget frame)
end MS
namespace Activation
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme originalProgramme)
end Activation
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (nextBorn frames runtime actual_next successor_valid)
end Shared
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion
  (receipt atReceipt receipt_next receipt_compiles)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix
  (receipt_distance_exact receipt_paid_prefix)
end Complete
namespace Native
export ActualNativeRelationTransport (bornStock born_stock complete_source_cost)
end Native
namespace AS
export ActualNativeRelationTransport.AS (stockScalar stockCfg generatedStock stockDecodedEnvironment)
end AS
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
  (preserve)
end Stock
namespace Feed
export SourceInventoryExecutionFeed (Inventory written written_trace executionBranches requests traceCost sourceCost)
end Feed
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR
namespace PT
export SourceOperationPaidRelations
  (exposure words complete_steps stepOccurrence stepOccurrence_word stepOccurrence_before_length stepOccurrence_positions)
end PT

private theorem cast_trace_length {Sorts : Type u} {V X : Sorts → Type u} [∀ s, AddCommGroup (V s)] {sort : Sorts}
    {environment : Env V X} {raw left right : Expr V X sort}
    (same : left = right) (actual : Trace environment raw left) :
    (Eq.mp (congrArg (Trace environment raw) same) actual).length = actual.length := by
  cases same
  rfl

private theorem cast_trace_words {Sorts : Type u} {V X : Sorts → Type u} [∀ s, AddCommGroup (V s)] {sort : Sorts}
    {environment : Env V X} {raw left right : Expr V X sort}
    (same : left = right) (actual : Trace environment raw left) :
    PT.words (Eq.mp (congrArg (Trace environment raw) same) actual) = PT.words actual := by
  cases same
  rfl

namespace Retained
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (u7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N u7)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
  visit.current → O.Raw (Value := Value) (Var := Var) (sort := sort))

private theorem state_eq : Adapter.state root visit u7 calculus reader =
    OC.targetState root.toAuthoritativeRoot visit.current reader := by
  let current := (MS.endpointState root visit u7 calculus reader).visit.current
  change (MS.packet root visit u7 calculus reader current).targetCurrent = _
  have endpoint : current = OC.targetState root.toAuthoritativeRoot visit.current reader :=
    MS.endpoint_source_state root visit u7 calculus reader
  have next := Option.some.inj ((MS.packet root visit u7 calculus reader current).actual_next.symm.trans
    (RootGeneratedDebtActivationJointSource.OwnerFree.next_eq root.toAuthoritativeRoot visit.current reader current))
  have zero : remaining current.1 = 0 := by
    rw [endpoint, OC.target_expression]
    rfl
  exact next.trans ((RootGeneratedDebtActivationJointSource.OwnerFree.Completion.next_state_of_zero
    root.toAuthoritativeRoot visit.current reader current zero).trans endpoint)

private theorem state_source : HEq (Adapter.state root visit u7 calculus reader)
    (OC.targetState root.toAuthoritativeRoot visit.current reader) :=
  heq_of_eq (state_eq root visit u7 calculus reader)

private theorem trace_source : HEq (Adapter.state root visit u7 calculus reader).2
    (OC.trace root.toAuthoritativeRoot visit.current reader) := by
  have same := state_eq root visit u7 calculus reader
  exact (Sigma.mk.inj same).2

private theorem trace_length : (Adapter.state root visit u7 calculus reader).2.length =
    (OC.trace root.toAuthoritativeRoot visit.current reader).length :=
  congrArg (fun state => state.2.length) (state_eq root visit u7 calculus reader)

private theorem expression : (Adapter.state root visit u7 calculus reader).1 =
    .const (OC.value root.toAuthoritativeRoot visit.current reader) :=
  (congrArg Sigma.fst (state_eq root visit u7 calculus reader)).trans
    (OC.target_expression root.toAuthoritativeRoot visit.current reader)

private noncomputable def normalizedTrace :
    Trace (O.raw root.toAuthoritativeRoot visit.current reader).environment
      (O.raw root.toAuthoritativeRoot visit.current reader).expression
      (.const (OC.value root.toAuthoritativeRoot visit.current reader)) :=
  Eq.mp (congrArg (Trace (O.raw root.toAuthoritativeRoot visit.current reader).environment
      (O.raw root.toAuthoritativeRoot visit.current reader).expression) (expression root visit u7 calculus reader))
    (Adapter.state root visit u7 calculus reader).2

private theorem normalized_words : PT.words (normalizedTrace root visit u7 calculus reader) =
    PT.words (Adapter.state root visit u7 calculus reader).2 :=
  cast_trace_words (expression root visit u7 calculus reader) (Adapter.state root visit u7 calculus reader).2

private theorem paid : (Adapter.state root visit u7 calculus reader).2.length =
    remaining (O.raw root.toAuthoritativeRoot visit.current reader).expression :=
  (trace_length root visit u7 calculus reader).trans
    (OC.paid_history root.toAuthoritativeRoot visit.current reader)

private theorem normalized_paid : (normalizedTrace root visit u7 calculus reader).length =
    remaining (O.raw root.toAuthoritativeRoot visit.current reader).expression :=
  (cast_trace_length (expression root visit u7 calculus reader)
    (Adapter.state root visit u7 calculus reader).2).trans (paid root visit u7 calculus reader)

private theorem word_count : (PT.words (Adapter.state root visit u7 calculus reader).2).length =
    remaining (O.raw root.toAuthoritativeRoot visit.current reader).expression :=
  (PT.complete_steps (Adapter.state root visit u7 calculus reader).2).trans
    (paid root visit u7 calculus reader)

private noncomputable def targetRoot := (MS.residualTarget root visit u7 calculus reader).targetRoot
private noncomputable def targetVisit := (MS.residualTarget root visit u7 calculus reader).targetVisit

private theorem frame_root : (MS.frame root visit u7 calculus reader).currentState.root =
    targetRoot root visit u7 calculus reader := rfl

private theorem frame_visit : HEq (MS.frame root visit u7 calculus reader).currentState.visit
    (targetVisit root visit u7 calculus reader) := HEq.rfl
end Retained

private theorem linear_cut_input {V X : Unit → Type} [∀ s, AddCommGroup (V s)]
    {environment : Env V X} {operation : V () →+ V ()} {body : Expr V X ()} {total input : V ()}
    {actual : Trace environment (.linear operation body) (.const total)}
    (cut : Trace.LinearSplit actual) (child : Trace environment body (.const input)) :
    cut.input = input := cut.trace.sound.symm.trans child.sound

private theorem trace_value {V X : Unit → Type} [∀ s, AddCommGroup (V s)]
    {environment : Env V X} {raw : Expr V X ()} {left right : V ()}
    (actual : Trace environment raw (.const left)) (original : Trace environment raw (.const right)) :
    left = right := actual.sound.symm.trans original.sound

private theorem linear_last_word {V X : Unit → Type} [∀ s, AddCommGroup (V s)]
    {environment : Env V X} {operation : V () →+ V ()} {body : Expr V X ()} {total : V ()}
    {actual : Trace environment (.linear operation body) (.const total)} (cut : Trace.LinearSplit actual) :
    (PT.words actual).get ⟨cut.trace.length, by rw [PT.complete_steps, cut.length_eq]; omega⟩ =
      Finsupp.single (.linear operation (.const cut.input)) (1 : ℤ) - Finsupp.single (.const total) 1 := by
  rcases cut with ⟨input, inside, retained⟩
  induction retained with
  | last => rfl
  | step _ _ previous =>
      simpa only [PT.words, Trace.length, List.get_eq_getElem, Nat.add_comm 1,
        List.getElem_cons_succ] using previous

private theorem linear_last_word_at {V X : Unit → Type} [∀ s, AddCommGroup (V s)]
    {environment : Env V X} {operation : V () →+ V ()} {body : Expr V X ()} {total : V ()}
    {actual : Trace environment (.linear operation body) (.const total)} (cut : Trace.LinearSplit actual)
    (words : List (Expr V X () →₀ ℤ)) (same : PT.words actual = words)
    (index : Fin words.length) (position : cut.trace.length = index.val)
    (input output : V ()) (input_eq : cut.input = input) (output_eq : total = output) :
    words.get index =
      Finsupp.single (.linear (s := ()) operation (.const (s := ()) input)) (1 : ℤ) -
        Finsupp.single (.const (s := ()) output) 1 := by
  let original : Fin (PT.words actual).length :=
    ⟨cut.trace.length, by rw [PT.complete_steps, cut.length_eq]; exact Nat.lt_succ_self _⟩
  have address : (PT.words actual).get original = words.get index :=
    (List.get_of_eq same original).trans (congrArg words.get (Fin.ext position))
  exact address.symm.trans ((linear_last_word cut).trans
    (congrArg₂ (fun (input output : V ()) =>
      (Finsupp.single (.linear (s := ()) operation (.const (s := ()) input)) (1 : ℤ) -
        Finsupp.single (.const (s := ()) output) 1 : Expr V X () →₀ ℤ)) input_eq output_eq))

private theorem transported_step_word {Sorts : Type u} {Value Var : Sorts → Type u}
    [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
    {environment : Env Value Var} {raw last : Expr Value Var sort}
    (trace : Trace environment raw last) {target : Feed.Inventory (V := Value) (X := Var) (s := sort)}
    (segment : SourceInventoryTraceSegment (PT.exposure trace) target)
    (index : Fin (PT.words trace).length) :
    ((PT.stepOccurrence trace index).transport segment).word = (PT.words trace).get index :=
  ((PT.stepOccurrence trace index).transport_word segment).trans (PT.stepOccurrence_word trace index)

private theorem transported_step_words {Sorts : Type u} {Value Var : Sorts → Type u}
    [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
    {environment : Env Value Var} {raw last : Expr Value Var sort}
    (trace : Trace environment raw last) {target : Feed.Inventory (V := Value) (X := Var) (s := sort)}
    (segment : SourceInventoryTraceSegment (PT.exposure trace) target) :
    (List.ofFn (fun index : Fin (PT.words trace).length =>
      (PT.stepOccurrence trace index).transport segment)).map (fun point => point.word) = PT.words trace := by
  simp only [List.map_ofFn]
  exact List.ofFn_get _

namespace Inventory
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (source : Feed.Inventory (V := Value) (X := Var) (s := sort))
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := Value) (Var := Var) (sort := sort))

/-- Only the retained source inventory is supplied; the existing programme generates its receipts. -/
private noncomputable def base : Activation.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort) :=
  { Activation.originalProgramme with nextInventory := fun _ => some source }

private noncomputable def sourceSegment : SourceInventoryTraceSegment source (AS.stockScalar frame (base source)) := by
  let inner := SourceInventoryTraceSegment.left source (AS.generatedStock frame)
  cases prior : frame.inventory with
  | none => simpa only [AS.stockScalar, base, Stock.preserve, prior] using inner
  | some carried =>
      simpa only [AS.stockScalar, base, Stock.preserve, prior] using
        inner.trans (SourceInventoryTraceSegment.right carried
          (SourceHistoryCommon.seed source (AS.generatedStock frame)))

private noncomputable def writtenSegment (environment : Env Value Var) :
    SourceInventoryTraceSegment source (Feed.written environment source) :=
  ⟨[], RootedAccountedUnfolding.traceBranches (Feed.executionBranches environment (Feed.requests source)), by
    simpa only [List.nil_append] using Feed.written_trace environment source⟩

private noncomputable def bornSegment : SourceInventoryTraceSegment source (Native.bornStock frame (base source)) :=
  (sourceSegment source frame).trans
    (writtenSegment (AS.stockScalar frame (base source)) (AS.stockDecodedEnvironment frame (base source)))

private theorem transported_word (point : WR.RelationOccurrence source) :
    (point.transport (bornSegment source frame)).word = point.word := rfl

private theorem transported_position (point : WR.RelationOccurrence source) :
    (point.transport (bornSegment source frame)).before.length =
      (bornSegment source frame).before.length + point.before.length :=
  point.transport_position (bornSegment source frame)
end Inventory

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "root" => A.sourceRoot observation nontrivial half depth ordinal
local notation "visit" => A.sourceVisit observation nontrivial half depth ordinal
local notation "u7" => A.sourceU7 observation nontrivial half depth ordinal
local notation "calculus" => A.sourceCalculus observation nontrivial half depth ordinal
local notation "reader" => A.sourceReader observation nontrivial half depth ordinal
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

noncomputable def sourceRoot := Retained.targetRoot root visit u7 calculus reader
noncomputable def sourceVisit := Retained.targetVisit root visit u7 calculus reader
noncomputable def sourceFrame := A.actualFrame observation nontrivial half depth ordinal

theorem source_frame_root : type_of% (Retained.frame_root root visit u7 calculus reader) :=
  Retained.frame_root root visit u7 calculus reader

theorem source_frame_visit : type_of% (Retained.frame_visit root visit u7 calculus reader) :=
  Retained.frame_visit root visit u7 calculus reader

theorem source_canonical_next : type_of% (A.canonical_next observation nontrivial half depth ordinal) :=
  A.canonical_next observation nontrivial half depth ordinal

noncomputable def pairedFace := Adapter.targetFace root visit u7 calculus reader
noncomputable def pairedState := Adapter.state root visit u7 calculus reader

theorem paired_state_source : type_of% (Retained.state_source root visit u7 calculus
    reader) :=
  Retained.state_source root visit u7 calculus reader

theorem paired_trace_source : type_of% (Retained.trace_source root visit u7 calculus
    reader) :=
  Retained.trace_source root visit u7 calculus reader

theorem original_trace_source : type_of% (paired_trace_source observation nontrivial half depth ordinal) :=
  paired_trace_source observation nontrivial half depth ordinal

theorem paired_paid : (pairedState observation nontrivial half depth ordinal).2.length = 5 :=
  Retained.paid root visit u7 calculus reader

noncomputable def pairedTrace := Retained.normalizedTrace root visit u7 calculus
  reader

private theorem paired_trace_paid : (pairedTrace observation nontrivial half depth ordinal).length = 5 :=
  Retained.normalized_paid root visit u7 calculus reader

private theorem paired_output :
    OC.value (root).toAuthoritativeRoot (visit).current reader =
      (S.result observation nontrivial half depth ordinal).2.2.1 :=
  trace_value (pairedTrace observation nontrivial half depth ordinal)
    (S.trace observation nontrivial half depth ordinal)

noncomputable def pairedInventory := PT.exposure (pairedState observation nontrivial half depth ordinal).2
noncomputable def pairedWords := PT.words (pairedState observation nontrivial half depth ordinal).2

private theorem paired_trace_words : type_of% (Retained.normalized_words root visit u7 calculus
    reader) :=
  Retained.normalized_words root visit u7 calculus reader

theorem paired_steps : (pairedWords observation nontrivial half depth ordinal).length = 5 :=
  Retained.word_count root visit u7 calculus reader

noncomputable def originalRInput := S.rInput observation nontrivial half depth ordinal

noncomputable def rCut := Trace.splitLinear (pairedTrace observation nontrivial half depth ordinal)

theorem r_cut_input : (rCut observation nontrivial half depth ordinal).input =
    (originalRInput observation nontrivial half depth ordinal).1 :=
  linear_cut_input (rCut observation nontrivial half depth ordinal)
    (originalRInput observation nontrivial half depth ordinal).2.1

private theorem r_child_steps : (rCut observation nontrivial half depth ordinal).trace.length = 4 := by
  have split := (rCut observation nontrivial half depth ordinal).length_eq
  have paid := paired_trace_paid observation nontrivial half depth ordinal
  exact Nat.add_right_cancel (split.symm.trans paid)

theorem original_R_equation : type_of% (S.r_equation observation nontrivial half depth ordinal) :=
  S.r_equation observation nontrivial half depth ordinal

/-- The five paid Steps stay in their Fin 2 language; only the new residual proceeds. -/
noncomputable def stockBase := Inventory.base (pairedInventory observation nontrivial half depth ordinal)
noncomputable def stockProgramme := AS.stockCfg (stockBase observation nontrivial half depth ordinal)
noncomputable def residualReceipt := Complete.receipt
  (stockProgramme observation nontrivial half depth ordinal) (sourceFrame observation nontrivial half depth ordinal) 0
noncomputable def settledFrame := Complete.atReceipt
  (stockProgramme observation nontrivial half depth ordinal) (sourceFrame observation nontrivial half depth ordinal) 0
noncomputable def bornFrame := Shared.nextBorn
  (settledFrame observation nontrivial half depth ordinal) (stockProgramme observation nontrivial half depth ordinal)

theorem residual_cost_exact : type_of% (Complete.receipt_distance_exact
    (stockProgramme observation nontrivial half depth ordinal) (sourceFrame observation nontrivial half depth ordinal) 0) :=
  Complete.receipt_distance_exact
    (stockProgramme observation nontrivial half depth ordinal) (sourceFrame observation nontrivial half depth ordinal) 0

noncomputable def residualPayment (index : Fin (residualReceipt observation nontrivial half depth ordinal).1) :=
  Complete.receipt_paid_prefix
    (stockProgramme observation nontrivial half depth ordinal) (sourceFrame observation nontrivial half depth ordinal) 0 index

theorem residual_compiles : type_of% (Complete.receipt_compiles
    (stockProgramme observation nontrivial half depth ordinal) (sourceFrame observation nontrivial half depth ordinal) 0) :=
  Complete.receipt_compiles
    (stockProgramme observation nontrivial half depth ordinal) (sourceFrame observation nontrivial half depth ordinal) 0

theorem canonical_birth : type_of% (Complete.receipt_next
    (stockProgramme observation nontrivial half depth ordinal) (sourceFrame observation nontrivial half depth ordinal) 0) :=
  Complete.receipt_next
    (stockProgramme observation nontrivial half depth ordinal) (sourceFrame observation nontrivial half depth ordinal) 0

noncomputable def sourceStock := AS.stockScalar
  (settledFrame observation nontrivial half depth ordinal) (stockBase observation nontrivial half depth ordinal)
noncomputable def bornStock := Native.bornStock
  (settledFrame observation nontrivial half depth ordinal) (stockBase observation nontrivial half depth ordinal)
noncomputable def feedEnvironment := AS.stockDecodedEnvironment
  (settledFrame observation nontrivial half depth ordinal) (stockBase observation nontrivial half depth ordinal)

theorem born_inventory : (bornFrame observation nontrivial half depth ordinal).inventory =
    some (bornStock observation nontrivial half depth ordinal) :=
  Native.born_stock
    (settledFrame observation nontrivial half depth ordinal) (stockBase observation nontrivial half depth ordinal)

theorem feed_cost_exact : type_of% (Native.complete_source_cost
    (settledFrame observation nontrivial half depth ordinal) (stockBase observation nontrivial half depth ordinal)) :=
  Native.complete_source_cost
    (settledFrame observation nontrivial half depth ordinal) (stockBase observation nontrivial half depth ordinal)

noncomputable def sourcePairedBlock : SourceInventoryTraceSegment
    (pairedInventory observation nontrivial half depth ordinal) (sourceStock observation nontrivial half depth ordinal) :=
  Inventory.sourceSegment (pairedInventory observation nontrivial half depth ordinal)
    (settledFrame observation nontrivial half depth ordinal)

noncomputable def sourcePairedOccurrence
    (index : Fin (pairedWords observation nontrivial half depth ordinal).length) :
    WR.RelationOccurrence (sourceStock observation nontrivial half depth ordinal) :=
  (PT.stepOccurrence (pairedState observation nontrivial half depth ordinal).2 index).transport
    (sourcePairedBlock observation nontrivial half depth ordinal)

theorem source_paired_word (index : Fin (pairedWords observation nontrivial half depth ordinal).length) :
    (sourcePairedOccurrence observation nontrivial half depth ordinal index).word =
      (pairedWords observation nontrivial half depth ordinal).get index :=
  transported_step_word (pairedState observation nontrivial half depth ordinal).2
    (sourcePairedBlock observation nontrivial half depth ordinal) index

theorem source_paired_position (index : Fin (pairedWords observation nontrivial half depth ordinal).length) :
    (sourcePairedOccurrence observation nontrivial half depth ordinal index).before.length =
      (sourcePairedBlock observation nontrivial half depth ordinal).before.length + (1 + index.val) :=
  ((PT.stepOccurrence (pairedState observation nontrivial half depth ordinal).2 index).transport_position
    (sourcePairedBlock observation nontrivial half depth ordinal)).trans
      (congrArg ((sourcePairedBlock observation nontrivial half depth ordinal).before.length + ·)
        (PT.stepOccurrence_before_length (pairedState observation nontrivial half depth ordinal).2 index))

noncomputable def pairedBlock : SourceInventoryTraceSegment
    (pairedInventory observation nontrivial half depth ordinal) (bornStock observation nontrivial half depth ordinal) :=
  Inventory.bornSegment (pairedInventory observation nontrivial half depth ordinal)
    (settledFrame observation nontrivial half depth ordinal)

noncomputable def pairedOccurrence
    (index : Fin (pairedWords observation nontrivial half depth ordinal).length) :
    WR.RelationOccurrence (bornStock observation nontrivial half depth ordinal) :=
  (PT.stepOccurrence (pairedState observation nontrivial half depth ordinal).2 index).transport
    (pairedBlock observation nontrivial half depth ordinal)

theorem paired_word (index : Fin (pairedWords observation nontrivial half depth ordinal).length) :
    (pairedOccurrence observation nontrivial half depth ordinal index).word =
      (pairedWords observation nontrivial half depth ordinal).get index :=
  transported_step_word (pairedState observation nontrivial half depth ordinal).2
    (pairedBlock observation nontrivial half depth ordinal) index

theorem paired_position (index : Fin (pairedWords observation nontrivial half depth ordinal).length) :
    (pairedOccurrence observation nontrivial half depth ordinal index).before.length =
      (pairedBlock observation nontrivial half depth ordinal).before.length + (1 + index.val) :=
  ((PT.stepOccurrence (pairedState observation nontrivial half depth ordinal).2 index).transport_position
    (pairedBlock observation nontrivial half depth ordinal)).trans
      (congrArg ((pairedBlock observation nontrivial half depth ordinal).before.length + ·)
        (PT.stepOccurrence_before_length (pairedState observation nontrivial half depth ordinal).2 index))

theorem paired_positions : StrictMono (fun index : Fin (pairedWords observation nontrivial half depth ordinal).length =>
    (pairedOccurrence observation nontrivial half depth ordinal index).before.length) := by
  intro first second ordered
  change (pairedOccurrence observation nontrivial half depth ordinal first).before.length <
    (pairedOccurrence observation nontrivial half depth ordinal second).before.length
  rw [paired_position, paired_position]
  exact Nat.add_lt_add_left (Nat.add_lt_add_left ordered 1) _

noncomputable def pairedOccurrences := List.ofFn
  (pairedOccurrence observation nontrivial half depth ordinal)

theorem paired_occurrences_words :
    (pairedOccurrences observation nontrivial half depth ordinal).map (fun occurrence => occurrence.word) =
      pairedWords observation nontrivial half depth ordinal :=
  transported_step_words (pairedState observation nontrivial half depth ordinal).2
    (pairedBlock observation nontrivial half depth ordinal)

noncomputable def lastRIndex : Fin (pairedWords observation nontrivial half depth ordinal).length :=
  ⟨4, by rw [paired_steps]; decide⟩

noncomputable def lastROccurrence := pairedOccurrence observation nontrivial half depth ordinal
  (lastRIndex observation nontrivial half depth ordinal)

theorem last_R_word : (lastROccurrence observation nontrivial half depth ordinal).word =
    Finsupp.single (.linear (s := ()) (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom
      (.const (s := ()) (originalRInput observation nontrivial half depth ordinal).1)) (1 : ℤ) -
      Finsupp.single (.const ((S.result observation nontrivial half depth ordinal).2.2.1)) 1 :=
  (paired_word observation nontrivial half depth ordinal
    (lastRIndex observation nontrivial half depth ordinal)).trans
      (linear_last_word_at (rCut observation nontrivial half depth ordinal)
        (pairedWords observation nontrivial half depth ordinal)
        (paired_trace_words observation nontrivial half depth ordinal)
        (lastRIndex observation nontrivial half depth ordinal)
        (r_child_steps observation nontrivial half depth ordinal)
        (originalRInput observation nontrivial half depth ordinal).1
        (S.result observation nontrivial half depth ordinal).2.2.1
        (r_cut_input observation nontrivial half depth ordinal)
        (paired_output observation nontrivial half depth ordinal))

theorem last_R_position : (lastROccurrence observation nontrivial half depth ordinal).before.length =
    (pairedBlock observation nontrivial half depth ordinal).before.length + 5 :=
  paired_position observation nontrivial half depth ordinal (lastRIndex observation nontrivial half depth ordinal)

end OriginalKPairedWaveNativeStockSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKPairedWaveNativeStockSource"
