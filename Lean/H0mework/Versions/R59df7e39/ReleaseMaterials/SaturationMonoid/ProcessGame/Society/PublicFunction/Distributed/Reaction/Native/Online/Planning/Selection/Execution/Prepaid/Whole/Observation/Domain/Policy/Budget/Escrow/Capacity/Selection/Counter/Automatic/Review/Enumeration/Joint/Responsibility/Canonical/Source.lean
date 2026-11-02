import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Responsibility
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawRootDebtAdmissionActualActionKernel

/-! One source-owned ledger extension of the exact paid report. The first
move shares the original base successor; remaining paid bookkeeping moves
keep that base visit fixed. At the actual paid-prefix boundary the base
programme resumes, carrying the unfinished computation debt without refill. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Responsibility.Canonical
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger DebtAdmissionFirstWrite
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {generatedSource : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue generatedSource.snapshot} {all : Candidates generatedSource catalogue} {owner : Ready all}
  (made : Generated owner) (index : Index prepared) (first : First made)

abbrev cursor := made.endpoint index
abbrev oldInput := (cursor made index).source.val.input
abbrev oldRoot := Online.Runtime.root (cursor made index)
abbrev originDepth := (cursor made index).depth

theorem origin_positive : 0 < originDepth made index := by
  change 0 < (cursor made index).source.val.history.length+1+(cursor made index).count
  omega

def baseOffset (tick : Nat) := if tick = 0 then 0 else 1+(tick-made.execution.work.length)
def oldCurrent (tick : Nat) :=
  (ProgrammeHistory.visitAt (oldInput made index) (originDepth made index+baseOffset made tick)).current

theorem oldCurrent_running (tick : Nat) :
    ∃ current past,oldCurrent made index tick = ProgrammeSource.Current.running current past := by
  have positive := origin_positive made index
  have past := ProgrammeHistory.past_length (oldInput made index) (originDepth made index+baseOffset made tick)
  cases actual : oldCurrent made index tick with
  | bootstrap =>
      change (ProgrammeSource.pastAt (oldCurrent made index tick)).length = _ at past
      rw [actual] at past
      change 0 = _ at past
      omega
  | running current past => exact ⟨current,past,rfl⟩

def position (tick : Nat) := min tick made.execution.work.length
def state (tick : Nat) : State owner := (execute owner (position made tick) (initial owner)).endpoint

def paidStep (tick : Nat) (paid : tick < made.execution.work.length) :
    (law owner).StepAt (state made tick) (state made (tick+1)) := by
  refine ⟨made.execution.work[tick],⟨?_⟩⟩
  have actual := made.execution.history.actual_prefix_step ⟨tick,paid⟩
  have before : position made tick = tick := by dsimp only [position];omega
  have after : position made (tick+1) = tick+1 := by dsimp only [position];omega
  change move owner (execute owner (position made tick) (initial owner)).endpoint =
    some ((execute owner (position made (tick+1)) (initial owner)).endpoint,made.execution.work[tick])
  rw [before,after]
  exact actual

theorem state_after_prefix (tick : Nat) (done : made.execution.work.length ≤ tick) :
    state made (tick+1) = state made tick := by
  have same : position made (tick+1) = position made tick := by dsimp only [position];omega
  exact congrArg (fun n => (execute owner n (initial owner)).endpoint) same

theorem budget_never_refills (tick : Nat) :
    (law owner).budget (state made (tick+1)) ≤ (law owner).budget (state made tick) := by
  by_cases paid : tick < made.execution.work.length
  · exact ((law owner).step_budget_lt (paidStep made tick paid)).le
  · rw [state_after_prefix made tick (by omega)]

include first in
theorem first_base_successor : oldCurrent made index 1 =
    ProgrammeSource.next (oldInput made index) (oldCurrent made index 0) := by
  have nonempty := first.nonempty
  simp only [oldCurrent,baseOffset,if_neg (by omega : (1:Nat) ≠ 0)]
  have difference : 1-made.execution.work.length = 0 := by omega
  rw [difference]
  rfl

theorem bookkeeping_does_not_reexecute (tick : Nat) (positive : 0 < tick)
    (paid : tick < made.execution.work.length) : oldCurrent made index (tick+1) = oldCurrent made index tick := by
  have a : tick-made.execution.work.length = 0 := by omega
  have b : tick+1-made.execution.work.length = 0 := by omega
  simp only [oldCurrent,baseOffset,if_neg (by omega : tick ≠ 0),if_neg (by omega : tick+1 ≠ 0),a,b]

include first in
theorem tail_uses_original_successor (tick : Nat) (done : made.execution.work.length ≤ tick) :
    oldCurrent made index (tick+1) = ProgrammeSource.next (oldInput made index) (oldCurrent made index tick) := by
  have positive := first.nonempty
  have offset : baseOffset made (tick+1) = baseOffset made tick+1 := by
    simp only [baseOffset,if_neg (by omega : tick ≠ 0),if_neg (by omega : tick+1 ≠ 0)]
    omega
  change (ProgrammeHistory.visitAt _ (originDepth made index+baseOffset made (tick+1))).current = _
  rw [offset,←Nat.add_assoc]
  rfl

def BaseAdvance (tick : Nat) : Prop := tick = 0 ∨ made.execution.work.length ≤ tick
instance (tick : Nat) : Decidable (BaseAdvance made tick) := inferInstanceAs (Decidable (tick = 0 ∨ made.execution.work.length ≤ tick))

include first in
theorem enabled_base_uses_actual_next (tick : Nat) (enabled : BaseAdvance made tick) :
    oldCurrent made index (tick+1) = ProgrammeSource.next (oldInput made index) (oldCurrent made index tick) := by
  rcases enabled with zero | done
  · subst tick
    exact first_base_successor made index first
  · exact tail_uses_original_successor made index first tick done

theorem bookkeeping_disables_base (tick : Nat) (positive : 0 < tick) (paid : tick < made.execution.work.length) :
    ¬ BaseAdvance made tick := by unfold BaseAdvance;omega

abbrev N := ExtendedNetwork (ProgrammeSource.N (oldInput made index)) (law owner)
def supportAt (tick : Nat) : (N made index).Support :=
  ⟨ProgrammeSource.supportAt (oldInput made index) (oldCurrent made index tick),some (state made tick)⟩

abbrev V : ConstructiveRoot.Vocabulary where
  Current := Nat
  Anchor := Unit
  Incidence := Bool
  Lineage := Unit
  anchorAt := fun _ => ()
  incidenceAt := fun tick => (N made index).incidenceAt (supportAt made index tick)
  lineageAt := fun _ => ()
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {tick} _ => tick+1
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

inductive Event : Nat → (N made index).Support → Type
  | emitted (tick : Nat) : Event tick (supportAt made index tick)

def sourceLaw : SourceNativeEventAlgebra (N made index) (V made index) where
  EventAt := Event made index
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun {_} {support} _ => OpenResponsibilityAt (N made index) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro tick support event;cases event;rfl
  incidence_commutes := by intro tick support event;cases event;rfl
  lineage_commutes := by intro tick support event;cases event;rfl

def source : SourceNativeSource (N made index) (V made index) where
  initial := first.row.ordinal.val
  law := sourceLaw made index

def emitted (tick : Nat) : (source made index first).toRootSource.actual.OccurrenceAt tick :=
  ⟨supportAt made index tick,.emitted tick⟩

theorem occurrence_eq_emitted {tick : Nat} (event : (source made index first).toRootSource.actual.OccurrenceAt tick) :
    event = emitted made index first tick := by rcases event with ⟨support,event⟩;cases event;rfl

def originalOccurrence (tick : Nat) := (oldRoot made index).emitted (oldCurrent made index tick)

def receipt (tick : Nat) : (N made index).DispositionAt (supportAt made index tick) .transfer :=
  if paid : tick < made.execution.work.length then
    debtStepReceipt (ProgrammeSource.supportAt (oldInput made index) (oldCurrent made index tick)) (paidStep made tick paid)
  else .inl (ProgrammeWorld.transferReceipt (ProgrammeSource.observation? (oldInput made index))
    (ProgrammeSource.supportAt (oldInput made index) (oldCurrent made index tick)))

def inheritedReceipt (tick : Nat) : (N made index).DispositionAt (supportAt made index tick) .transfer :=
  if BaseAdvance made tick then
    .inl (ProgrammeWorld.transferReceipt (ProgrammeSource.observation? (oldInput made index))
      (ProgrammeSource.supportAt (oldInput made index) (oldCurrent made index tick)))
  else receipt made index tick

theorem inherited_receipt_on_base (tick : Nat) (enabled : BaseAdvance made tick) :
    inheritedReceipt made index tick = .inl (ProgrammeWorld.transferReceipt (ProgrammeSource.observation? (oldInput made index))
      (ProgrammeSource.supportAt (oldInput made index) (oldCurrent made index tick))) := by
  simp only [inheritedReceipt,if_pos enabled]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Responsibility.Canonical
