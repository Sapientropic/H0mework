import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Window

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt inventory next query)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Option (Compile.RawInput Party Good Port Technology Instrument)
local notation "Word" => Script Party Good Port Technology Instrument

abbrev ScopeFailure (cut : C) := Public.Scope.Failure cut.native.input cut.native.depth
  cut.native.count cut.native.prefixLimit cut.native.renewalLimit cut.native.oldPast cut.native.actual.snapshot cut.executionRaw

abbrev scopeFailure (cut : C) := Public.Scope.failure? cut.native.input cut.native.depth
  cut.native.count cut.native.prefixLimit cut.native.renewalLimit cut.native.oldPast cut.native.actual.snapshot cut.executionRaw

abbrev ScopeNeed (cut : C) (failed : ScopeFailure cut) :=
  Material.NeedFloorIssue (Public.Scope.checkInput cut.native.input)
    (Capitalism.Universal.Abolition.Root.Actual.origin cut.native.input cut.native.depth cut.native.count)
    cut.raw (Public.Scope.scope cut.native.input cut.native.depth cut.native.count cut.native.prefixLimit
      cut.native.renewalLimit cut.native.oldPast cut.native.actual.snapshot failed.word) failed.word

/-- A named shortage from the actual period guard. Pending native work
takes precedence over a submitted material request. -/
structure NativeShortage (cut : C) (input : Input) where
  ready : ¬ Reparation.Transport.NativeWork (query cut input)
  failed : ScopeFailure (query cut input)
  generated : scopeFailure (query cut input) = some failed
  need : ScopeNeed (query cut input) failed
  reason : failed.issue = .originalNeed need

namespace NativeShortage

variable {cut : Root.Cut Party Good Port Technology Instrument}
  {input : Option (Compile.RawInput Party Good Port Technology Instrument)} (shortage : NativeShortage cut input)

abbrev cell : Party × Use × Good × ℚ := shortage.need.cell

def amount : ℚ :=
  let q := query cut input
  shortage.cell.2.2.2 - Material.actualUse (Public.Scope.checkInput q.native.input) q.raw
    shortage.failed.word shortage.cell.1 shortage.cell.2.1 shortage.cell.2.2.1

theorem positive : 0 < shortage.amount := sub_pos.mpr shortage.need.deficit

theorem rejected :
    let q := query cut input
    Public.Scope.inspect q.native.input q.native.depth q.native.count q.native.prefixLimit
      q.native.renewalLimit q.native.oldPast q.native.actual.snapshot q.executionRaw = .rejected shortage.failed := by
  let q := query cut input
  have read := shortage.generated
  change Public.Scope.failure? q.native.input q.native.depth q.native.count q.native.prefixLimit
    q.native.renewalLimit q.native.oldPast q.native.actual.snapshot q.executionRaw = some shortage.failed at read
  unfold Public.Scope.failure? at read
  dsimp only
  split at read
  · cases Option.some.inj read
    assumption
  · cases read
  · cases read

/-- The same rejected input is written by the original root. It leaves the
physical state, including its clock, untouched and retains the deferred input. -/
theorem rejected_tick_keeps_its_material_and_original_deferred_input
    (witness : NativeShortage cut input) :
    let q := query cut input
    (next cut input).raw = cut.raw ∧ inventory cut [input] = [] ∧
      Public.Scope.deferred q.native.input q.native.depth q.native.count q.native.prefixLimit
        q.native.renewalLimit q.native.oldPast q.native.actual.snapshot q.executionRaw = some q.executionRaw ∧
      Quantities.Recorded cut [input] := by
  let q := query cut input
  have material := Public.Scope.an_actual_scope_rejection_cannot_advance_the_physical_current
    q.native.input q.native.depth q.native.count q.native.prefixLimit q.native.renewalLimit
    q.native.oldPast q.native.actual.snapshot q.executionRaw witness.failed witness.rejected
  have kept := Public.Scope.every_actual_rejection_stops_and_keeps_its_original_residual
    q.native.input q.native.depth q.native.count q.native.prefixLimit q.native.renewalLimit
    q.native.oldPast q.native.actual.snapshot q.executionRaw witness.failed witness.rejected
  refine ⟨?_, ?_, kept.2.2, Quantities.record _ _⟩
  · change q.advance.raw = cut.raw
    rw [Evolving.Epoch.Current.advance_eq_epoch q witness.ready,
      Evolving.Epoch.Transition.next_state_reads_the_same_actual_material_target q witness.ready]
    exact (congrArg (fun state => state.raw) material.1).trans
      (congrArg (fun state => state.raw) (Quantities.Execution.query_physical cut input))
  · change Optimality.Programme.Epoch.materialItems q ++ [] = []
    unfold Optimality.Programme.Epoch.materialItems
    rw [if_neg witness.ready, show q.physicalResult.execution.items = [] from material.2]
    rfl

end NativeShortage

def inspectNativeShortage (cut : C) (input : Input) : Option (NativeShortage cut input) :=
  let q := query cut input
  if work : Reparation.Transport.NativeWork q then none
  else
    match observed : scopeFailure q with
    | none => none
    | some failed =>
      match reason : failed.issue with
      | .originalNeed need => some ⟨work, failed, observed, need, reason⟩
      | _ => none

theorem inspectNativeShortage_recognizes {cut : C} {input : Input}
    (issue : NativeShortage cut input) : inspectNativeShortage cut input = some issue := by
  rw [inspectNativeShortage, dif_neg issue.ready]
  split
  · rename_i absent
    cases absent.symm.trans issue.generated
  · rename_i found selected
    have same : found = issue.failed := Option.some.inj (selected.symm.trans issue.generated)
    subst found
    split
    · rename_i need reason
      have same := Review.Guarded.Issue.originalNeed.inj (reason.symm.trans issue.reason)
      subst need
      rfl
    · rename_i invalid
      exact (invalid _ issue.reason).elim


def NoNativeShortage : C → Word → Prop
  | _, [] => True
  | cut, input :: rest => inspectNativeShortage cut input = none ∧ NoNativeShortage (next cut input) rest

structure FirstNativeShortage (cut : C) (word : Word) where
  before : Word
  input : Input
  after : Word
  split : word = before ++ input :: after
  earlier : NoNativeShortage cut before
  issue : NativeShortage (endAt cut before) input

def firstNativeShortage : (cut : C) → (word : Word) → Option (FirstNativeShortage cut word)
  | _, [] => none
  | cut, input :: rest =>
    match observed : inspectNativeShortage cut input with
    | some issue => some ⟨[], input, rest, rfl, trivial, issue⟩
    | none => (firstNativeShortage (next cut input) rest).map fun later =>
        ⟨input :: later.before, later.input, later.after, congrArg (List.cons input) later.split,
          ⟨observed, later.earlier⟩, later.issue⟩

theorem no_first_native_shortage_iff_every_tick_passes (cut : C) (word : Word) :
    firstNativeShortage cut word = none ↔ NoNativeShortage cut word := by
  induction word generalizing cut with
  | nil => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | cons input rest ih =>
    rw [firstNativeShortage]
    split
    · rename_i issue observed
      simp only [NoNativeShortage, observed, reduceCtorEq, false_and]
    · rename_i observed
      simp only [NoNativeShortage, observed, true_and, Option.map_eq_none_iff, ih]

theorem FirstNativeShortage.original_prefix_and_next {cut : C} {word : Word}
    (first : FirstNativeShortage cut word) :
    word = (first.before ++ [first.input]) ++ first.after ∧
      (endAt cut (first.before ++ [first.input])).raw = (endAt cut first.before).raw ∧
      Quantities.Recorded cut (first.before ++ [first.input]) := by
  refine ⟨?_, ?_, Quantities.record _ _⟩
  · simpa only [List.append_assoc, List.singleton_append] using first.split
  · rw [Quantities.Execution.endAt_append]
    exact first.issue.rejected_tick_keeps_its_material_and_original_deferred_input.1

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence
