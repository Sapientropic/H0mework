import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.NativeShortage
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation.Shortage

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Transition.Handoff.Consumers.Continuation
  (start start_ready start_control withoutProvision MissingScope shortage the_same_cut_refuses_the_unfunded_word_and_preserves_the_original_row)
open Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)

noncomputable section

open private permitted_review_selects_the_period from H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Period

local notation "Raw" => Compile.RawInput Bool Bool Bool Unit Unit
local notation "Input" => Option Raw

def unfundedPeriod : Input := some (.execute withoutProvision)

private abbrev ShortageCut := Conflict.Root.Cut Bool Bool Bool Unit Unit
private abbrev submittedCut (cut : ShortageCut) := Quantities.Execution.query cut unfundedPeriod

private abbrev FailureAt (cut : ShortageCut) (raw : Raw) :=
  Public.Scope.Failure (submittedCut cut).native.input (submittedCut cut).native.depth (submittedCut cut).native.count
    (submittedCut cut).native.prefixLimit (submittedCut cut).native.renewalLimit (submittedCut cut).native.oldPast
    (submittedCut cut).native.actual.snapshot raw

private def sourceCoordinates (cut : ShortageCut) (raw : Raw) (failed : FailureAt cut raw) : Option (Bool × Use × Bool × ℚ) :=
  match failed.issue with
  | .originalNeed need =>
    let (person, purpose, good, due) := need.cell
    some (person, purpose, good, due - Material.actualUse (Public.Scope.checkInput (submittedCut cut).native.input)
      (submittedCut cut).raw failed.word person purpose good)
  | _ => none

private theorem the_original_coordinates_are_the_same_readout (cut : ShortageCut) (failed : MissingScope cut) :
    sourceCoordinates cut (.execute withoutProvision) failed = shortage cut failed := by
  unfold sourceCoordinates shortage
  have raw : (submittedCut cut).raw = cut.raw :=
    congrArg (fun state => state.raw) (Quantities.Execution.query_physical cut unfundedPeriod)
  have sameInput : (submittedCut cut).native.input = cut.native.input :=
    Quantities.Execution.query_input cut unfundedPeriod
  have sameUse (person : Bool) (purpose : Use) (good : Bool) :
      Material.actualUse (Public.Scope.checkInput (submittedCut cut).native.input) (submittedCut cut).raw
          failed.word person purpose good =
        Material.actualUse (Public.Scope.checkInput cut.native.input) cut.raw failed.word person purpose good :=
    congrArg₂ (fun input current => Material.actualUse (Public.Scope.checkInput input) current
      failed.word person purpose good) sameInput raw
  rcases failed with ⟨word, selected, issue⟩
  cases issue with
  | financial request present unsupported => rfl
  | period issue => rfl
  | originalNeed need =>
    exact congrArg (fun used => some (need.cell.1, need.cell.2.1, need.cell.2.2.1, need.cell.2.2.2 - used))
      (sameUse need.cell.1 need.cell.2.1 need.cell.2.2.1)

private theorem checked_original_source_coordinates (cut : ShortageCut)
    (ready : ¬ Reparation.Transport.NativeWork (submittedCut cut)) (raw : Raw) (selected : (submittedCut cut).executionRaw = raw)
    (failed : FailureAt cut raw)
    (generated : Public.Scope.failure? (submittedCut cut).native.input (submittedCut cut).native.depth (submittedCut cut).native.count
      (submittedCut cut).native.prefixLimit (submittedCut cut).native.renewalLimit (submittedCut cut).native.oldPast
      (submittedCut cut).native.actual.snapshot raw = some failed)
    (named : sourceCoordinates cut raw failed = some (false, .necessity, true, 1)) :
    ∃ witness : NativeShortage cut unfundedPeriod,
      (witness.cell.1, witness.cell.2.1, witness.cell.2.2.1, witness.amount) = (false, .necessity, true, 1) := by
  subst raw
  cases issue : failed.issue with
  | financial request present unsupported =>
    simp only [sourceCoordinates, issue, reduceCtorEq] at named
  | period obstruction =>
    simp only [sourceCoordinates, issue, reduceCtorEq] at named
  | originalNeed need =>
    let witness : NativeShortage cut unfundedPeriod := ⟨ready, failed, generated, need, issue⟩
    unfold sourceCoordinates at named
    rw [issue] at named
    have original := Option.some.inj named
    exact ⟨witness, original⟩

private theorem original_source_witness :
    ∃ witness : NativeShortage start unfundedPeriod,
      (witness.cell.1, witness.cell.2.1, witness.cell.2.2.1, witness.amount) = (false, .necessity, true, 1) := by
  obtain ⟨failed, named, original, _⟩ :=
    the_same_cut_refuses_the_unfunded_word_and_preserves_the_original_row.2.2.1
  have available : ReviewAvailable start := by
    unfold ReviewAvailable
    rw [start_control.2]
    trivial
  have selected : (submittedCut start).executionRaw = .execute withoutProvision :=
    permitted_review_selects_the_period start withoutProvision available
  exact checked_original_source_coordinates start start_ready _ selected failed original
    ((the_original_coordinates_are_the_same_readout start failed).trans named)

private theorem finds_the_singleton {cut : ShortageCut} {input : Input} (witness : NativeShortage cut input) :
    firstNativeShortage cut [input] = some ⟨[], input, [], rfl, trivial, witness⟩ := by
  have recognized := inspectNativeShortage_recognizes witness
  rw [firstNativeShortage]
  split
  · rename_i found selected
    cases Option.some.inj (selected.symm.trans recognized)
    rfl
  · rename_i absent
    cases absent.symm.trans recognized

/-- The existing source rejection supplies the exact missing unit at
clock six, before any new material item or period can occur. -/
theorem the_native_first_shortage_keeps_its_named_unit_and_unadvanced_clock :
    ∃ first : FirstNativeShortage start [unfundedPeriod],
      firstNativeShortage start [unfundedPeriod] = some first ∧
      first.before = [] ∧
      (first.issue.cell.1, first.issue.cell.2.1, first.issue.cell.2.2.1, first.issue.amount) =
        (false, .necessity, true, 1) ∧
      (Quantities.Execution.endAt start [unfundedPeriod]).raw.clock = 6 ∧
      Quantities.Execution.inventory start [unfundedPeriod] = [] ∧
      Quantities.Recorded start [unfundedPeriod] := by
  obtain ⟨witness, named⟩ := original_source_witness
  have prior := the_same_cut_refuses_the_unfunded_word_and_preserves_the_original_row
  exact ⟨⟨[], unfundedPeriod, [], rfl, trivial, witness⟩, finds_the_singleton witness,
    rfl, named, prior.1, prior.2.1, prior.2.2.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Consumers
