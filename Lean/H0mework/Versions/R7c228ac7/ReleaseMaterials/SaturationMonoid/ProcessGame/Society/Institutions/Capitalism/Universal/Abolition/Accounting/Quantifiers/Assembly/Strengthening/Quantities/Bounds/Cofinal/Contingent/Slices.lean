import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent.Tight
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System.Slices

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent.Slices

open Abolition.Root Abolition.Root.Registered Execution
open Bounds.System
open Recovery.Robust.Recurring (run)

noncomputable section

universe w

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Event Signal Key Address : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Request" => Option (Compile.RawInput Party Good Port Technology Instrument)
local notation "Script" => List Request
local notation "Exposure" => Nat → C → Event → Script
local notation "Observation" => Nat → C → Signal
local notation "Selection" => Nat → C → Bounds.System.Slices.Selection Request Key

variable {Issue : Nat → Key → Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument) →
    List (Option (Compile.RawInput Party Good Port Technology Instrument)) → Type w}

def inspectStage (locate : Selection)
    (inquiry : ∀ stage, Bounds.System.Slices.LocalInquiry C Request (Issue stage))
    (stage : Nat) (current : C) (word : Script) :
    Option (System.Failure (Bounds.System.Slices.inspect current (locate stage current) (inquiry stage)) word) :=
  System.inspect (Bounds.System.Slices.inspect current (locate stage current) (inquiry stage)) word

def readStage (locate : Selection) (owner : Address → Key)
    (read : Nat → Address → C → Script → EReal) (stage : Nat) (current : C) (word : Script) : Address → EReal :=
  Bounds.System.Slices.readAt current (locate stage current) owner (read stage) word

theorem a_stage_checks_every_required_slice_on_its_exact_original_cut
    (locate : Selection) (inquiry : ∀ stage, Bounds.System.Slices.LocalInquiry C Request (Issue stage))
    (stage : Nat) (current : C) (word : Script) :
    inspectStage locate inquiry stage current word = none ↔
      ∀ key, ∃ slice, locate stage current word key = some slice ∧
        inquiry stage key (slice.current current word) (slice.body word) = none ∧
        Recorded (slice.current current word) (slice.body word) ∧
        (type_of% (slice.read_at_the_end_of_a_slice_uses_the_literal_original_successor current word)) := by
  unfold inspectStage
  rw [all_checks_pass_exactly_when_there_is_no_failure]
  constructor
  · intro all key
    obtain ⟨slice, original, clear⟩ :=
      (Bounds.System.Slices.a_required_slice_is_paid_exactly_at_its_original_cut _ _ _ _ _).mp (all key)
    exact ⟨slice, original, clear, record _ _, slice.read_at_the_end_of_a_slice_uses_the_literal_original_successor current word⟩
  · intro all key
    obtain ⟨slice, original, clear, _, _⟩ := all key
    exact (Bounds.System.Slices.a_required_slice_is_paid_exactly_at_its_original_cut _ _ _ _ _).mpr ⟨slice, original, clear⟩

/-- One policy must settle every actual branch and every original inquiry
in that branch. The complete domain retains the whole original word, its
local slices and the root-generated next at each stage. -/
theorem the_complete_contingent_domain_uses_only_original_quantities_at_paid_cuts
    (source : C) (expose : Exposure) (observe : Observation)
    (locate : Selection) (inquiry : ∀ stage, Bounds.System.Slices.LocalInquiry C Request (Issue stage))
    (owner : Address → Key)
    (read : Nat → Address → C → Script → EReal) (profile : Address → EReal) :
    profile ∈ values source expose observe (inspectStage locate inquiry) (readStage locate owner read) ↔
      ∃ policy, Nonempty (Nat → Event) ∧ peak source expose observe policy (readStage locate owner read) = profile ∧
        (∀ events, ClockCofinal source (run expose observe policy events)) ∧
        ∀ events stage,
          let branch := run expose observe policy events
          let current := stageAt source branch stage
          let word := stageBody source branch stage
          Recorded source (stageScript source branch stage) ∧ Settled current word ∧
            stageAt source branch (stage + 1) = endAt current word ∧
            (∀ key, ∃ slice, locate stage current word key = some slice ∧
              inquiry stage key (slice.current current word) (slice.body word) = none ∧
              Recorded (slice.current current word) (slice.body word) ∧
              (type_of% (slice.read_at_the_end_of_a_slice_uses_the_literal_original_successor current word))) := by
  constructor
  · rintro ⟨policy, paid, rfl⟩
    refine ⟨policy, paid.hasInput, rfl, fun events => (paid.actual events).time, ?_⟩
    intro events stage
    have actual := paid.actual events
    obtain ⟨original, settled, next⟩ := a_paid_stage_writes_the_original_whole_ledger_into_the_next_stage
      source _ (inspectStage locate inquiry) actual stage
    exact ⟨original, settled, next,
      (a_stage_checks_every_required_slice_on_its_exact_original_cut _ _ _ _ _).mp (actual.passes stage)⟩
  · rintro ⟨policy, input, rfl, cofinal, all⟩
    refine ⟨policy, ⟨input, fun events => ?_⟩, rfl⟩
    exact ⟨fun stage => (all events stage).2.1,
      fun stage => (a_stage_checks_every_required_slice_on_its_exact_original_cut _ _ _ _ _).mpr
        (all events stage).2.2.2, cofinal events⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent.Slices
