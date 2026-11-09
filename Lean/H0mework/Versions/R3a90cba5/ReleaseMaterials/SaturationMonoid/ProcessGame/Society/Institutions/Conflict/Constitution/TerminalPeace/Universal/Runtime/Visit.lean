import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Native
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Select

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (StateAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good]
  [DecidableEq Instrument] [DecidableEq Community]

abbrev Native (Party Good Port Technology Instrument : Type) :=
  Capitalism.Universal.Abolition.Root.Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)

/-- A due visit reads the actual before-state and its submitted finite
programme. The choice and the written inventory are computed here. -/
structure Attempt (input : ProgrammeSource.Input Party Good Port Technology Instrument) (origin : RawCurrent Party Good Technology Instrument) (roster : List Party) where
  before : Native Party Good Port Technology Instrument
  offers : List (RawEvent Party Good Port Technology Instrument)

namespace Attempt

variable {input : ProgrammeSource.Input Party Good Port Technology Instrument} {origin : RawCurrent Party Good Technology Instrument} {roster : List Party}
  (attempt : Attempt input origin roster)

def selected (attempt : Attempt input origin roster) :
    Supply.Selection input origin attempt.before.raw roster attempt.offers := by
  exact Supply.select input origin attempt.before.raw roster attempt.offers

def after : Native Party Good Port Technology Instrument :=
  match attempt.selected with
  | .paid position _ _ => (Physical.Public.compile input attempt.before (.execute attempt.offers[position])).next
  | .blocked _ => attempt.before

def items : List (ExecutionItem Party Good Port Technology Instrument) :=
  match attempt.selected with
  | .paid position _ _ => (Physical.Public.compile input attempt.before (.execute attempt.offers[position])).execution.items
  | .blocked _ => []

def Succeeds : Prop := ∃ position paid earlier,
  attempt.selected = .paid position paid earlier

def Refused : Prop := ∃ failure, attempt.selected = .blocked failure

theorem fails_iff :
    attempt.Refused ↔
      ∀ word ∈ attempt.offers, ¬ Supply.Period input origin attempt.before.raw roster word :=
  Supply.the_original_menu_is_blocked_iff_no_submitted_word_pays _ _ _ _ _

theorem pays_or_refuses : attempt.Succeeds ∨ attempt.Refused := by
  cases actual : attempt.selected with
  | paid position paid earlier => exact .inl ⟨position, paid, earlier, actual⟩
  | blocked failure => exact .inr ⟨failure, actual⟩

theorem refusal_has_no_physical_effect (refused : attempt.Refused) :
    attempt.after = attempt.before ∧ attempt.items = [] := by
  obtain ⟨_, failed⟩ := refused
  simp only [after, items, failed, and_self]

theorem accepted_effect (success : attempt.Succeeds) :
    ∃ position : Fin attempt.offers.length,
      let word := attempt.offers[position]
      Supply.Period input origin attempt.before.raw roster word ∧
      attempt.items = input.law.rawItems attempt.before.raw word ∧
      attempt.after = {attempt.before with raw := input.law.next attempt.before.raw word} := by
  obtain ⟨position, paid, _, selected⟩ := success
  have compiled := paid.native_write attempt.before
  refine ⟨position, paid, ?_, ?_⟩
  · unfold items
    rw [selected]
    exact congrArg ExecutionResult.items compiled.2.1
  · unfold after
    rw [selected]
    exact compiled.2.2

theorem no_actual_damage (community : Party → Community) :
    ∀ item ∈ attempt.items, ∀ key, Reparation.loss input.law community item key = 0 := by
  intro item written key
  rcases attempt.pays_or_refuses with success | failed
  · obtain ⟨_, paid, actualItems, _⟩ := attempt.accepted_effect success
    exact (paid.own item (actualItems ▸ written)).opens_no_coercive_loss community key
  · rw [(attempt.refusal_has_no_physical_effect failed).2] at written
    exact (List.not_mem_nil written).elim

theorem original_time_never_decreases :
    attempt.before.raw.clock ≤ (attempt.after).raw.clock := by
  rcases attempt.pays_or_refuses with success | failed
  · obtain ⟨_, paid, _, native⟩ := attempt.accepted_effect success
    rw [native]
    change attempt.before.raw.clock ≤ (input.law.next attempt.before.raw _).clock
    rw [paid.exact_clock]
    exact le_add_of_nonneg_right paid.positiveClock.le
  · rw [(attempt.refusal_has_no_physical_effect failed).1]

end Attempt

variable [DecidableEq Port]

abbrev RootWrite (seed : Conflict.Root.Cut Party Good Port Technology Instrument) (community : Party → Community) (cut : Conflict.Root.Cut Party Good Port Technology Instrument)
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (origin : RawCurrent Party Good Technology Instrument) (roster : List Party) :=
  Installation.Core.Landed seed community cut (Attempt input origin roster)

variable {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {origin : RawCurrent Party Good Technology Instrument} {roster : List Party}

def commit (prior : StateAt seed community cut)
    (attempt : Attempt input origin roster) : RootWrite seed community cut input origin roster :=
  Installation.Core.publish (seed := seed) (cut := cut) (community := community) prior attempt true

theorem commit_writes_the_same_original_whole_successor (prior : StateAt seed community cut)
    (attempt : Attempt input origin roster) :
    (⟨prior.world, (Installation.Core.action prior attempt true).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = (commit prior attempt).state.resident.erase :=
  Installation.Core.the_canonical_write_is_the_published_whole_state prior attempt true

theorem commit_reads_its_exact_attempt (prior : StateAt seed community cut)
    (attempt : Attempt input origin roster) :
    (commit prior attempt).read = attempt :=
  Installation.Core.publish_reads_the_exact_payload prior attempt true

theorem commit_retains_the_whole_stack (prior : StateAt seed community cut)
    (attempt : Attempt input origin roster) :
    (commit prior attempt).state.stack = prior.stack :=
  Installation.Core.publish_preserves_the_entire_stack prior attempt true

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime
