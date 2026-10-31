import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile.Migration

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase

open Source.Program PublicFunction
open Macro.Services

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (origin : Physical.Cursor Party Good Port Technology Instrument)
  (code : Admission.FeeCode (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- The successful check is attached to the already paid original fee
target. No constructor accepts a replacement target or continuation. -/
structure SelectedAt (current : Physical.Cursor Party Good Port Technology Instrument) where
  private mk ::
  before : Physical.Cursor Party Good Port Technology Instrument
  prior : PendingAt source depth count prefixLimit renewalLimit origin code before
  pair : Material.Migration.CodePair Party Good Port Technology Instrument
  tail : List (Material.Migration.CodePair Party Good Port Technology Instrument)
  head : prior.remaining = pair :: tail
  payment : Review.PaymentAt source.seed.law code.request
    (state source depth count prefixLimit renewalLimit before).raw
  paidCheck : Migration.Budget.Checks source depth count prefixLimit renewalLimit origin code
    (prior.paidCount + 1) payment.microNext pair
  generated : Migration.Budget.evaluate source depth count prefixLimit renewalLimit origin code
    prior.paidCount (state source depth count prefixLimit renewalLimit before).raw pair =
      .selected payment paidCheck
  actual : current = Migration.Budget.feeTarget before code

namespace SelectedAt

variable {source depth count prefixLimit renewalLimit origin code}
  {current : Physical.Cursor Party Good Port Technology Instrument}
  (selected : SelectedAt source depth count prefixLimit renewalLimit origin code current)

theorem checked : Migration.Budget.Checks source depth count prefixLimit renewalLimit origin code
    (selected.prior.paidCount + 1) (state source depth count prefixLimit renewalLimit current).raw selected.pair := by
  have raw := (congrArg (fun cut => (state source depth count prefixLimit renewalLimit cut).raw)
    selected.actual).trans (actual_fee_target source depth count prefixLimit renewalLimit code selected.before selected.payment)
  rw [raw]
  exact selected.paidCheck

theorem original_command_feed : Actual.Migration.Checks source.input
    (Actual.origin source.input depth count) (state source depth count prefixLimit renewalLimit current).raw
    (Actual.members source.input depth count) selected.pair :=
  Migration.Budget.checked_migration_keeps_every_original_livelihood source depth count prefixLimit renewalLimit
    origin code _ _ _ selected.checked

def frontInput := Physical.receive current (.migrate selected.pair)
def frontTarget := Physical.next selected.frontInput

theorem original_front_executes_and_locks_the_same_tail :
    (state source depth count prefixLimit renewalLimit selected.frontTarget).raw =
      source.seed.law.next (state source depth count prefixLimit renewalLimit current).raw selected.pair.1 ∧
    (state source depth count prefixLimit renewalLimit selected.frontTarget).phase = .renewal selected.pair.2 := by
  have same := Physical.consumed_input_generates_its_own_after source.input depth count prefixLimit renewalLimit selected.frontInput
  have checked := Compile.a_checked_migration_executes_its_front_and_fixes_its_own_tail
    source.input depth count prefixLimit renewalLimit (state source depth count prefixLimit renewalLimit current)
    selected.pair selected.original_command_feed
  change state source depth count prefixLimit renewalLimit selected.frontTarget = _ at same
  rw [same]
  exact checked.2.2

end SelectedAt

variable {origin code}
  {current : Physical.Cursor Party Good Port Technology Instrument}
  (pending : PendingAt source depth count prefixLimit renewalLimit origin code current)
  (pair : Material.Migration.CodePair Party Good Port Technology Instrument)
  (tail : List (Material.Migration.CodePair Party Good Port Technology Instrument))
  (head : pending.remaining = pair :: tail)

inductive FeeResult : Type
  | selected (selection : SelectedAt source depth count prefixLimit renewalLimit origin code
      (Migration.Budget.feeTarget current code))
  | rejected (payment : Review.PaymentAt source.seed.law code.request
      (state source depth count prefixLimit renewalLimit current).raw)
      (issue : Migration.Budget.Issue source depth count prefixLimit renewalLimit origin code
        (pending.paidCount + 1) payment.microNext pair)
      (generated : Migration.Budget.evaluate source depth count prefixLimit renewalLimit origin code
        pending.paidCount (state source depth count prefixLimit renewalLimit current).raw pair = .rejected payment issue)
      (after : PendingAt source depth count prefixLimit renewalLimit origin code
        (Migration.Budget.feeTarget current code))
      (after_exact : after = pending.afterRejected pair tail head payment issue generated)
  | blocked (obstruction : Review.Blockage source.seed.law code.request code.scope
      (state source depth count prefixLimit renewalLimit current).raw)
      (generated : Migration.Budget.evaluate source depth count prefixLimit renewalLimit origin code
        pending.paidCount (state source depth count prefixLimit renewalLimit current).raw pair = .blocked obstruction)

/-- This is the dependent result face of the original fee occurrence.
Only its literal physical target can carry the selected migration. -/
def afterFee : FeeResult source depth count prefixLimit renewalLimit pending pair tail head :=
  match generated : Migration.Budget.evaluate source depth count prefixLimit renewalLimit origin code
      pending.paidCount (state source depth count prefixLimit renewalLimit current).raw pair with
  | .selected payment checked =>
      .selected ⟨current, pending, pair, tail, head, payment, checked, generated, rfl⟩
  | .rejected payment issue => .rejected payment issue generated
      (pending.afterRejected pair tail head payment issue generated) rfl
  | .blocked obstruction => .blocked obstruction generated

theorem rejected_actual_step_removes_one_original_candidate
    (payment : Review.PaymentAt source.seed.law code.request
      (state source depth count prefixLimit renewalLimit current).raw)
    (issue : Migration.Budget.Issue source depth count prefixLimit renewalLimit origin code
      (pending.paidCount + 1) payment.microNext pair)
    (generated : Migration.Budget.evaluate source depth count prefixLimit renewalLimit origin code
      pending.paidCount (state source depth count prefixLimit renewalLimit current).raw pair = .rejected payment issue) :
    (pending.afterRejected pair tail head payment issue generated).remaining.length + 1 = pending.remaining.length ∧
    (pending.afterRejected pair tail head payment issue generated).paidCount = pending.paidCount + 1 := by
  change tail.length + 1 = pending.remaining.length ∧ _
  rw [head]
  exact ⟨rfl, rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase
