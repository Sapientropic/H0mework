import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Authority
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Horizon
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Defence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution
open Reparation.Actual (run publishAfter originalLosses Occurrence)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] [DecidableEq Community]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Item" => ExecutionItem Party Good Port M Instrument
local notation "Word" => RawEvent Party Good Port M Instrument
local notation "Script" => Reparation.Actual.Script Party Good Port M Instrument

variable {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

omit [DecidableEq Technology] in
theorem every_loss_is_readable_on_the_same_publication
    (seed : C) (community : Party → Community) (past suffix : Script)
    (origin : Occurrence seed community) (listed : origin ∈ originalLosses seed community (past ++ suffix)) :
    ∃ balance, ∃ row, (publishAfter (run seed community past) suffix).next.read row = .inr (origin, balance) := by
  rw [Reparation.Actual.publication_consumes_the_retained_visit]
  rw [← Reparation.Actual.the_live_ledger_contains_exactly_the_original_losses seed community] at listed
  obtain ⟨⟨found, balance⟩, present, rfl⟩ := List.mem_map.mp listed
  obtain ⟨row, exactRow⟩ := (run seed community (past ++ suffix)).every_balance_is_a_row_of_the_current _ present
  exact ⟨balance, row, exactRow⟩

/-- This publication distinguishes physically written refusal from lawful
restoration and reads new and old losses at the literal successor. The
crossed horizon remains closed under every continuation. -/
theorem the_original_publication_audits_restoration_after_release
    (seed : C) (community : Party → Community) (past suffix : Script)
    (installed : Emergency.Installed seed base scope)
    (released : Civil.Mandate.Released (endAt seed past).raw) :
    let cut := endAt seed past
    let written := publishAfter (run seed community past) suffix
    let reached := endAt seed (past ++ suffix)
    Quantities.Recorded seed (past ++ suffix) ∧
    (∀ origin ∈ originalLosses seed community (past ++ suffix),
      ∃ balance, ∃ row, written.next.read row = .inr (origin, balance)) ∧
    (match Emergency.inspectAuthority cut suffix with
    | .refused item _ _ =>
        item ∈ inventory cut suffix ∧ ¬ cut.native.input.law.Valid item.before item.request
    | .authorized _ =>
        (∀ candidate, reached.raw.technology.holder = some candidate →
          LiveGrant base scope (inventory cut suffix) candidate) ∧
        ∀ (front : List Item) (item : Item) (back : List Item),
          inventory cut suffix = front ++ item :: back →
          ∀ debit : (Party × Good) × ℚ,
            debit ∈ (PublicFunction.physicalLaw cut.native.input.law).actualDebit item.before item.request →
            base.stockPort cut.raw.technology.technology debit.1.1 debit.1.2 = scope.service →
            LiveGrant base scope front item.request.signer ∧
              (Emergency.Ordinary item.request →
                scope.task.earliest ≤ item.before.clock ∧ item.before.clock ≤ scope.task.deadline)) ∧
    (scope.task.deadline < cut.raw.clock →
      scope.task.deadline < reached.raw.clock ∧
      ∀ word : Word, ∀ command : ActualCommand base scope reached.raw word,
        command.command ≠ .accept ∧ command.command ≠ .renew ∧
        ∀ candidate, command.command ≠ .propose candidate) := by
  dsimp only
  refine ⟨(publishAfter (run seed community past) suffix).recorded,
    every_loss_is_readable_on_the_same_publication seed community past suffix, ?_, ?_⟩
  · cases Emergency.inspectAuthority (endAt seed past) suffix with
    | refused item listed refused => exact ⟨listed, refused⟩
    | authorized checked =>
      refine ⟨?_, ?_⟩
      · rw [endAt_append]
        exact the_actual_successor_holder_has_original_grant _ suffix (installed.along past) released checked
      · exact the_actual_protected_debit_has_original_grant _ suffix (installed.along past) released checked
  · intro crossed
    exact (Reparation.Actual.the_joint_successor_keeps_every_original_loss_and_the_crossed_horizon
      installed community past suffix crossed).2.2.2

omit [DecidableEq Technology] in
/-- A locally paid defence retains its original independent exit and every
loss from the same generated successor. -/
theorem the_original_defence_keeps_its_exit_on_the_reparation_successor
    (seed source : C) (community : Party → Community) (past : Script)
    {attackWord response continuation : Word} (attack : Boundary.AggressionAt source attackWord community)
    (atAttack : endAt seed past = attack.after)
    (defended : Boundary.DefenceAt attack response continuation) :
    let suffix := primitiveScript response
    let written := publishAfter (run seed community past) suffix
    let reached := endAt seed (past ++ suffix)
    Quantities.Recorded seed (past ++ suffix) ∧
    Boundary.ExitFloorAt source reached attack.residents continuation ∧
    (∀ origin ∈ originalLosses seed community (past ++ suffix),
      ∃ balance, ∃ row, written.next.read row = .inr (origin, balance)) := by
  dsimp only
  refine ⟨(publishAfter (run seed community past) (primitiveScript response)).recorded, ?_,
    every_loss_is_readable_on_the_same_publication seed community past (primitiveScript response)⟩
  rw [endAt_append, atAttack]
  exact defended.independentExit

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal
