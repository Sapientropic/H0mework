import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Continue
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.GuardedPublication

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt endAt_append inventory)
open Reparation.Actual (originalLosses)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]

namespace EffectiveRelease

variable {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {seed submitted : Root.Cut Party Good Port (State Party Technology) Instrument} {actor : Party}
  {word : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  (release : EffectiveRelease base scope seed submitted actor word)
  (community : Party → Community)
  (attempts : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)

abbrev admittedSuffix :=
  Renewal.guardedHistory (endAt seed release.releasedPrefix) attempts

def dispatchAfterRelease :=
  release.continueWith community (release.admittedSuffix attempts)

/-- Every repeated submission uses the successor written by the paid
withdrawal. A restored holder requires fresh independent payments. -/
theorem the_same_paid_root_checks_every_restoration_and_keeps_the_hard_horizon
    (installed : Emergency.Installed seed base scope) :
    let original := endAt seed release.releasedPrefix
    let suffix := release.admittedSuffix attempts
    let reached := endAt seed (release.releasedPrefix ++ suffix)
    let written := release.dispatchAfterRelease community attempts
    Quantities.Recorded seed (release.releasedPrefix ++ suffix) ∧
    (∀ loss ∈ originalLosses seed community (release.releasedPrefix ++ suffix),
      ∃ balance, ∃ row, written.next.read row = .inr (loss, balance)) ∧
    (∀ candidate, reached.raw.technology.holder = some candidate ↔
      Renewal.LiveGrant base scope (inventory original suffix) candidate) ∧
    (∀ signer, (∀ item ∈ inventory original suffix, item.request.signer = signer) →
      reached.raw.technology.holder = none) ∧
    (scope.task.deadline < original.raw.clock → scope.task.deadline < reached.raw.clock ∧
      ∀ requests : RawEvent Party Good Port (State Party Technology) Instrument,
      ∀ command : ActualCommand base scope reached.raw requests, command.command ≠ .accept ∧
        command.command ≠ .renew ∧ ∀ nominee, command.command ≠ .propose nominee) := by
  let original := endAt seed release.releasedPrefix
  let suffix := release.admittedSuffix attempts
  have licensed := Renewal.every_guarded_history_has_source_authority original attempts
  have writes := release.the_paid_successor_carries_authority_and_every_original_victim_into_its_next_write
    community suffix installed licensed.original_authority
  refine ⟨writes.1, writes.2.1, writes.2.2, ?_, ?_⟩
  · intro signer alone
    rw [endAt_append]
    exact Renewal.one_signer_cannot_restore_after_any_admitted_history original suffix
      (installed.along release.releasedPrefix) release.the_literal_paid_successor_has_no_holder_or_offer
      licensed signer alone
  · intro crossed
    exact (Reparation.Actual.the_joint_successor_keeps_every_original_loss_and_the_crossed_horizon
      installed community release.releasedPrefix suffix crossed).2.2.2

end EffectiveRelease

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
