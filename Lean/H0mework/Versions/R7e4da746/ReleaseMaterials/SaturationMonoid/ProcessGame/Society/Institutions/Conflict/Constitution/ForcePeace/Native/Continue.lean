import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Effective
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Recurrence
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Root

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt endAt_append inventory)
open Reparation.Actual (publishAfter run SourceAuthority originalLosses)

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

abbrev releasedPrefix := release.before ++ [withdrawalInput scope submitted actor]

theorem the_literal_paid_successor_has_no_holder_or_offer :
    Civil.Mandate.Released (endAt seed release.releasedPrefix).raw := by
  rw [endAt_append]
  exact release.receipt.released

def write :=
  publishAfter (run seed community release.before) [withdrawalInput scope submitted actor]

theorem the_paid_withdrawal_writes_its_literal_original_successor :
    (release.write community).next = run seed community release.releasedPrefix :=
  Reparation.Actual.publication_consumes_the_retained_visit _ _ _ _

def continueWith (suffix : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument) :=
  publishAfter (release.write community).next suffix

theorem the_paid_successor_carries_authority_and_every_original_victim_into_its_next_write
    (suffix : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)
    (installed : Emergency.Installed seed base scope)
    (authorized : SourceAuthority (endAt seed release.releasedPrefix) suffix) :
    let original := endAt seed release.releasedPrefix
    let written := release.continueWith community suffix
    Quantities.Recorded seed (release.releasedPrefix ++ suffix) ∧
    (∀ loss ∈ originalLosses seed community (release.releasedPrefix ++ suffix),
      ∃ balance, ∃ row, written.next.read row = .inr (loss, balance)) ∧
    (∀ candidate, (endAt seed (release.releasedPrefix ++ suffix)).raw.technology.holder = some candidate ↔
      Renewal.LiveGrant base scope (inventory original suffix) candidate) := by
  refine ⟨(release.continueWith community suffix).recorded, ?_, ?_⟩
  · unfold continueWith
    rw [release.the_paid_withdrawal_writes_its_literal_original_successor community]
    exact Renewal.every_loss_is_readable_on_the_same_publication _ _ _ _
  · intro candidate
    rw [endAt_append]
    exact Renewal.the_actual_holder_is_equivalent_to_a_live_paid_grant_after_release
      _ suffix (installed.along release.releasedPrefix)
      release.the_literal_paid_successor_has_no_holder_or_offer authorized candidate

end EffectiveRelease

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
