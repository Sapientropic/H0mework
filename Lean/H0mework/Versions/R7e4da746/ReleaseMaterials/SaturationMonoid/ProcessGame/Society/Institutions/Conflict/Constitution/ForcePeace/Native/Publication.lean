import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Release
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)
open PublicFunction.Mandate
open Reparation.Actual (run)
open Quantities.Execution

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "L" => RawLaw Party Good Port Technology Instrument
local notation "J" => Scope (Party := Party) (Good := Good) (Port := Port)
local notation "Input" => Reparation.Actual.Input Party Good Port (State Party Technology) Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port (State Party Technology) Instrument
local notation "Rival" => Nat → C → Input

variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))
  (cut : Root.Cut Party Good Port (State Party Technology) Instrument) (actor : Party)
  (rival : Nat → Root.Cut Party Good Port (State Party Technology) Instrument →
    Reparation.Actual.Input Party Good Port (State Party Technology) Instrument)

abbrev atReservedVisit := endAt cut (queuedPrefix cut (withdrawalInput scope cut actor) rival)

inductive ReleaseDecision
  | paid (receipt : ReleaseReceipt base scope cut (atReservedVisit scope cut actor rival) actor)
  | reviewBlocked (blocked : ¬ ReviewAvailable (atReservedVisit scope cut actor rival))
  | feeBlocked (issue : FeeShortage scope (atReservedVisit scope cut actor rival) actor)
      (refused : ¬ (law base scope).Valid (atReservedVisit scope cut actor rival).raw (withdrawal scope cut actor))
  | authorityBlocked
      (refused : ¬ (law base scope).Valid (atReservedVisit scope cut actor rival).raw (withdrawal scope cut actor))
      (feeFits : feeShortage scope (atReservedVisit scope cut actor rival) actor = none)

def releaseDecision (installed : Emergency.Installed cut base scope) :
    ReleaseDecision base scope cut actor rival := by
  let reached := atReservedVisit scope cut actor rival
  have first := the_first_material_visit_is_reserved_at_the_same_physical_cut cut (withdrawalInput scope cut actor) rival
  if review : ReviewAvailable reached then
    if valid : (law base scope).Valid reached.raw (withdrawal scope cut actor) then
      exact .paid (release_at_the_original_material_visit actor (installed.along _) first.1 review valid)
    else
      match read : feeShortage scope reached actor with
      | some issue => exact .feeBlocked issue valid
      | none => exact .authorityBlocked valid read
  else
    exact .reviewBlocked review

/-- Preserve the typed refusal without forwarding an unlicensed
revision to the physical interpreter. -/
def dispositionInput (decision : ReleaseDecision base scope cut actor rival) : Input :=
  match decision with
  | .paid _ => withdrawalInput scope cut actor
  | .reviewBlocked _ | .feeBlocked _ _ | .authorityBlocked _ _ => some .stopReview

variable (seed : Root.Cut Party Good Port (State Party Technology) Instrument) (community : Party → Community)
  (past : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)

def executeReservation (installed : Emergency.Installed (endAt seed past) base scope) :=
  let chosen := withdrawalInput scope (endAt seed past) actor
  let decision := releaseDecision base scope (endAt seed past) actor rival installed
  (decision, Reparation.Actual.publishAfter (run seed community past)
    (queuedPrefix (endAt seed past) chosen rival ++ [dispositionInput base scope (endAt seed past) actor rival decision]))

theorem the_reserved_disposition_uses_the_same_original_whole_write
    (installed : Emergency.Installed (endAt seed past) base scope) :
    let chosen := withdrawalInput scope (endAt seed past) actor
    let waiting := queuedPrefix (endAt seed past) chosen rival
    let executed := executeReservation base scope actor rival seed community past installed
    let selected := dispositionInput base scope (endAt seed past) actor rival executed.1
    Quantities.Recorded seed (past ++ (waiting ++ [selected])) ∧
    executed.2.next = run seed community (past ++ (waiting ++ [selected])) ∧
    (run seed community (past ++ waiting)).stack.balances = (run seed community past).stack.balances :=
  ⟨(executeReservation base scope actor rival seed community past installed).2.recorded,
    Reparation.Actual.publication_consumes_the_retained_visit seed community past _,
    every_native_interleaving_carries_the_identical_reparation_balances seed community past _
      (queuedPrefix_length _ _ _).le⟩

theorem the_dispatched_revision_has_a_paid_release_receipt
    (decision : ReleaseDecision base scope cut actor rival)
    (forwarded : dispositionInput base scope cut actor rival decision = withdrawalInput scope cut actor) :
    ReleaseReceipt base scope cut (atReservedVisit scope cut actor rival) actor := by
  cases decision with
  | paid receipt => exact receipt
  | reviewBlocked _ | feeBlocked _ _ | authorityBlocked _ _ => cases forwarded

theorem admission_depends_only_on_the_original_submission_cut
    (installed : Emergency.Installed cut base scope) :
    dispositionInput base scope cut actor rival (releaseDecision base scope cut actor rival installed) =
      withdrawalInput scope cut actor ↔
      ReviewAvailable cut ∧ (law base scope).Valid cut.raw (withdrawal scope cut actor) := by
  have original := the_first_material_visit_is_reserved_at_the_same_physical_cut cut (withdrawalInput scope cut actor) rival
  let atVisit := atReservedVisit scope cut actor rival
  have sameReview : ReviewAvailable atVisit ↔ ReviewAvailable cut := by
    unfold ReviewAvailable
    rw [original.2.2.1]
  have sameValid :
      (law base scope).Valid atVisit.raw (withdrawal scope cut actor) ↔
        (law base scope).Valid cut.raw (withdrawal scope cut actor) := by rw [original.2.1]
  rw [← sameReview, ← sameValid]
  unfold releaseDecision
  dsimp only
  split
  · rename_i review
    split
    · rename_i valid
      exact ⟨fun _ => ⟨review, valid⟩, fun _ => rfl⟩
    · rename_i denied
      split <;> exact ⟨(fun selected => by cases selected), fun good => (denied good.2).elim⟩
  · rename_i blocked
    exact ⟨(fun selected => by cases selected), fun good => (blocked good.1).elim⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
