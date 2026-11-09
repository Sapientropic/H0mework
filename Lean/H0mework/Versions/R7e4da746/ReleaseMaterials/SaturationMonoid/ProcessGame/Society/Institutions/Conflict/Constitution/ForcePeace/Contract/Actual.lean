import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Contract.Policy
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Contract.Renewal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)
open PublicFunction.Mandate Counterplay
open Quantities.Execution (endAt endAt_append inventory)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]
  {CivilView : Type u} {OpponentView : Type v}

variable (game : Game Party Good Port (State Party Technology) Instrument Community CivilView OpponentView)
  {base : RawLaw Party Good Port Technology Instrument}
  (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (actor : Party)
  (follow : CivilPlan Party Good Port (State Party Technology) Instrument CivilView)
  (opponent : List OpponentView → Reparation.Actual.Input Party Good Port (State Party Technology) Instrument)
  (interleave : Nat → Root.Cut Party Good Port (State Party Technology) Instrument → Turn)

local notation "policy" => committedPlan game scope actor follow
local notation "schedule" => protectedTurn game interleave
local notation "finish" => reservedRank game + 1
local notation "Word" => Reparation.Actual.Script Party Good Port (State Party Technology) Instrument

/-- The release paid on this actual game path supplies the original
successor for every later legal prefix of that same game. -/
theorem the_actual_priority_payment_governs_each_later_constitutional_write
    (installed : Emergency.Installed game.seed base scope)
    (admitted : ReviewAvailable (submittedCut game) ∧
      (law base scope).Valid (submittedCut game).raw (withdrawal scope (submittedCut game) actor))
    (allowed : ConstitutionalPlay game policy opponent schedule) (tick : Nat) (later : finish ≤ tick) :
    let release := paidWithdrawalAtPriority game scope actor follow opponent interleave (installed.along game.past) admitted
    let original := endAt game.seed release.releasedPrefix
    ∃ suffix : Word, game.prefixAt policy opponent schedule tick = release.releasedPrefix ++ suffix ∧
      Renewal.AdmittedHistory original suffix ∧
      HEq (release.continueWith game.community suffix).next
        (game.ledger (policy).submit opponent schedule tick) ∧
      (∀ candidate, (game.currentAt (policy).submit opponent schedule tick).raw.technology.holder = some candidate ↔
        Renewal.LiveGrant base scope (inventory original suffix) candidate) ∧
      (∀ signer, (∀ item ∈ inventory original suffix, item.request.signer = signer) →
        (game.currentAt (policy).submit opponent schedule tick).raw.technology.holder = none) := by
  let release := paidWithdrawalAtPriority game scope actor follow opponent interleave (installed.along game.past) admitted
  let original := endAt game.seed release.releasedPrefix
  have paidAt : game.prefixAt policy opponent schedule finish = release.releasedPrefix := release.original
  obtain ⟨suffix, extended⟩ := game.earlier_is_a_prefix policy opponent schedule later
  have split := extended.trans (congrArg (· ++ suffix) paidAt)
  have suffixExact :
      game.scriptAt (policy).submit opponent schedule tick =
        game.scriptAt (policy).submit opponent schedule finish ++ suffix :=
    List.append_cancel_left (extended.trans (List.append_assoc _ _ _))
  have legal := constitutional_play_has_original_admission_at_every_prefix game policy opponent schedule allowed tick
  rw [suffixExact] at legal
  have suffixLegal := (Renewal.AdmittedHistory.restrict legal).2
  change Renewal.AdmittedHistory (endAt (submittedCut game) (game.scriptAt (policy).submit opponent schedule finish)) suffix
    at suffixLegal
  rw [← endAt_append, ← show game.prefixAt policy opponent schedule finish =
    game.past ++ game.scriptAt (policy).submit opponent schedule finish from rfl, paidAt] at suffixLegal
  have audit := release.the_paid_successor_carries_authority_and_every_original_victim_into_its_next_write
    game.community suffix installed suffixLegal.original_authority
  refine ⟨suffix, split, suffixLegal, ?_, ?_, ?_⟩
  · change HEq (release.continueWith game.community suffix).next
      (Reparation.Actual.run game.seed game.community (game.prefixAt policy opponent schedule tick))
    rw [split, EffectiveRelease.continueWith, release.the_paid_withdrawal_writes_its_literal_original_successor]
    exact heq_of_eq (Reparation.Actual.publication_consumes_the_retained_visit _ _ _ _)
  · rw [game.play_is_the_original_current]
    change ∀ candidate, (endAt game.seed (game.prefixAt policy opponent schedule tick)).raw.technology.holder =
      some candidate ↔ Renewal.LiveGrant base scope (inventory original suffix) candidate
    rw [split]
    exact audit.2.2
  · intro signer alone
    rw [game.play_is_the_original_current]
    change (endAt game.seed (game.prefixAt policy opponent schedule tick)).raw.technology.holder = none
    rw [split, endAt_append]
    exact Renewal.one_signer_cannot_restore_after_any_admitted_history original suffix
      (installed.along release.releasedPrefix) release.the_literal_paid_successor_has_no_holder_or_offer
      suffixLegal signer alone

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
