import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Contract.Actual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Contract.Force
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Contract.Delay
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Contract.Adversary
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Timing.Deadline

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)
open PublicFunction.Mandate Counterplay
open Quantities.Execution (endAt inventory)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]
  {CivilView : Type u} {OpponentView : Type v}

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port (State Party Technology) Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port (State Party Technology) Instrument
local notation "Pos" => Position Party Good Port (State Party Technology) Instrument CivilView OpponentView
local notation "Plan" => CivilPlan Party Good Port (State Party Technology) Instrument CivilView
local notation "Opponent" => List OpponentView → Input
local notation "Arbitration" => Nat → C → Turn

variable (game : Game Party Good Port (State Party Technology) Instrument Community CivilView OpponentView)
  {base : RawLaw Party Good Port Technology Instrument}
  (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (actor : Party)

/-- One policy is chosen before the interleaving. Its paid withdrawal is
the source of the very same legal suffix that carries later authority. -/
theorem peace_is_enforceable_and_war_authority_cannot_be_unilaterally_reborn
    (installed : Emergency.Installed game.seed base scope)
    (admitted : ReviewAvailable (submittedCut game) ∧
      (law base scope).Valid (submittedCut game).raw (withdrawal scope (submittedCut game) actor))
    (family : Pos → Prop) (initial : family game.start)
    (closed : game.FibreCloses (signedChoice game scope actor) (constitutionalMove game) family)
    (live : Game.LocalMenusNonempty (constitutionalMove game) family
      (game.compileFibre (signedChoice game scope actor) (constitutionalMove game) family closed)) :
    ∃ policy : Plan,
      ForcesAtEveryOriginalCut game base scope actor policy ∧
      ∀ (opponent : Opponent) (interleave : Arbitration),
        let committed := committedPlan game scope actor policy
        let schedule := protectedTurn game interleave
        ConstitutionalPlay game committed opponent schedule →
        ∀ tick ≥ reservedRank game + 1,
          let release := paidWithdrawalAtPriority game scope actor policy opponent interleave
            (installed.along game.past) admitted
          ∃ suffix : Word, game.prefixAt committed opponent schedule tick = release.releasedPrefix ++ suffix ∧
            Renewal.AdmittedHistory (endAt game.seed release.releasedPrefix) suffix ∧
            HEq (release.continueWith game.community suffix).next (game.ledger committed.submit opponent schedule tick) ∧
            (∀ loss ∈ Reparation.Actual.originalLosses game.seed game.community (release.releasedPrefix ++ suffix),
              ∃ balance, ∃ row, (release.continueWith game.community suffix).next.read row = .inr (loss, balance)) ∧
            (∀ candidate, (game.currentAt committed.submit opponent schedule tick).raw.technology.holder =
              some candidate ↔ Renewal.LiveGrant base scope (inventory (endAt game.seed release.releasedPrefix) suffix)
                candidate) ∧
            ∀ signer, (∀ item ∈ inventory (endAt game.seed release.releasedPrefix) suffix,
              item.request.signer = signer) →
              (game.currentAt committed.submit opponent schedule tick).raw.technology.holder = none := by
  obtain ⟨policy, _, preserves, wins⟩ :=
    the_original_live_fibres_force_the_submitted_withdrawal_and_preserve_independent_exit
      game scope actor (installed.along game.past) admitted family initial closed live
  refine ⟨policy, ⟨wins.1, preserves, fun rival schedule allowed => (wins.2 rival schedule allowed).2⟩, ?_⟩
  intro opponent interleave committed schedule lawful tick reached
  obtain ⟨suffix, path, licensed, whole, grant, unilateral⟩ :=
    the_actual_priority_payment_governs_each_later_constitutional_write
      game scope actor policy opponent interleave installed admitted lawful tick reached
  let release := paidWithdrawalAtPriority game scope actor policy opponent interleave
    (installed.along game.past) admitted
  have kept := release.the_paid_successor_carries_authority_and_every_original_victim_into_its_next_write
    game.community suffix installed licensed.original_authority
  exact ⟨suffix, path, licensed, whole, kept.2.1, grant, unilateral⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
