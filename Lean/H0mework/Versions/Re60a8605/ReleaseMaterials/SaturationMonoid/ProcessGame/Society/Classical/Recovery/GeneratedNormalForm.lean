import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Exchange.FulfilledTerminalExchange

/-!
# Source-generated strategic normal form

The free program generates M0 participating players, M2 actionable strategy
fibres and profiles, and M3 whole-exchange outcomes.  Finite sequential search
and history readouts live in `GeneratedStrategicGame`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Classical

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Settlement
open Settlement.SourceOwnedSettlementCompiler
open Source Source.FreeStrategicSyntax
open GeneratedTerminalExchange

namespace Source.FreeStrategicSyntax

def IsParticipatingActor (program : FreeStrategicSyntax)
    (actor : program.Actor) : Prop :=
  actor.1.val < program.playerCount

abbrev GeneratedPlayer (program : FreeStrategicSyntax) :=
  { actor : program.Actor // program.IsParticipatingActor actor }

def generatedPlayerOf (program : FreeStrategicSyntax)
    (player : program.Player) : program.GeneratedPlayer :=
  ⟨program.actorOf (program.playerActorIndex player), player.isLt⟩

def generatedPlayerIndex (program : FreeStrategicSyntax)
    (player : program.GeneratedPlayer) : program.Player :=
  ⟨player.1.1.val, player.2⟩

abbrev GeneratedStrategyFor (program : FreeStrategicSyntax)
    (player : program.GeneratedPlayer) :=
  Source.FreeStrategicSyntax.GeneratedStrategy program
    (program.generatedPlayerIndex player)

abbrev GeneratedProfile (program : FreeStrategicSyntax) :=
  (player : program.GeneratedPlayer) → program.GeneratedStrategyFor player

def generatedPlayerEquiv (program : FreeStrategicSyntax) :
    program.GeneratedPlayer ≃ program.Player where
  toFun := program.generatedPlayerIndex
  invFun := program.generatedPlayerOf
  left_inv := by
    intro player
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by intro player; rfl

theorem generatedPlayer_has_exact_participation_relation
    (program : FreeStrategicSyntax) (player : program.GeneratedPlayer) :
    program.relationCompiler.GeneratedInterestAt player.1
      (program.generatedRelation (program.generatedPlayerIndex player)) := by
  have actorEq :
      program.actorOf (program.playerActorIndex
        (program.generatedPlayerIndex player)) = player.1 := by
    apply Subtype.ext
    rfl
  rw [← actorEq]
  exact program.player_generates_interest
    (program.generatedPlayerIndex player)

noncomputable instance generatedPlayerFintype
    (program : FreeStrategicSyntax) : Fintype program.GeneratedPlayer :=
  Fintype.ofEquiv program.Player program.generatedPlayerEquiv.symm

noncomputable instance generatedPlayerDecidableEq
    (program : FreeStrategicSyntax) : DecidableEq program.GeneratedPlayer :=
  Classical.decEq _

noncomputable instance generatedStrategyForFintype
    (program : FreeStrategicSyntax) (player : program.GeneratedPlayer) :
    Fintype (program.GeneratedStrategyFor player) :=
  Fintype.ofEquiv (program.Strategy (program.generatedPlayerIndex player))
    (program.generatedStrategyEquiv
      (program.generatedPlayerIndex player)).symm

noncomputable instance generatedStrategyForDecidableEq
    (program : FreeStrategicSyntax) (player : program.GeneratedPlayer) :
    DecidableEq (program.GeneratedStrategyFor player) :=
  Classical.decEq _

def generatedProfileToCanonical (program : FreeStrategicSyntax)
    (profile : program.GeneratedProfile) : program.CanonicalProfile :=
  fun player =>
    program.generatedStrategyEquiv player
      (profile (program.generatedPlayerOf player))

def generatedProfileOfCanonical (program : FreeStrategicSyntax)
    (profile : program.CanonicalProfile) : program.GeneratedProfile :=
  fun player =>
    program.generatedStrategyOf (program.generatedPlayerIndex player)
      (profile (program.generatedPlayerIndex player))

def generatedProfileEquivCanonical (program : FreeStrategicSyntax) :
    program.GeneratedProfile ≃ program.CanonicalProfile where
  toFun := program.generatedProfileToCanonical
  invFun := program.generatedProfileOfCanonical
  left_inv := by
    intro profile
    funext player
    have playerEq :
        program.generatedPlayerOf (program.generatedPlayerIndex player) =
          player := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    cases playerEq
    exact (program.generatedStrategyEquiv
      (program.generatedPlayerIndex player)).left_inv
      (profile (program.generatedPlayerOf
        (program.generatedPlayerIndex player)))
  right_inv := by
    intro profile
    funext player
    exact (program.generatedStrategyEquiv player).right_inv (profile player)

def generatedTerminalRestriction (program : FreeStrategicSyntax)
    (profile : program.GeneratedProfile)
    (terminal : program.isWorldTerminal
      (program.generatedProfileEquivCanonical profile) = true) :
    program.ExactWorldTerminalRestriction :=
  program.exactWorldTerminalRestriction
    ⟨program.generatedProfileEquivCanonical profile, terminal⟩

def generatedOutcome (program : FreeStrategicSyntax)
    (profile : program.GeneratedProfile) :
    Option (program.GeneratedPlayer → ℚ) :=
  let canonical := program.generatedProfileEquivCanonical profile
  if terminal : program.isWorldTerminal canonical = true then
    some fun player => terminalUtility program
      (program.generatedTerminalRestriction profile terminal)
      (program.generatedPlayerIndex player)
  else
    none

theorem generatedOutcome_eq_none_of_cutoff
    (program : FreeStrategicSyntax) (profile : program.GeneratedProfile)
    (cutoff : program.isWorldTerminal
      (program.generatedProfileEquivCanonical profile) = false) :
    program.generatedOutcome profile = none := by
  simp [generatedOutcome, cutoff]

theorem generatedOutcome_has_exact_cutoff_restriction
    (program : FreeStrategicSyntax) (profile : program.GeneratedProfile)
    (cutoff : program.isWorldTerminal
      (program.generatedProfileEquivCanonical profile) = false) :
    ∃ restriction : program.ExactCutoffRestriction,
      restriction.1.1 = program.generatedProfileEquivCanonical profile ∧
        program.cutoffAtom restriction.1.1 ∈ program.occurrence.trace := by
  let sourceProfile : program.CutoffProfile :=
    ⟨program.generatedProfileEquivCanonical profile, cutoff⟩
  exact ⟨program.exactCutoffRestriction sourceProfile, rfl,
    program.cutoffAtom_mem_trace sourceProfile.1 sourceProfile.2⟩

theorem generatedOutcome_eq_some_of_terminal
    (program : FreeStrategicSyntax) (profile : program.GeneratedProfile)
    (terminal : program.isWorldTerminal
      (program.generatedProfileEquivCanonical profile) = true) :
    program.generatedOutcome profile =
      some (fun player => program.settlementValue
        (program.generatedProfileEquivCanonical profile)
        (program.generatedPlayerIndex player)) := by
  unfold generatedOutcome
  simp only [terminal, dite_true]
  apply congrArg some
  funext player
  exact terminalUtility_eq_settlementValue program
    (program.generatedTerminalRestriction profile terminal)
    (program.generatedPlayerIndex player)

theorem generatedOutcome_is_whole_exchange_settlement_fold
    (program : FreeStrategicSyntax) (profile : program.GeneratedProfile)
    (terminal : program.isWorldTerminal
      (program.generatedProfileEquivCanonical profile) = true) :
    Nonempty (FullyFulfilledExchangeAt
      (terminalSettlementCompiler program)
      (terminalSettlement program
        (program.generatedTerminalRestriction profile terminal))) ∧
      program.generatedOutcome profile =
        some (fun player =>
          (terminalFulfilledPlayerLeg program
            (program.generatedTerminalRestriction profile terminal)
            (program.generatedPlayerIndex player)).obligation.residual) ∧
      ∀ player : program.GeneratedPlayer,
        (terminalFulfilledPlayerLeg program
          (program.generatedTerminalRestriction profile terminal)
          (program.generatedPlayerIndex player)).obligation.bearer = player.1 := by
  refine ⟨⟨terminalFullyFulfilled program
    (program.generatedTerminalRestriction profile terminal)⟩, ?_, ?_⟩
  · rw [program.generatedOutcome_eq_some_of_terminal profile terminal]
    apply congrArg some
    funext player
    exact (terminalUtility_eq_settlementValue program
      (program.generatedTerminalRestriction profile terminal)
      (program.generatedPlayerIndex player)).symm
  · intro player
    rw [terminalUtility_exact_bearer program
      (program.generatedTerminalRestriction profile terminal)
      (program.generatedPlayerIndex player)]
    apply Subtype.ext
    rfl

theorem generatedOutcome_has_exact_world_terminal_restriction
    (program : FreeStrategicSyntax) (profile : program.GeneratedProfile)
    (terminal : program.isWorldTerminal
      (program.generatedProfileEquivCanonical profile) = true) :
    ∃ restriction : program.ExactWorldTerminalRestriction,
      restriction.1.1 = program.generatedProfileEquivCanonical profile ∧
        program.worldTerminalAtom restriction.1.1 ∈
          program.occurrence.trace := by
  let sourceProfile : program.WorldTerminalProfile :=
    ⟨program.generatedProfileEquivCanonical profile, terminal⟩
  exact ⟨program.exactWorldTerminalRestriction sourceProfile, rfl,
    program.worldTerminalAtom_mem_trace sourceProfile.1 sourceProfile.2⟩

end Source.FreeStrategicSyntax
end
end Classical
end Society
end ProcessGame
end SaturationMonoid
