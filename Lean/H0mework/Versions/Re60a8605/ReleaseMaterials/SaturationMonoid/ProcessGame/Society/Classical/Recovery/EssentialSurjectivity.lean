import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Recovery.RecoveredFiniteStrategicGame

/-!
# Representation completeness of source-generated finite strategic games

Every independently presented finite rational strategic game is isomorphic
to the normal-form readout of one valid natural-number code in the fixed
target-independent source language.  This declaration is the object-level essential-surjectivity
transporter: its proof uses the target to locate a preimage in the already
fixed free syntax.  It is not the source producer and is never used to certify
the provenance of that chosen code.  The no-target-input producer is
`recovered_source_native`; independently named source-first preimages are
checked by direct regressions.  Neither public recovery nor the syntax stores
a target type, equivalence, normalizer, or every-profile certificate.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Classical
namespace Recovery

noncomputable section

open Independent Source
open Source.FreeStrategicSyntax

namespace EssentialSurjectivity

universe u v

/-- Canonical finite player skeleton used only inside the completeness
proof. -/
private def targetPlayerEquiv (target : FiniteStrategicGame.{u, v}) :
    target.Player ≃ Fin (Fintype.card target.Player) :=
  Fintype.equivFin _

/-- Exact cardinality of every finite target strategy fibre, including zero. -/
private def strategyCountsOf (target : FiniteStrategicGame.{u, v}) : List Nat :=
  List.ofFn fun player : Fin (Fintype.card target.Player) =>
    Fintype.card (target.Strategy ((targetPlayerEquiv target).symm player))

/-- Cardinal skeleton of a target.  Outcome bits and settlement values are
filled by the final syntax below and do not affect its player or strategy
types. -/
private def skeletonOf (target : FiniteStrategicGame.{u, v}) : FreeStrategicSyntax where
  playerCount := Fintype.card target.Player
  strategyCounts := strategyCountsOf target
  terminalFlags := []
  settlementValues := []
  authorityResiduals := []

private theorem skeleton_strategyCount
    (target : FiniteStrategicGame.{u, v})
    (player : (skeletonOf target).Player) :
    (skeletonOf target).strategyCount player =
      Fintype.card
        (target.Strategy ((targetPlayerEquiv target).symm player)) := by
  let targetPlayer := (targetPlayerEquiv target).symm player
  change
    (strategyCountsOf target)[player.val]?.getD 0 =
      Fintype.card (target.Strategy targetPlayer)
  have lookup :
      (strategyCountsOf target)[player.val]? =
        some (Fintype.card (target.Strategy targetPlayer)) := by
    simp only [strategyCountsOf, List.getElem?_ofFn]
    split
    · rename_i inRange
      have canonicalEq :
          (⟨player.val, inRange⟩ : Fin (Fintype.card target.Player)) =
            player :=
        Fin.ext rfl
      rw [canonicalEq]
    · rename_i outOfRange
      exact False.elim (outOfRange player.isLt)
  rw [lookup]
  rfl

/-- A canonical source strategy code is exactly one strategy of the target
player represented by that code's player index. -/
private def skeletonStrategyEquiv
    (target : FiniteStrategicGame.{u, v})
    (player : (skeletonOf target).Player) :
    (skeletonOf target).Strategy player ≃
      target.Strategy ((targetPlayerEquiv target).symm player) :=
  (Equiv.cast (congrArg Fin (skeleton_strategyCount target player))).trans
    (Fintype.equivFin _).symm

/-- Whole dependent profile transport from the canonical source skeleton to
the independently presented target. -/
private def skeletonProfileEquiv
    (target : FiniteStrategicGame.{u, v}) :
    (skeletonOf target).CanonicalProfile ≃ target.Profile :=
  (targetPlayerEquiv target).symm.piCongr
    (skeletonStrategyEquiv target)

/-- Terminal/cutoff bits indexed by the fixed canonical profile enumeration. -/
private def terminalFlagsOf (target : FiniteStrategicGame.{u, v}) : List Bool :=
  List.ofFn fun index :
      Fin (Fintype.card (skeletonOf target).CanonicalProfile) =>
    (target.outcome
      (skeletonProfileEquiv target
        ((skeletonOf target).profileEquivFin.symm index))).isSome

/-- Settlement atoms indexed by the fixed canonical `(profile, player)`
enumeration.  This is an event-value stream, not a callable payoff table in
the source language. -/
private def settlementValuesOf (target : FiniteStrategicGame.{u, v}) : List ℚ :=
  List.ofFn fun index :
      Fin (Fintype.card (skeletonOf target).OutcomeIndex) =>
    let outcome := (skeletonOf target).outcomeEquivFin.symm index
    match target.outcome (skeletonProfileEquiv target outcome.1) with
    | none => 0
    | some payoffs =>
        payoffs ((targetPlayerEquiv target).symm outcome.2)

/-- First-order free syntax selected by the completeness proof.  The record
contains only cardinal data, terminal bits, and terminal settlement events. -/
private def syntaxFor (target : FiniteStrategicGame.{u, v}) : FreeStrategicSyntax where
  playerCount := Fintype.card target.Player
  strategyCounts := strategyCountsOf target
  terminalFlags := terminalFlagsOf target
  settlementValues := settlementValuesOf target
  authorityResiduals := []

private theorem listOfFn_getElem_getD
    {Alpha : Type u} {size : Nat}
    (values : Fin size → Alpha) (index : Fin size) (fallback : Alpha) :
    (List.ofFn values)[index.val]?.getD fallback = values index := by
  have lookup :
      (List.ofFn values)[index.val]? = some (values index) := by
    simp only [List.getElem?_ofFn]
    split
    · rename_i inRange
      have canonicalEq : (⟨index.val, inRange⟩ : Fin size) = index :=
        Fin.ext rfl
      rw [canonicalEq]
    · rename_i outOfRange
      exact False.elim (outOfRange index.isLt)
  rw [lookup]
  rfl

private theorem syntaxFor_strategyCount
    (target : FiniteStrategicGame.{u, v})
    (player : (syntaxFor target).Player) :
    (syntaxFor target).strategyCount player =
      Fintype.card
        (target.Strategy ((targetPlayerEquiv target).symm player)) :=
  skeleton_strategyCount target player

/-- Fibre equivalence for the final syntax.  Outcome fields do not enter its
construction. -/
private def syntaxStrategyEquiv
    (target : FiniteStrategicGame.{u, v})
    (player : (syntaxFor target).Player) :
    (syntaxFor target).Strategy player ≃
      target.Strategy ((targetPlayerEquiv target).symm player) :=
  (Equiv.cast (congrArg Fin (syntaxFor_strategyCount target player))).trans
    (Fintype.equivFin _).symm

/-- Dependent profile equivalence of the final syntax and the target. -/
private def syntaxProfileEquiv
    (target : FiniteStrategicGame.{u, v}) :
    (syntaxFor target).CanonicalProfile ≃ target.Profile :=
  (targetPlayerEquiv target).symm.piCongr
    (syntaxStrategyEquiv target)

private theorem syntaxProfileEquiv_eq_skeletonProfileEquiv
    (target : FiniteStrategicGame.{u, v}) :
    syntaxProfileEquiv target = skeletonProfileEquiv target := by
  rfl

/-- Exact terminal/cutoff decoding at every canonical profile. -/
private theorem syntaxFor_isWorldTerminal
    (target : FiniteStrategicGame.{u, v})
    (profile : (syntaxFor target).CanonicalProfile) :
    (syntaxFor target).isWorldTerminal profile =
      (target.outcome (syntaxProfileEquiv target profile)).isSome := by
  let skeletonProfile : (skeletonOf target).CanonicalProfile := profile
  have profileTransport :
      syntaxProfileEquiv target profile =
        skeletonProfileEquiv target skeletonProfile := by
    rfl
  change
    (terminalFlagsOf target)[
        ((syntaxFor target).profileEquivFin profile).val]?.getD true = _
  unfold terminalFlagsOf
  change
    (List.ofFn fun index :
        Fin (Fintype.card (skeletonOf target).CanonicalProfile) =>
      (target.outcome
        (skeletonProfileEquiv target
          ((skeletonOf target).profileEquivFin.symm index))).isSome)[
        ((skeletonOf target).profileEquivFin skeletonProfile).val]?.getD true = _
  rw [listOfFn_getElem_getD]
  have decoded :=
    (skeletonOf target).profileEquivFin.symm_apply_apply skeletonProfile
  rw [decoded, profileTransport]

/-- Exact terminal settlement value at every canonical profile/player
coordinate. -/
private theorem syntaxFor_settlementValue
    (target : FiniteStrategicGame.{u, v})
    (profile : (syntaxFor target).CanonicalProfile)
    (player : (syntaxFor target).Player) :
    (syntaxFor target).settlementValue profile player =
      match target.outcome (syntaxProfileEquiv target profile) with
      | none => 0
      | some payoffs =>
          payoffs ((targetPlayerEquiv target).symm player) := by
  let skeletonProfile : (skeletonOf target).CanonicalProfile := profile
  let skeletonPlayer : (skeletonOf target).Player := player
  have profileTransport :
      syntaxProfileEquiv target profile =
        skeletonProfileEquiv target skeletonProfile := by
    rfl
  have playerTransport :
      (targetPlayerEquiv target).symm player =
        (targetPlayerEquiv target).symm skeletonPlayer := by
    rfl
  change
    (settlementValuesOf target)[
        ((syntaxFor target).outcomeEquivFin (profile, player)).val]?.getD 0 = _
  unfold settlementValuesOf
  change
    (List.ofFn fun index :
        Fin (Fintype.card (skeletonOf target).OutcomeIndex) =>
      let outcome := (skeletonOf target).outcomeEquivFin.symm index
      match target.outcome (skeletonProfileEquiv target outcome.1) with
      | none => 0
      | some payoffs =>
          payoffs ((targetPlayerEquiv target).symm outcome.2))[
        ((skeletonOf target).outcomeEquivFin
          (skeletonProfile, skeletonPlayer)).val]?.getD 0 = _
  rw [listOfFn_getElem_getD]
  have decoded :=
    (skeletonOf target).outcomeEquivFin.symm_apply_apply
      (skeletonProfile, skeletonPlayer)
  rw [decoded, profileTransport, playerTransport]

/-- The public source code selected internally by completeness. -/
private def codeFor (target : FiniteStrategicGame.{u, v}) : ValidCode :=
  validCodeOfSyntax (syntaxFor target)

@[simp] private theorem syntaxOf_codeFor
    (target : FiniteStrategicGame.{u, v}) :
    syntaxOf (codeFor target) = syntaxFor target :=
  syntaxOf_validCodeOfSyntax _

/-- Player transport from M0 generated actors to the independently presented
target carrier. -/
private def recoveredPlayerEquiv
    (target : FiniteStrategicGame.{u, v}) :
    (recoveredOfProgram (syntaxFor target)).Player ≃ target.Player :=
  (syntaxFor target).generatedPlayerEquiv.trans
    (targetPlayerEquiv target).symm

/-- Fibrewise strategy transport from M2 actionable continuation codes. -/
private def recoveredStrategyEquiv
    (target : FiniteStrategicGame.{u, v})
    (player : (recoveredOfProgram (syntaxFor target)).Player) :
  (recoveredOfProgram (syntaxFor target)).Strategy player ≃
      target.Strategy (recoveredPlayerEquiv target player) :=
  ((syntaxFor target).generatedStrategyEquiv
      ((syntaxFor target).generatedPlayerIndex player)).trans
    (syntaxStrategyEquiv target
      ((syntaxFor target).generatedPlayerIndex player))

/-- Whole-profile transport is generated-profile normalization followed by
the fixed finite skeleton transport. -/
private def recoveredProfileEquiv
    (target : FiniteStrategicGame.{u, v}) :
    (recoveredOfProgram (syntaxFor target)).Profile ≃ target.Profile :=
  (syntaxFor target).generatedProfileEquivCanonical.trans
    (syntaxProfileEquiv target)

private theorem recoveredProfile_strategy_commutes
    (target : FiniteStrategicGame.{u, v})
    (profile : (recoveredOfProgram (syntaxFor target)).Profile)
    (player : (recoveredOfProgram (syntaxFor target)).Player) :
    recoveredProfileEquiv target profile
        (recoveredPlayerEquiv target player) =
      recoveredStrategyEquiv target player (profile player) := by
  have playerEq :
      (syntaxFor target).generatedPlayerOf
          ((syntaxFor target).generatedPlayerIndex player) = player := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  cases playerEq
  change
    syntaxProfileEquiv target
        ((syntaxFor target).generatedProfileEquivCanonical profile)
        ((targetPlayerEquiv target).symm
          ((syntaxFor target).generatedPlayerIndex player)) =
      syntaxStrategyEquiv target
          ((syntaxFor target).generatedPlayerIndex player)
        ((syntaxFor target).generatedStrategyEquiv
            ((syntaxFor target).generatedPlayerIndex player)
          (profile player))
  exact Equiv.piCongr_apply_apply
    ((targetPlayerEquiv target).symm)
    (syntaxStrategyEquiv target)
    ((syntaxFor target).generatedProfileEquivCanonical profile)
    ((syntaxFor target).generatedPlayerIndex player)

/-- The complete optional outcome commutes.  Terminal coordinates are read
from exact M3 settlements; cutoff remains `none`. -/
private theorem recoveredOutcome_preserved
    (target : FiniteStrategicGame.{u, v})
    (profile : (recoveredOfProgram (syntaxFor target)).Profile) :
    target.outcome (recoveredProfileEquiv target profile) =
      ((recoveredOfProgram (syntaxFor target)).outcome profile).map
        (reindexPayoff (recoveredPlayerEquiv target)) := by
  let program := syntaxFor target
  let canonical := program.generatedProfileEquivCanonical profile
  have profileEq :
      recoveredProfileEquiv target profile =
        syntaxProfileEquiv target canonical := by
    rfl
  rw [profileEq]
  cases result : target.outcome (syntaxProfileEquiv target canonical) with
  | none =>
      have cutoff : program.isWorldTerminal canonical = false := by
        rw [syntaxFor_isWorldTerminal target canonical, result]
        rfl
      change none = (program.generatedOutcome profile).map _
      rw [program.generatedOutcome_eq_none_of_cutoff profile cutoff]
      rfl
  | some payoffs =>
      have terminal : program.isWorldTerminal canonical = true := by
        rw [syntaxFor_isWorldTerminal target canonical, result]
        rfl
      change
        some payoffs = (program.generatedOutcome profile).map
          (reindexPayoff (recoveredPlayerEquiv target))
      rw [program.generatedOutcome_eq_some_of_terminal profile terminal]
      change
        some payoffs = some (reindexPayoff (recoveredPlayerEquiv target)
          (fun player => program.settlementValue
            (program.generatedProfileEquivCanonical profile)
            (program.generatedPlayerIndex player)))
      apply congrArg some
      funext targetPlayer
      unfold reindexPayoff
      change
        payoffs targetPlayer =
          program.settlementValue canonical
            (program.generatedPlayerIndex
              ((recoveredPlayerEquiv target).symm targetPlayer))
      rw [syntaxFor_settlementValue target canonical]
      rw [result]
      have inversePlayer :=
        (recoveredPlayerEquiv target).apply_symm_apply targetPlayer
      exact congrArg payoffs inversePlayer.symm

/-- Strong recovered-game isomorphism.  Every coordinate is constructed
above; no equivalence or outcome agreement is an input to recovery. -/
private def recoveredOfProgramIso
    (target : FiniteStrategicGame.{u, v}) :
    StrategicGameIso (recoveredOfProgram (syntaxFor target)) target where
  playerEquiv := recoveredPlayerEquiv target
  strategyEquiv := recoveredStrategyEquiv target
  profileEquiv := recoveredProfileEquiv target
  profile_strategy_commutes :=
    recoveredProfile_strategy_commutes target
  outcome_preserved := recoveredOutcome_preserved target

/-- The same isomorphism at the public natural-number code mouth. -/
private def recoveredCodeIso
    (target : FiniteStrategicGame.{u, v}) :
    StrategicGameIso (recovered (codeFor target)) target := by
  simpa [recovered, codeFor] using recoveredOfProgramIso target

/-- Representation-level essential surjectivity over the entire independent carrier:
empty player sets, empty or inhabited heterogeneous finite strategy fibres,
world-terminal outcomes, and cutoff outcomes are all included. -/
theorem recovery_representation_essentially_surjective :
    ∀ target : FiniteStrategicGame.{u, v},
      ∃ code : ValidCode,
        Nonempty (StrategicGameIso (recovered code) target) := by
  intro target
  exact ⟨codeFor target, ⟨recoveredCodeIso target⟩⟩

/-- Compatibility name.  Like the canonical theorem above, this is a
representation-completeness transporter, never a source-provenance producer. -/
theorem recovery_essentially_surjective :
    ∀ target : FiniteStrategicGame.{u, v},
      ∃ code : ValidCode,
        Nonempty (StrategicGameIso (recovered code) target) :=
  recovery_representation_essentially_surjective

end EssentialSurjectivity

end
end Recovery
end Classical
end Society
end ProcessGame
end SaturationMonoid
