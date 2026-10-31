import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Independent.SourceFirstSingletonGame
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Recovery.RecoveredFiniteStrategicGame

/-!
# Source-first independent singleton preimage

The literal free program and its public code are declared before any target
constant is used.  The target game is then connected by a manually assembled
strong isomorphism; no essential-surjectivity code selector participates.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M4SourceFirstIndependentPreimageRegression

noncomputable section

open Classical.Source Classical.Source.FreeStrategicSyntax
open Classical.Recovery
open Classical.Independent
open Classical.GeneratedTerminalExchange
open _root_.SaturationMonoid.ProcessGame.Society.Settlement
open Settlement.SourceOwnedSettlementCompiler

/-! ## Target-independent source declarations -/

def program : FreeStrategicSyntax where
  playerCount := 1
  strategyCounts := [1]
  terminalFlags := [true]
  settlementValues := [7]
  authorityResiduals := [0]

def code : ValidCode :=
  validCodeOfSyntax program

@[simp] theorem syntaxOf_code : syntaxOf code = program :=
  syntaxOf_validCodeOfSyntax program

def sourcePlayer : program.Player := ⟨0, by decide⟩

def sourceCanonicalProfile : program.CanonicalProfile :=
  fun player => ⟨0, by
    have playerZero : player.val = 0 := Fin.val_eq_zero player
    simp [program, FreeStrategicSyntax.strategyCount, playerZero]⟩

theorem program_strategyCount (player : program.Player) :
    program.strategyCount player = 1 := by
  have playerZero : player.val = 0 := Fin.val_eq_zero player
  simp [FreeStrategicSyntax.strategyCount, program, playerZero]

theorem canonicalProfile_unique (profile : program.CanonicalProfile) :
    profile = sourceCanonicalProfile := by
  funext player
  apply Fin.ext
  have valueLt := (profile player).isLt
  have countEq := program_strategyCount player
  omega

theorem canonicalProfile_card :
    Fintype.card program.CanonicalProfile = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  exact ⟨sourceCanonicalProfile, fun profile =>
    canonicalProfile_unique profile⟩

theorem outcomeIndex_card : Fintype.card program.OutcomeIndex = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨(sourceCanonicalProfile, sourcePlayer), ?_⟩
  rintro ⟨profile, player⟩
  apply Prod.ext
  · exact canonicalProfile_unique profile
  · apply Fin.ext
    exact Fin.val_eq_zero _

theorem sourceCanonicalProfile_terminal :
    program.isWorldTerminal sourceCanonicalProfile = true := by
  unfold FreeStrategicSyntax.isWorldTerminal
  have indexZero : program.profileIndex sourceCanonicalProfile = 0 := by
    unfold FreeStrategicSyntax.profileIndex
    have indexLt := (program.profileEquivFin sourceCanonicalProfile).isLt
    have profileCard := canonicalProfile_card
    omega
  rw [indexZero]
  rfl

theorem sourceSettlementValue_seven
    (profile : program.CanonicalProfile) (player : program.Player) :
    program.settlementValue profile player = 7 := by
  unfold FreeStrategicSyntax.settlementValue
  have indexZero : program.outcomeIndex (profile, player) = 0 := by
    unfold FreeStrategicSyntax.outcomeIndex
    have indexLt := (program.outcomeEquivFin (profile, player)).isLt
    have outcomeCard := outcomeIndex_card
    omega
  rw [indexZero]
  rfl

def sourceGeneratedProfile : program.GeneratedProfile :=
  program.generatedProfileOfCanonical sourceCanonicalProfile

theorem sourceGeneratedProfile_terminal :
    program.isWorldTerminal
      (program.generatedProfileEquivCanonical sourceGeneratedProfile) = true := by
  have canonical :
      program.generatedProfileEquivCanonical
          (program.generatedProfileOfCanonical sourceCanonicalProfile) =
        sourceCanonicalProfile :=
    program.generatedProfileEquivCanonical.right_inv sourceCanonicalProfile
  calc
    program.isWorldTerminal
        (program.generatedProfileEquivCanonical sourceGeneratedProfile) =
      program.isWorldTerminal sourceCanonicalProfile :=
        congrArg program.isWorldTerminal canonical
    _ = true := sourceCanonicalProfile_terminal

/-! ## Manual bridge to the independently declared target -/

open Classical.Independent.SourceFirstSingletonGame

def canonicalStrategyEquiv (player : program.Player) :
    program.Strategy player ≃ game.Strategy player :=
  Equiv.cast (congrArg Fin (program_strategyCount player))

def canonicalProfileEquiv : program.CanonicalProfile ≃ game.Profile :=
  (Equiv.refl program.Player).piCongr canonicalStrategyEquiv

def singletonPlayerEquiv :
    (recoveredOfProgram program).Player ≃ game.Player :=
  program.generatedPlayerEquiv

def singletonStrategyEquiv
    (player : (recoveredOfProgram program).Player) :
    (recoveredOfProgram program).Strategy player ≃
      game.Strategy (singletonPlayerEquiv player) :=
  (program.generatedStrategyEquiv
    (program.generatedPlayerIndex player)).trans
      (canonicalStrategyEquiv (program.generatedPlayerIndex player))

def singletonProfileEquiv :
    (recoveredOfProgram program).Profile ≃ game.Profile :=
  program.generatedProfileEquivCanonical.trans canonicalProfileEquiv

theorem singletonProfile_strategy_commutes
    (profile : (recoveredOfProgram program).Profile)
    (player : (recoveredOfProgram program).Player) :
    singletonProfileEquiv profile (singletonPlayerEquiv player) =
      singletonStrategyEquiv player (profile player) := by
  have playerEq :
      program.generatedPlayerOf (program.generatedPlayerIndex player) =
        player := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  cases playerEq
  change
    canonicalProfileEquiv
        (program.generatedProfileEquivCanonical profile)
        (program.generatedPlayerIndex player) =
      canonicalStrategyEquiv (program.generatedPlayerIndex player)
        (program.generatedStrategyEquiv
          (program.generatedPlayerIndex player) (profile player))
  exact Equiv.piCongr_apply_apply (Equiv.refl program.Player)
    canonicalStrategyEquiv
    (program.generatedProfileEquivCanonical profile)
    (program.generatedPlayerIndex player)

theorem singletonOutcome_preserved
    (profile : (recoveredOfProgram program).Profile) :
    game.outcome (singletonProfileEquiv profile) =
      ((recoveredOfProgram program).outcome profile).map
        (reindexPayoff singletonPlayerEquiv) := by
  have terminal : program.isWorldTerminal
      (program.generatedProfileEquivCanonical profile) = true := by
    have canonicalEq :
        program.generatedProfileEquivCanonical profile =
          sourceCanonicalProfile := by
      funext player
      apply Fin.ext
      have valueLt :=
        (program.generatedProfileEquivCanonical profile player).isLt
      have countEq := program_strategyCount player
      omega
    rw [canonicalEq]
    exact sourceCanonicalProfile_terminal
  change some payoff = (program.generatedOutcome profile).map _
  rw [program.generatedOutcome_eq_some_of_terminal profile terminal]
  change some payoff = some (reindexPayoff singletonPlayerEquiv
    (fun player => program.settlementValue
      (program.generatedProfileEquivCanonical profile)
      (program.generatedPlayerIndex player)))
  apply congrArg some
  funext player
  unfold reindexPayoff payoff
  exact (sourceSettlementValue_seven _ _).symm

def manualProgramIso :
    StrategicGameIso (recoveredOfProgram program) game where
  playerEquiv := singletonPlayerEquiv
  strategyEquiv := singletonStrategyEquiv
  profileEquiv := singletonProfileEquiv
  profile_strategy_commutes := singletonProfile_strategy_commutes
  outcome_preserved := singletonOutcome_preserved

def manualCodeIso : StrategicGameIso (recovered code) game := by
  simpa [recovered, code] using manualProgramIso

/-! ## Whole exchange-settlement consumption -/

def terminalRestriction : program.ExactWorldTerminalRestriction :=
  program.generatedTerminalRestriction sourceGeneratedProfile
    sourceGeneratedProfile_terminal

theorem sourceFirst_whole_exchange_provenance :
    Nonempty (FullyFulfilledExchangeAt
      (terminalSettlementCompiler program)
      (terminalSettlement program terminalRestriction)) ∧
      (recoveredOfProgram program).outcome sourceGeneratedProfile =
        some (fun player =>
          (terminalFulfilledPlayerLeg program terminalRestriction
            (program.generatedPlayerIndex player)).obligation.residual) ∧
      (terminalFulfilledPlayerLeg program terminalRestriction
        sourcePlayer).obligation.residual = (7 : ℚ) ∧
      IsEmpty (OpenSettlementAt (terminalSettlementCompiler program)
        (terminalSettlement program terminalRestriction)) := by
  have whole := recoveredOfProgram_outcome_has_exact_exchange_settlement
    program sourceGeneratedProfile sourceGeneratedProfile_terminal
  refine ⟨whole.1, whole.2.1, ?_,
    terminalSettlement_open_isEmpty program terminalRestriction⟩
  change terminalUtility program terminalRestriction sourcePlayer = 7
  rw [terminalUtility_eq_settlementValue]
  exact sourceSettlementValue_seven _ _

/-- One named sink keeps source-first construction, independent target
isomorphism, and the complete whole-exchange settlement consumer together. -/
structure SourceFirstIndependentPreimageCertificate : Prop where
  syntax_exact : syntaxOf code = program
  independent_iso :
    Nonempty (StrategicGameIso (recovered code) game)
  whole_exchange :
    Nonempty (FullyFulfilledExchangeAt
      (terminalSettlementCompiler program)
      (terminalSettlement program terminalRestriction)) ∧
      (recoveredOfProgram program).outcome sourceGeneratedProfile =
        some (fun player =>
          (terminalFulfilledPlayerLeg program terminalRestriction
            (program.generatedPlayerIndex player)).obligation.residual) ∧
      (terminalFulfilledPlayerLeg program terminalRestriction
        sourcePlayer).obligation.residual = (7 : ℚ) ∧
      IsEmpty (OpenSettlementAt (terminalSettlementCompiler program)
        (terminalSettlement program terminalRestriction))

theorem sourceFirstIndependentPreimageDirectConsumer :
    SourceFirstIndependentPreimageCertificate where
  syntax_exact := syntaxOf_code
  independent_iso := ⟨manualCodeIso⟩
  whole_exchange := sourceFirst_whole_exchange_provenance

end
end M4SourceFirstIndependentPreimageRegression
end Society
end ProcessGame
end SaturationMonoid
