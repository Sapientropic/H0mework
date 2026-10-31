import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M4.SourceFirstIndependentPreimageRegression

/-!
# Source-first cross-occurrence fixture

Two literal free programs share every classical source field.  The left one
changes only the source-owned authority residual.  Each program generates its
own exact terminal restriction and fulfilled authority consumer before either
normal form is compared with the independent singleton game.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M5SourceFirstCrossOccurrenceFixture

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Classical.Source Classical.Source.FreeStrategicSyntax
open Classical.Recovery
open Classical.Independent
open Classical.Independent.SourceFirstSingletonGame
open Classical.GeneratedTerminalExchange
open M4SourceFirstIndependentPreimageRegression

abbrev rightProgram : FreeStrategicSyntax :=
  M4SourceFirstIndependentPreimageRegression.program

/-- The only source change is the authority residual list. -/
def leftProgram : FreeStrategicSyntax :=
  { rightProgram with authorityResiduals := [1] }

def leftCode : ValidCode := validCodeOfSyntax leftProgram
abbrev rightCode : ValidCode :=
  M4SourceFirstIndependentPreimageRegression.code

theorem classical_source_fields_agree :
    leftProgram.playerCount = rightProgram.playerCount ∧
      leftProgram.strategyCounts = rightProgram.strategyCounts ∧
      leftProgram.terminalFlags = rightProgram.terminalFlags ∧
      leftProgram.settlementValues = rightProgram.settlementValues :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem source_programs_ne : leftProgram ≠ rightProgram := by
  intro equal
  have residuals := congrArg FreeStrategicSyntax.authorityResiduals equal
  change ([1] : List ℚ) = [0] at residuals
  simp at residuals
def leftCanonicalProfile : leftProgram.CanonicalProfile :=
  M4SourceFirstIndependentPreimageRegression.sourceCanonicalProfile

theorem left_strategyCount (player : leftProgram.Player) :
    leftProgram.strategyCount player = 1 := by
  have playerZero : player.val = 0 := Fin.val_eq_zero player
  simp [FreeStrategicSyntax.strategyCount, leftProgram, rightProgram,
    M4SourceFirstIndependentPreimageRegression.program, playerZero]

theorem left_canonicalProfile_unique
    (profile : leftProgram.CanonicalProfile) :
    profile = leftCanonicalProfile := by
  funext player
  apply Fin.ext
  have valueLt := (profile player).isLt
  have countEq := left_strategyCount player
  omega

theorem left_canonicalProfile_card :
    Fintype.card leftProgram.CanonicalProfile = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  exact ⟨leftCanonicalProfile, left_canonicalProfile_unique⟩
def leftSourcePlayer : leftProgram.Player := ⟨0, by decide⟩

theorem left_outcomeIndex_card :
    Fintype.card leftProgram.OutcomeIndex = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨(leftCanonicalProfile, leftSourcePlayer), ?_⟩
  rintro ⟨profile, player⟩
  apply Prod.ext
  · exact left_canonicalProfile_unique profile
  · apply Fin.ext
    exact Fin.val_eq_zero _

theorem leftCanonicalProfile_terminal :
    leftProgram.isWorldTerminal leftCanonicalProfile = true := by
  unfold FreeStrategicSyntax.isWorldTerminal
  have indexZero : leftProgram.profileIndex leftCanonicalProfile = 0 := by
    unfold FreeStrategicSyntax.profileIndex
    have indexLt := (leftProgram.profileEquivFin leftCanonicalProfile).isLt
    have profileCard := left_canonicalProfile_card
    omega
  rw [indexZero]
  rfl

theorem leftSettlementValue_seven
    (profile : leftProgram.CanonicalProfile)
    (player : leftProgram.Player) :
    leftProgram.settlementValue profile player = 7 := by
  unfold FreeStrategicSyntax.settlementValue
  have indexZero : leftProgram.outcomeIndex (profile, player) = 0 := by
    unfold FreeStrategicSyntax.outcomeIndex
    have indexLt := (leftProgram.outcomeEquivFin (profile, player)).isLt
    have outcomeCard := left_outcomeIndex_card
    omega
  rw [indexZero]
  change ([7] : List ℚ)[0]?.getD 0 = 7
  rfl

def leftGeneratedProfile : leftProgram.GeneratedProfile :=
  leftProgram.generatedProfileOfCanonical leftCanonicalProfile
theorem leftGeneratedProfile_terminal :
    leftProgram.isWorldTerminal
      (leftProgram.generatedProfileEquivCanonical leftGeneratedProfile) = true := by
  have canonical :
      leftProgram.generatedProfileEquivCanonical leftGeneratedProfile =
        leftCanonicalProfile :=
    leftProgram.generatedProfileEquivCanonical.right_inv leftCanonicalProfile
  rw [canonical]
  exact leftCanonicalProfile_terminal

def leftTerminal : leftProgram.ExactWorldTerminalRestriction :=
  leftProgram.generatedTerminalRestriction leftGeneratedProfile
    leftGeneratedProfile_terminal
abbrev rightTerminal : rightProgram.ExactWorldTerminalRestriction :=
  M4SourceFirstIndependentPreimageRegression.terminalRestriction

theorem left_authorityIndex_card :
    Fintype.card leftProgram.AuthorityIndex = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨(leftCanonicalProfile, firstTerminalLegBase leftProgram), ?_⟩
  rintro ⟨profile, base⟩
  apply Prod.ext
  · exact left_canonicalProfile_unique profile
  · apply Fin.ext
    exact Fin.val_eq_zero _

theorem left_authorityResidual_one
    (profile : leftProgram.CanonicalProfile)
    (base : leftProgram.AuthorityBase) :
    leftProgram.authorityResidual profile base = 1 := by
  unfold FreeStrategicSyntax.authorityResidual
  have indexZero : leftProgram.authorityIndex (profile, base) = 0 := by
    unfold FreeStrategicSyntax.authorityIndex
    have indexLt := (leftProgram.authorityEquivFin (profile, base)).isLt
    have authorityCard := left_authorityIndex_card
    omega
  rw [indexZero]
  change ([1] : List ℚ)[0]?.getD 0 = 1
  rfl

theorem right_authorityIndex_card :
    Fintype.card rightProgram.AuthorityIndex = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨(sourceCanonicalProfile, firstTerminalLegBase rightProgram), ?_⟩
  rintro ⟨profile, base⟩
  apply Prod.ext
  · exact canonicalProfile_unique profile
  · apply Fin.ext
    exact Fin.val_eq_zero _

theorem right_authorityResidual_zero
    (profile : rightProgram.CanonicalProfile)
    (base : rightProgram.AuthorityBase) :
    rightProgram.authorityResidual profile base = 0 := by
  unfold FreeStrategicSyntax.authorityResidual
  have indexZero : rightProgram.authorityIndex (profile, base) = 0 := by
    unfold FreeStrategicSyntax.authorityIndex
    have indexLt := (rightProgram.authorityEquivFin (profile, base)).isLt
    have authorityCard := right_authorityIndex_card
    omega
  rw [indexZero]
  change ([0] : List ℚ)[0]?.getD 0 = 0
  rfl

theorem right_all_terminal (profile : rightProgram.CanonicalProfile) :
    rightProgram.isWorldTerminal profile = true := by
  rw [canonicalProfile_unique profile]
  exact sourceCanonicalProfile_terminal
def leftAuthorityAtom : FreeClassicalAtom :=
  .authorityResidual 0 0 1

theorem leftAuthorityAtom_exact :
    leftProgram.authorityAtom leftCanonicalProfile
        (firstTerminalLegBase leftProgram) = leftAuthorityAtom := by
  unfold FreeStrategicSyntax.authorityAtom leftAuthorityAtom
  have profileZero : leftProgram.profileIndex leftCanonicalProfile = 0 := by
    unfold FreeStrategicSyntax.profileIndex
    have indexLt := (leftProgram.profileEquivFin leftCanonicalProfile).isLt
    have profileCard := left_canonicalProfile_card
    omega
  rw [profileZero, left_authorityResidual_one]
  rfl

theorem leftAuthorityAtom_mem_trace :
    leftAuthorityAtom ∈ leftProgram.occurrence.trace := by
  rw [← leftAuthorityAtom_exact]
  exact leftProgram.authorityAtom_mem_trace leftCanonicalProfile
    (firstTerminalLegBase leftProgram) leftCanonicalProfile_terminal
theorem leftAuthorityAtom_not_mem_right_trace :
    leftAuthorityAtom ∉ rightProgram.occurrence.trace := by
  rw [rightProgram.occurrence_trace]
  simp [FreeStrategicSyntax.programEvents,
    FreeStrategicSyntax.actorEvents,
    FreeStrategicSyntax.participationEvents,
    FreeStrategicSyntax.actionEvents,
    FreeStrategicSyntax.outcomeEvents,
    FreeStrategicSyntax.authorityEvents,
    FreeStrategicSyntax.authorityAtom,
    leftAuthorityAtom, right_all_terminal,
    right_authorityResidual_zero]

theorem source_occurrences_ne :
    leftProgram.occurrence ≠ rightProgram.occurrence := by
  intro equal
  have traces := congrArg RootedAccountedUnfolding.trace equal
  have member : leftAuthorityAtom ∈ rightProgram.occurrence.trace := by
    rw [← traces]
    exact leftAuthorityAtom_mem_trace
  exact leftAuthorityAtom_not_mem_right_trace member

theorem left_terminalAuthorityK :
    terminalAuthorityK leftProgram leftTerminal = 1 := by
  rw [terminalAuthorityK_eq_sourceResidual]
  exact left_authorityResidual_one _ _

theorem right_terminalAuthorityK :
    terminalAuthorityK rightProgram rightTerminal = 0 := by
  rw [terminalAuthorityK_eq_sourceResidual]
  exact right_authorityResidual_zero _ _
theorem leftAuthorityConsumer :
    TerminalAuthorityConsumerAt leftProgram leftTerminal :=
  terminalAuthorityK_has_exact_consumer leftProgram leftTerminal

theorem rightAuthorityConsumer :
    TerminalAuthorityConsumerAt rightProgram rightTerminal :=
  terminalAuthorityK_has_exact_consumer rightProgram rightTerminal
/-! ## Manual normalization of the left generated game -/

def leftCanonicalStrategyEquiv (player : leftProgram.Player) :
    leftProgram.Strategy player ≃ game.Strategy player :=
  Equiv.cast (congrArg Fin (left_strategyCount player))
def leftCanonicalProfileEquiv : leftProgram.CanonicalProfile ≃ game.Profile :=
  (Equiv.refl leftProgram.Player).piCongr leftCanonicalStrategyEquiv

def leftPlayerEquiv :
    (recoveredOfProgram leftProgram).Player ≃ game.Player :=
  leftProgram.generatedPlayerEquiv
def leftStrategyEquiv
    (player : (recoveredOfProgram leftProgram).Player) :
    (recoveredOfProgram leftProgram).Strategy player ≃
      game.Strategy (leftPlayerEquiv player) :=
  (leftProgram.generatedStrategyEquiv
    (leftProgram.generatedPlayerIndex player)).trans
      (leftCanonicalStrategyEquiv
        (leftProgram.generatedPlayerIndex player))

def leftProfileEquiv :
    (recoveredOfProgram leftProgram).Profile ≃ game.Profile :=
  leftProgram.generatedProfileEquivCanonical.trans leftCanonicalProfileEquiv

theorem leftProfile_strategy_commutes
    (profile : (recoveredOfProgram leftProgram).Profile)
    (player : (recoveredOfProgram leftProgram).Player) :
    leftProfileEquiv profile (leftPlayerEquiv player) =
      leftStrategyEquiv player (profile player) := by
  have playerEq :
      leftProgram.generatedPlayerOf
          (leftProgram.generatedPlayerIndex player) = player := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  cases playerEq
  change
    leftCanonicalProfileEquiv
        (leftProgram.generatedProfileEquivCanonical profile)
        (leftProgram.generatedPlayerIndex player) =
      leftCanonicalStrategyEquiv
        (leftProgram.generatedPlayerIndex player)
        (leftProgram.generatedStrategyEquiv
          (leftProgram.generatedPlayerIndex player) (profile player))
  exact Equiv.piCongr_apply_apply (Equiv.refl leftProgram.Player)
    leftCanonicalStrategyEquiv
    (leftProgram.generatedProfileEquivCanonical profile)
    (leftProgram.generatedPlayerIndex player)

theorem leftOutcome_preserved
    (profile : (recoveredOfProgram leftProgram).Profile) :
    game.outcome (leftProfileEquiv profile) =
      ((recoveredOfProgram leftProgram).outcome profile).map
        (reindexPayoff leftPlayerEquiv) := by
  have terminal : leftProgram.isWorldTerminal
      (leftProgram.generatedProfileEquivCanonical profile) = true := by
    rw [left_canonicalProfile_unique
      (leftProgram.generatedProfileEquivCanonical profile)]
    exact leftCanonicalProfile_terminal
  change some payoff = (leftProgram.generatedOutcome profile).map _
  rw [leftProgram.generatedOutcome_eq_some_of_terminal profile terminal]
  change some payoff = some (reindexPayoff leftPlayerEquiv
    (fun player => leftProgram.settlementValue
      (leftProgram.generatedProfileEquivCanonical profile)
      (leftProgram.generatedPlayerIndex player)))
  apply congrArg some
  funext player
  unfold reindexPayoff payoff
  exact (leftSettlementValue_seven _ _).symm

def leftManualProgramIso :
    StrategicGameIso (recoveredOfProgram leftProgram) game where
  playerEquiv := leftPlayerEquiv
  strategyEquiv := leftStrategyEquiv
  profileEquiv := leftProfileEquiv
  profile_strategy_commutes := leftProfile_strategy_commutes
  outcome_preserved := leftOutcome_preserved

def leftManualCodeIso : StrategicGameIso (recovered leftCode) game := by
  simpa [recovered, leftCode] using leftManualProgramIso

def leftRightProgramIso :
    StrategicGameIso (recoveredOfProgram leftProgram)
      (recoveredOfProgram rightProgram) :=
  leftManualProgramIso.trans manualProgramIso.symm

/-- Honest composition through the independently declared singleton image. -/
def leftRightCodeIso :
    StrategicGameIso (recovered leftCode) (recovered rightCode) :=
  leftManualCodeIso.trans manualCodeIso.symm

end
end M5SourceFirstCrossOccurrenceFixture
end Society
end ProcessGame
end SaturationMonoid
