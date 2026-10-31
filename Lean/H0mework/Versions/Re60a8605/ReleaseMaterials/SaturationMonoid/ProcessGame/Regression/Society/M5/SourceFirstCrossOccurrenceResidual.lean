import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M5.SourceFirstCrossOccurrenceFixture

/-!
# M5 source-first cross-occurrence strict residual

The two programs are declared without a target-derived code selector.  Their
generated classical games normalize to one fixed independent image, while an
exact source authority atom passes through the fulfilled exchange consumer
with residuals `1` and `0`.  Consequently neither the occurrence nor its `K`
can be reconstructed from that common classical image.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M5SourceFirstCrossOccurrenceResidual

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Classical.Source Classical.Source.FreeStrategicSyntax
open Classical.Recovery
open Classical.Independent
open Classical.Independent.SourceFirstSingletonGame
open Classical.GeneratedTerminalExchange
open M5SourceFirstCrossOccurrenceFixture

inductive PathIndex where
  | left
  | right
  deriving DecidableEq

def leftPath : PathIndex := .left

def rightPath : PathIndex := .right

theorem leftPath_ne_rightPath : leftPath ≠ rightPath := by
  decide

/-- The fixed normalized classical image; it is declared independently in M4. -/
def normalizedClassicalImage : FiniteStrategicGame := game

/-- Classical forgetting first normalizes either source-generated game to the
same independently presented finite strategic game. -/
def Forget (_path : PathIndex) : FiniteStrategicGame :=
  normalizedClassicalImage

def leftNormalization :
    StrategicGameIso (recovered leftCode) (Forget leftPath) :=
  leftManualCodeIso

def rightNormalization :
    StrategicGameIso (recovered rightCode) (Forget rightPath) :=
  M4SourceFirstIndependentPreimageRegression.manualCodeIso

def leftAnchoredProfile : (recovered leftCode).Profile :=
  leftNormalization.profileEquiv.symm uniqueProfile

def rightAnchoredProfile : (recovered rightCode).Profile :=
  rightNormalization.profileEquiv.symm uniqueProfile

theorem terminal_profile_commutes :
    leftRightCodeIso.profileEquiv leftAnchoredProfile =
      rightAnchoredProfile := by
  unfold leftRightCodeIso leftAnchoredProfile rightAnchoredProfile
  change
    (StrategicGameIso.symm
      M4SourceFirstIndependentPreimageRegression.manualCodeIso).profileEquiv
        (leftManualCodeIso.profileEquiv
          (leftManualCodeIso.profileEquiv.symm uniqueProfile)) =
      (M4SourceFirstIndependentPreimageRegression.manualCodeIso.profileEquiv).symm
        uniqueProfile
  rw [leftManualCodeIso.profileEquiv.apply_symm_apply]
  rfl

def leftProgramTerminalProfile :
    (recoveredOfProgram leftProgram).Profile := by
  change leftProgram.GeneratedProfile
  exact leftGeneratedProfile

def rightProgramTerminalProfile :
    (recoveredOfProgram rightProgram).Profile := by
  change rightProgram.GeneratedProfile
  exact M4SourceFirstIndependentPreimageRegression.sourceGeneratedProfile

theorem rightProgramProfile_unique
    (first second : (recoveredOfProgram rightProgram).Profile) :
    first = second := by
  funext player
  apply (rightProgram.generatedStrategyEquiv
    (rightProgram.generatedPlayerIndex player)).injective
  apply Fin.ext
  have countEq :=
    M4SourceFirstIndependentPreimageRegression.program_strategyCount
      (rightProgram.generatedPlayerIndex player)
  have firstZero :
      (rightProgram.generatedStrategyEquiv
        (rightProgram.generatedPlayerIndex player) (first player)).val = 0 := by
    have valueLt := (rightProgram.generatedStrategyEquiv
      (rightProgram.generatedPlayerIndex player) (first player)).isLt
    have valueLtOne :
        (rightProgram.generatedStrategyEquiv
          (rightProgram.generatedPlayerIndex player) (first player)).val < 1 :=
      valueLt.trans_le (Nat.le_of_eq countEq)
    omega
  have secondZero :
      (rightProgram.generatedStrategyEquiv
        (rightProgram.generatedPlayerIndex player) (second player)).val = 0 := by
    have valueLt := (rightProgram.generatedStrategyEquiv
      (rightProgram.generatedPlayerIndex player) (second player)).isLt
    have valueLtOne :
        (rightProgram.generatedStrategyEquiv
          (rightProgram.generatedPlayerIndex player) (second player)).val < 1 :=
      valueLt.trans_le (Nat.le_of_eq countEq)
    omega
  exact firstZero.trans secondZero.symm

theorem exact_terminal_generated_profile_commutes :
    leftRightProgramIso.profileEquiv leftProgramTerminalProfile =
      rightProgramTerminalProfile :=
  rightProgramProfile_unique _ _

theorem equal_normalized_classical_image :
    Forget leftPath = Forget rightPath := rfl

theorem terminalAuthorityK_ne :
    terminalAuthorityK leftProgram leftTerminal ≠
      terminalAuthorityK rightProgram rightTerminal := by
  rw [left_terminalAuthorityK, right_terminalAuthorityK]
  decide

theorem Forget_not_injective : ¬ Function.Injective Forget := by
  intro injective
  exact leftPath_ne_rightPath
    (injective equal_normalized_classical_image)

theorem Forget_has_no_left_inverse :
    ¬ ∃ reconstruct : FiniteStrategicGame → PathIndex,
      Function.LeftInverse reconstruct Forget := by
  rintro ⟨reconstruct, leftInverse⟩
  exact Forget_not_injective (leftInverse.injective)

theorem Forget_cannot_determine_K :
    ¬ ∃ readK : FiniteStrategicGame → ℚ,
      readK (Forget leftPath) = terminalAuthorityK leftProgram leftTerminal ∧
        readK (Forget rightPath) =
          terminalAuthorityK rightProgram rightTerminal := by
  rintro ⟨readK, leftRead, rightRead⟩
  apply terminalAuthorityK_ne
  calc
    terminalAuthorityK leftProgram leftTerminal =
        readK (Forget leftPath) := leftRead.symm
    _ = readK (Forget rightPath) :=
      congrArg readK equal_normalized_classical_image
    _ = terminalAuthorityK rightProgram rightTerminal := rightRead

theorem Forget_has_no_occurrence_reconstruction :
    ¬ ∃ reconstruct : FiniteStrategicGame →
        RootedAccountedUnfolding FreeClassicalAtom,
      reconstruct (Forget leftPath) = leftProgram.occurrence ∧
        reconstruct (Forget rightPath) = rightProgram.occurrence := by
  rintro ⟨reconstruct, leftRead, rightRead⟩
  apply source_occurrences_ne
  calc
    leftProgram.occurrence = reconstruct (Forget leftPath) := leftRead.symm
    _ = reconstruct (Forget rightPath) :=
      congrArg reconstruct equal_normalized_classical_image
    _ = rightProgram.occurrence := rightRead

/-- Public M5 mouth.  The `leftConsumer` and `rightConsumer` fields carry the
fulfilled authority leg, whole fulfilled exchange, exact source event and
membership, native responsibility consumer, and residual identity. -/
structure SourceFirstCrossOccurrenceResidualCertificate : Prop where
  leftSyntaxExact : syntaxOf leftCode = leftProgram
  rightSyntaxExact : syntaxOf rightCode = rightProgram
  sameClassicalSource :
    leftProgram.playerCount = rightProgram.playerCount ∧
      leftProgram.strategyCounts = rightProgram.strategyCounts ∧
      leftProgram.terminalFlags = rightProgram.terminalFlags ∧
      leftProgram.settlementValues = rightProgram.settlementValues
  authorityStreams :
    leftProgram.authorityResiduals = [1] ∧
      rightProgram.authorityResiduals = [0]
  differentPrograms : leftProgram ≠ rightProgram
  differentOccurrences : leftProgram.occurrence ≠ rightProgram.occurrence
  leftGeneratedTerminal : leftProgram.isWorldTerminal
    (leftProgram.generatedProfileEquivCanonical leftGeneratedProfile) = true
  leftConsumer : TerminalAuthorityConsumerAt leftProgram leftTerminal
  rightConsumer : TerminalAuthorityConsumerAt rightProgram rightTerminal
  leftExactSourceEvent :
    (exactTerminalExchangeSeed leftProgram leftTerminal).sourceEvent
        (terminalExchangeCompiler leftProgram)
        (terminalAuthorityLeg leftProgram leftTerminal) =
      leftProgram.authorityAtom (terminalProfile leftProgram leftTerminal)
        (firstTerminalLegBase leftProgram)
  rightExactSourceEvent :
    (exactTerminalExchangeSeed rightProgram rightTerminal).sourceEvent
        (terminalExchangeCompiler rightProgram)
        (terminalAuthorityLeg rightProgram rightTerminal) =
      rightProgram.authorityAtom (terminalProfile rightProgram rightTerminal)
        (firstTerminalLegBase rightProgram)
  leftK : terminalAuthorityK leftProgram leftTerminal = 1
  rightK : terminalAuthorityK rightProgram rightTerminal = 0
  differentK : terminalAuthorityK leftProgram leftTerminal ≠
    terminalAuthorityK rightProgram rightTerminal
  leftNormalization : Nonempty
    (StrategicGameIso (recovered leftCode) (Forget leftPath))
  rightNormalization : Nonempty
    (StrategicGameIso (recovered rightCode) (Forget rightPath))
  honestCrossOccurrenceIso : Nonempty
    (StrategicGameIso (recovered leftCode) (recovered rightCode))
  terminalProfileCommutes :
    leftRightCodeIso.profileEquiv leftAnchoredProfile = rightAnchoredProfile
  exactTerminalGeneratedProfileCommutes :
    leftRightProgramIso.profileEquiv leftProgramTerminalProfile =
      rightProgramTerminalProfile
  equalClassicalImage : Forget leftPath = Forget rightPath
  forgetNotInjective : ¬ Function.Injective Forget
  noLeftInverse : ¬ ∃ reconstruct : FiniteStrategicGame → PathIndex,
    Function.LeftInverse reconstruct Forget
  noKReadout : ¬ ∃ readK : FiniteStrategicGame → ℚ,
    readK (Forget leftPath) = terminalAuthorityK leftProgram leftTerminal ∧
      readK (Forget rightPath) =
        terminalAuthorityK rightProgram rightTerminal
  noOccurrenceReconstruction :
    ¬ ∃ reconstruct : FiniteStrategicGame →
        RootedAccountedUnfolding FreeClassicalAtom,
      reconstruct (Forget leftPath) = leftProgram.occurrence ∧
        reconstruct (Forget rightPath) = rightProgram.occurrence

theorem sourceFirstCrossOccurrenceResidualDirectConsumer :
    SourceFirstCrossOccurrenceResidualCertificate where
  leftSyntaxExact := syntaxOf_validCodeOfSyntax leftProgram
  rightSyntaxExact := M4SourceFirstIndependentPreimageRegression.syntaxOf_code
  sameClassicalSource := classical_source_fields_agree
  authorityStreams := ⟨rfl, rfl⟩
  differentPrograms := source_programs_ne
  differentOccurrences := source_occurrences_ne
  leftGeneratedTerminal := leftGeneratedProfile_terminal
  leftConsumer := leftAuthorityConsumer
  rightConsumer := rightAuthorityConsumer
  leftExactSourceEvent := leftAuthorityConsumer.exactSourceEvent
  rightExactSourceEvent := rightAuthorityConsumer.exactSourceEvent
  leftK := left_terminalAuthorityK
  rightK := right_terminalAuthorityK
  differentK := terminalAuthorityK_ne
  leftNormalization := ⟨leftNormalization⟩
  rightNormalization := ⟨rightNormalization⟩
  honestCrossOccurrenceIso := ⟨leftRightCodeIso⟩
  terminalProfileCommutes := terminal_profile_commutes
  exactTerminalGeneratedProfileCommutes :=
    exact_terminal_generated_profile_commutes
  equalClassicalImage := equal_normalized_classical_image
  forgetNotInjective := Forget_not_injective
  noLeftInverse := Forget_has_no_left_inverse
  noKReadout := Forget_cannot_determine_K
  noOccurrenceReconstruction := Forget_has_no_occurrence_reconstruction

end
end M5SourceFirstCrossOccurrenceResidual
end Society
end ProcessGame
end SaturationMonoid
