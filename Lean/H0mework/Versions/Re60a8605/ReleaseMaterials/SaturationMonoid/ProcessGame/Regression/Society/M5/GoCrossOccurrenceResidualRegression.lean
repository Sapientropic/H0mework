import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.Classical.G7CrossOccurrenceClassicalResidualRegression

/-!
# M5 Go cross-occurrence strict residual

This consumer is the strong cross-occurrence form, not the earlier pair of
lineage restrictions inside one replay.  The two existing G1 replay spines
and their actual occurrences are unequal.  At every finite horizon an honest
cross-replay transporter identifies their generated classical normal forms,
while the replay-native `actualizationK` values remain unequal and cannot be
reconstructed from the common `Forget` image.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M5GoCrossOccurrenceResidualRegression

open Go.CrossOccurrencePathResidual
open Go.CrossOccurrenceClassicalResidual
open _root_.SaturationMonoid.ProcessGame.Go.Classical
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

/-- One certificate exposes the entire strongest mouth at an arbitrary
observation horizon.  `differentReplaySpines` and `differentOccurrences`
rule out interpreting the witnesses as two restrictions of one replay. -/
structure GoCrossOccurrenceResidualCertificate (horizon : Nat) : Prop where
  differentReplaySpines :
    koTerminalReplay.stateTrace ≠ freshTerminalReplay.stateTrace
  differentOccurrences :
    koTerminalReplay.toOccurrence ≠ freshTerminalReplay.toOccurrence
  honestNormalForm :
    Nonempty (CrossReplayNormalFormEquivalence
      koTerminalReplay freshTerminalReplay horizon)
  differentK :
    actualizationK koTerminalReplay ≠ actualizationK freshTerminalReplay
  distinctPathWitnesses : koPath ≠ freshPath
  equalForget :
    Forget horizon koPath = Forget horizon freshPath
  forgetNotInjective : ¬ Function.Injective (Forget horizon)
  noLeftInverse :
    ¬ ∃ reconstruct :
        NormalFormProjection (terminalGame koTerminalReplay horizon) →
          PathIndex,
      Function.LeftInverse reconstruct (Forget horizon)
  noOccurrenceReconstruction :
    ¬ ∃ reconstruct :
        NormalFormProjection (terminalGame koTerminalReplay horizon) →
          RootedAccountedUnfolding (Go.Frame 2),
      reconstruct (Forget horizon koPath) = koTerminalReplay.toOccurrence ∧
        reconstruct (Forget horizon freshPath) =
          freshTerminalReplay.toOccurrence
  noReadK :
    ¬ ∃ readK :
        NormalFormProjection (terminalGame koTerminalReplay horizon) →
          Go.TacticalPhase,
      readK (Forget horizon koPath) = actualizationK koTerminalReplay ∧
        readK (Forget horizon freshPath) =
          actualizationK freshTerminalReplay

theorem goCrossOccurrenceResidualDirectConsumer (horizon : Nat) :
    GoCrossOccurrenceResidualCertificate horizon := by
  have strongest := strongest_crossOccurrence_Forget_residual horizon
  exact
    { differentReplaySpines := terminal_stateTraces_ne
      differentOccurrences := strongest.1
      honestNormalForm := strongest.2.1
      differentK := strongest.2.2.1
      distinctPathWitnesses := koPath_ne_freshPath
      equalForget := strongest.2.2.2.1
      forgetNotInjective := strongest.2.2.2.2.1
      noLeftInverse := strongest.2.2.2.2.2
      noOccurrenceReconstruction :=
        Forget_has_no_occurrence_reconstruction horizon
      noReadK := Forget_cannot_determine_K horizon }

end M5GoCrossOccurrenceResidualRegression
end Society
end ProcessGame
end SaturationMonoid
