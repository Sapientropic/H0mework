import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Classical.ProcessGameCrossOccurrenceResidual

/-!
# G7 strongest cross-occurrence classical residual regression

This consumer closes the distinction missed by the earlier same-replay
restriction theorem: the two witnesses are unequal actual occurrences, not
two keys on one replay.  Their generated terminal normal forms normalize to
one representative through exact `N/Sᵢ/uᵢ` transporters, while their
replay-native residuals remain different.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G7CrossOccurrenceClassicalResidualRegression

open CrossOccurrencePathResidual
open CrossOccurrenceClassicalResidual
open _root_.SaturationMonoid.ProcessGame.Go.Classical
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

def horizon : Nat := 1

theorem different_gamma_same_normalForm_different_K :
    koTerminalReplay.toOccurrence ≠ freshTerminalReplay.toOccurrence ∧
      Nonempty (CrossReplayNormalFormEquivalence
        koTerminalReplay freshTerminalReplay horizon) ∧
      actualizationK koTerminalReplay ≠
        actualizationK freshTerminalReplay :=
  distinct_paths_isomorphic_normalForms_different_K horizon

theorem common_representative_has_bidirectional_normalization :
    Nonempty (CrossReplayNormalFormEquivalence
      koTerminalReplay freshTerminalReplay horizon) ∧
      Nonempty (CrossReplayNormalFormEquivalence
        koTerminalReplay koTerminalReplay horizon) ∧
      Nonempty (CrossReplayNormalFormEquivalence
        freshTerminalReplay koTerminalReplay horizon) :=
  ⟨⟨normalFormEquivalence horizon⟩,
    (Forget_normalization_sound horizon).1,
    (Forget_normalization_sound horizon).2⟩

theorem normalForm_N_Si_profile_ui_all_commute :
    (koNormalForm horizon).players.map
        (normalFormEquivalence horizon).playerEquiv =
          (freshNormalForm horizon).players ∧
      (forall player : (koNormalForm horizon).Player,
        Function.Bijective
          ((normalFormEquivalence horizon).strategyEquiv player)) ∧
      Function.Bijective (normalFormEquivalence horizon).profileEquiv ∧
      (forall profile player,
        ((normalFormEquivalence horizon).profileEquiv profile).strategy
            ((normalFormEquivalence horizon).playerEquiv player) =
          (normalFormEquivalence horizon).strategyEquiv player
            (profile.strategy player)) ∧
      (forall profile player,
        (freshNormalForm horizon).utility
            ((normalFormEquivalence horizon).profileEquiv profile)
            ((normalFormEquivalence horizon).playerEquiv player) =
          (koNormalForm horizon).utility profile player) :=
  ⟨normalForm_players_preserved horizon,
    fun player => (normalFormEquivalence horizon).strategyEquiv player |>.bijective,
    (normalFormEquivalence horizon).profileEquiv.bijective,
    (normalFormEquivalence horizon).profile_strategy_commutes,
    normalForm_utilities_preserved horizon⟩

theorem normalized_Forget_is_equal_noninjective_and_has_no_leftInverse :
    Forget horizon koPath = Forget horizon freshPath ∧
      ¬ Function.Injective (Forget horizon) ∧
      ¬ ∃ reconstruct :
          NormalFormProjection (terminalGame koTerminalReplay horizon) →
            PathIndex,
        Function.LeftInverse reconstruct (Forget horizon) :=
  ⟨Forget_ko_eq_fresh horizon, Forget_not_injective horizon,
    Forget_has_no_leftInverse horizon⟩

theorem normalized_Forget_reconstructs_neither_occurrence_nor_K :
    (¬ ∃ reconstruct :
        NormalFormProjection (terminalGame koTerminalReplay horizon) →
          RootedAccountedUnfolding (Frame 2),
      reconstruct (Forget horizon koPath) = koTerminalReplay.toOccurrence ∧
        reconstruct (Forget horizon freshPath) =
          freshTerminalReplay.toOccurrence) ∧
      (¬ ∃ readK :
        NormalFormProjection (terminalGame koTerminalReplay horizon) →
          TacticalPhase,
      readK (Forget horizon koPath) = actualizationK koTerminalReplay ∧
        readK (Forget horizon freshPath) =
          actualizationK freshTerminalReplay) :=
  ⟨Forget_has_no_occurrence_reconstruction horizon,
    Forget_cannot_determine_K horizon⟩

theorem G7_strongest_mouth_has_no_caller_premises :
    koTerminalReplay.toOccurrence ≠ freshTerminalReplay.toOccurrence ∧
      Nonempty (CrossReplayNormalFormEquivalence
        koTerminalReplay freshTerminalReplay horizon) ∧
      actualizationK koTerminalReplay ≠
        actualizationK freshTerminalReplay ∧
      Forget horizon koPath = Forget horizon freshPath ∧
      ¬ Function.Injective (Forget horizon) ∧
      ¬ ∃ reconstruct :
          NormalFormProjection (terminalGame koTerminalReplay horizon) →
            PathIndex,
        Function.LeftInverse reconstruct (Forget horizon) :=
  strongest_crossOccurrence_Forget_residual horizon

end G7CrossOccurrenceClassicalResidualRegression
end Go
end ProcessGame
end SaturationMonoid
