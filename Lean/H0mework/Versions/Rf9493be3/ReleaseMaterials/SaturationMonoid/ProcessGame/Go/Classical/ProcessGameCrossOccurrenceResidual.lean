import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Classical.CrossOccurrencePathResidual
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Classical.NormalFormEquivalence

/-!
# Strict process residual across two actual Go occurrences

The two G1 paths are first extended by the same exact resignation.  Their
actual occurrences remain different, while their terminal classical normal
forms are equivalent at every finite horizon.  `actualizationK` is still
different because it is folded independently from each replay's own emitted
spine.

This is the cross-occurrence strengthening of the same-replay restriction
result in `ProcessGameStrictResidual`.  No replay, normal-form coordinate or
residual value is accepted from a caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace CrossOccurrenceClassicalResidual

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open CrossOccurrencePathResidual
open _root_.SaturationMonoid.ProcessGame.Go.Classical

/-- The left generated normal form; its dependent replay index is preserved. -/
abbrev koNormalForm (horizon : Nat) :=
  terminalNormalForm koTerminalReplay horizon

/-- The right generated normal form; its dependent replay index is preserved. -/
abbrev freshNormalForm (horizon : Nat) :=
  terminalNormalForm freshTerminalReplay horizon

/-- Legitimate transporter between the two terminal normal forms.  The
underlying actual occurrences are not identified. -/
def normalFormEquivalence (horizon : Nat) :
    CrossReplayNormalFormEquivalence
      koTerminalReplay freshTerminalReplay horizon :=
  terminalNormalFormEquivalence koTerminalReplay freshTerminalReplay horizon
    (.resignation .negative) terminal_visible_eq terminal_status_eq.1

/-- Reverse transporter used to normalize the fresh path to the fixed left
generated representative. -/
def freshNormalFormEquivalenceToRepresentative (horizon : Nat) :
    CrossReplayNormalFormEquivalence
      freshTerminalReplay koTerminalReplay horizon :=
  terminalNormalFormEquivalence freshTerminalReplay koTerminalReplay horizon
    (.resignation .negative) terminal_visible_eq.symm terminal_status_eq.2

/-- The representative normal form normalizes to itself through the same
generated transporter interface. -/
def koNormalFormEquivalenceToRepresentative (horizon : Nat) :
    CrossReplayNormalFormEquivalence
      koTerminalReplay koTerminalReplay horizon :=
  terminalNormalFormEquivalence koTerminalReplay koTerminalReplay horizon
    (.resignation .negative) rfl terminal_status_eq.1

theorem normalForm_players_preserved (horizon : Nat) :
    (koNormalForm horizon).players.map
        (normalFormEquivalence horizon).playerEquiv =
      (freshNormalForm horizon).players :=
  (normalFormEquivalence horizon).players_map

theorem normalForm_strategies_preserved (horizon : Nat)
    (player : (koNormalForm horizon).Player) :
    Nonempty ((koNormalForm horizon).StrategyFor player ≃
      (freshNormalForm horizon).StrategyFor
        ((normalFormEquivalence horizon).playerEquiv player)) :=
  ⟨(normalFormEquivalence horizon).strategyEquiv player⟩

theorem normalForm_profiles_preserved (horizon : Nat) :
    Nonempty ((koNormalForm horizon).Profile ≃
      (freshNormalForm horizon).Profile) :=
  ⟨(normalFormEquivalence horizon).profileEquiv⟩

theorem normalForm_utilities_preserved (horizon : Nat)
    (profile : (koNormalForm horizon).Profile)
    (player : (koNormalForm horizon).Player) :
    (freshNormalForm horizon).utility
        ((normalFormEquivalence horizon).profileEquiv profile)
        ((normalFormEquivalence horizon).playerEquiv player) =
      (koNormalForm horizon).utility profile player :=
  (normalFormEquivalence horizon).utility_preserved profile player

theorem actualizationK_ne :
    actualizationK koTerminalReplay ≠
      actualizationK freshTerminalReplay := by
  rw [koTerminalK_eq_one, freshTerminalK_eq_zero]
  decide

/-! ## Common generated classical representative and Forget -/

/-- The two fixed witnesses are selected with the existing finite type; no
path registry or second occurrence carrier is introduced. -/
abbrev PathIndex := Fin 2

def koPath : PathIndex := 0
def freshPath : PathIndex := 1

theorem koPath_ne_freshPath : koPath ≠ freshPath := by
  decide

/-- Exact fresh normal form normalized to the fixed ko representative.  Both
the source token and the reverse transporter are exact closed producers. -/
def normalizedFreshNormalForm (horizon : Nat) :
    NormalFormProjection (terminalGame koTerminalReplay horizon) :=
  match freshNormalFormEquivalenceToRepresentative horizon,
      freshNormalForm horizon with
  | _, .generated => .generated

/-- Cross-occurrence classical projection into one generated representative.
The fresh branch is admitted only through its exact normal-form transporter;
the caller supplies no normalizer or target coordinates. -/
def Forget (horizon : Nat) (path : PathIndex) :
    NormalFormProjection (terminalGame koTerminalReplay horizon) :=
  if path = koPath then koNormalForm horizon
  else normalizedFreshNormalForm horizon

/-- Both actual paths have a generated normalization to the chosen common
representative; this is the soundness bridge behind `Forget`. -/
theorem Forget_normalization_sound (horizon : Nat) :
    Nonempty (CrossReplayNormalFormEquivalence
      koTerminalReplay koTerminalReplay horizon) ∧
      Nonempty (CrossReplayNormalFormEquivalence
        freshTerminalReplay koTerminalReplay horizon) :=
  ⟨⟨koNormalFormEquivalenceToRepresentative horizon⟩,
    ⟨freshNormalFormEquivalenceToRepresentative horizon⟩⟩

theorem Forget_ko_eq_fresh (horizon : Nat) :
    Forget horizon koPath = Forget horizon freshPath := by
  unfold Forget
  simp [normalizedFreshNormalForm, koNormalForm,
    terminalNormalForm, toNormalForm]

theorem Forget_not_injective (horizon : Nat) :
    ¬ Function.Injective (Forget horizon) := by
  intro injective
  exact koPath_ne_freshPath (injective (Forget_ko_eq_fresh horizon))

theorem Forget_has_no_leftInverse (horizon : Nat) :
    ¬ ∃ reconstruct :
        NormalFormProjection (terminalGame koTerminalReplay horizon) →
          PathIndex,
      Function.LeftInverse reconstruct (Forget horizon) := by
  rintro ⟨_reconstruct, leftInverse⟩
  exact Forget_not_injective horizon leftInverse.injective

/-- Strong §22.4 mouth: the paths are genuinely different actual
occurrences, their complete generated normal-form coordinates are connected
by an honest transporter, and their independently generated residuals differ.
-/
theorem distinct_paths_isomorphic_normalForms_different_K (horizon : Nat) :
    koTerminalReplay.toOccurrence ≠ freshTerminalReplay.toOccurrence ∧
      Nonempty (CrossReplayNormalFormEquivalence
        koTerminalReplay freshTerminalReplay horizon) ∧
      actualizationK koTerminalReplay ≠
        actualizationK freshTerminalReplay :=
  ⟨terminal_occurrences_ne, ⟨normalFormEquivalence horizon⟩,
    actualizationK_ne⟩

/-- Full cross-occurrence strict residual: unequal actual paths, honest
normal-form equivalence, independently different `K`, equal normalized
classical images, and failure of both injectivity and left reconstruction.
-/
theorem strongest_crossOccurrence_Forget_residual (horizon : Nat) :
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
  ⟨terminal_occurrences_ne, ⟨normalFormEquivalence horizon⟩,
    actualizationK_ne, Forget_ko_eq_fresh horizon,
    Forget_not_injective horizon, Forget_has_no_leftInverse horizon⟩

/-- Equal images cannot reconstruct two unequal occurrence authorities.  This
is the direct consumer for any classical normalization which identifies the
two isomorphic normal forms in a common carrier. -/
theorem equal_classical_images_have_no_occurrence_reconstruction
    {ClassicalImage : Type*} {koImage freshImage : ClassicalImage}
    (imagesEqual : koImage = freshImage) :
    ¬ ∃ reconstruct : ClassicalImage →
        RootedAccountedUnfolding (Frame 2),
      reconstruct koImage = koTerminalReplay.toOccurrence ∧
        reconstruct freshImage = freshTerminalReplay.toOccurrence := by
  rintro ⟨reconstruct, reconstructKo, reconstructFresh⟩
  apply terminal_occurrences_ne
  calc
    koTerminalReplay.toOccurrence = reconstruct koImage := reconstructKo.symm
    _ = reconstruct freshImage := congrArg reconstruct imagesEqual
    _ = freshTerminalReplay.toOccurrence := reconstructFresh

/-- The same equality of classical images cannot carry the path residual.
Thus `K` does not factor through any isomorphism-invariant classical image of
this pair. -/
theorem equal_classical_images_cannot_determine_K
    {ClassicalImage : Type*} {koImage freshImage : ClassicalImage}
    (imagesEqual : koImage = freshImage) :
    ¬ ∃ readK : ClassicalImage → TacticalPhase,
      readK koImage = actualizationK koTerminalReplay ∧
        readK freshImage = actualizationK freshTerminalReplay := by
  rintro ⟨readK, readKo, readFresh⟩
  apply actualizationK_ne
  calc
    actualizationK koTerminalReplay = readK koImage := readKo.symm
    _ = readK freshImage := congrArg readK imagesEqual
    _ = actualizationK freshTerminalReplay := readFresh

/-- Concrete endpoint consumer: even the exactly equal terminal visible
readout cannot reconstruct the two actual occurrences. -/
theorem terminalVisible_has_no_occurrence_reconstruction :
    ¬ ∃ reconstruct : VisiblePosition 2 →
        RootedAccountedUnfolding (Frame 2),
      reconstruct koTerminalReplay.final.visible =
          koTerminalReplay.toOccurrence ∧
        reconstruct freshTerminalReplay.final.visible =
          freshTerminalReplay.toOccurrence :=
  equal_classical_images_have_no_occurrence_reconstruction terminal_visible_eq

/-- Concrete endpoint consumer: the independently folded `K` cannot be read
back from the exactly equal terminal visible position. -/
theorem terminalVisible_cannot_determine_K :
    ¬ ∃ readK : VisiblePosition 2 → TacticalPhase,
      readK koTerminalReplay.final.visible =
          actualizationK koTerminalReplay ∧
        readK freshTerminalReplay.final.visible =
          actualizationK freshTerminalReplay :=
  equal_classical_images_cannot_determine_K terminal_visible_eq

/-- The normalized full classical image cannot reconstruct the two unequal
actual occurrences. -/
theorem Forget_has_no_occurrence_reconstruction (horizon : Nat) :
    ¬ ∃ reconstruct :
        NormalFormProjection (terminalGame koTerminalReplay horizon) →
          RootedAccountedUnfolding (Frame 2),
      reconstruct (Forget horizon koPath) =
          koTerminalReplay.toOccurrence ∧
        reconstruct (Forget horizon freshPath) =
          freshTerminalReplay.toOccurrence :=
  equal_classical_images_have_no_occurrence_reconstruction
    (Forget_ko_eq_fresh horizon)

/-- The normalized full classical image cannot determine the independently
generated residual either. -/
theorem Forget_cannot_determine_K (horizon : Nat) :
    ¬ ∃ readK :
        NormalFormProjection (terminalGame koTerminalReplay horizon) →
          TacticalPhase,
      readK (Forget horizon koPath) = actualizationK koTerminalReplay ∧
        readK (Forget horizon freshPath) =
          actualizationK freshTerminalReplay :=
  equal_classical_images_cannot_determine_K (Forget_ko_eq_fresh horizon)

end CrossOccurrenceClassicalResidual
end Go
end ProcessGame
end SaturationMonoid
