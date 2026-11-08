import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Adapters.KataGoClosureConsumer
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Ko.PhasePath

/-!
# G6 checked KataGo closure consumer regression

The external fixture compares `C2` with the ko capture `B3` at the exact G5
3×3 setup.  Both candidates are compiled against one and the same source
obligation face.  KataGo metadata is attached only after their closure gains
have been generated.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G6KataGoConsumerRegression

open Obligation
open Ko KoReachableCycle

private theorem relationFreedom_eq_empty_of_root_false
    {n : Nat} {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (horizon : Nat) (relation : RelationProbe n)
    (rootFalse : relation.holds replay.final = false) :
    relationFreedom replay horizon relation = ∅ := by
  apply Finset.Subset.antisymm
  · intro word member
    have survival :=
      ((mem_relationFreedom_iff replay horizon relation word).mp member).2.2
    cases word <;> simp [relationSurvivesWord, rootFalse] at survival
  · exact Finset.empty_subset _

private theorem emptyWord_mem_relationFreedom_of_root_true
    {n : Nat} {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (horizon : Nat) (relation : RelationProbe n)
    (rootTrue : relation.holds replay.final = true) :
    ([] : List (Move n)) ∈ relationFreedom replay horizon relation := by
  apply (mem_relationFreedom_iff replay horizon relation []).mpr
  exact ⟨by simp, rfl, by simpa [relationSurvivesWord] using rootTrue⟩

def c2 : Point 3 := (1, 2)

theorem c2_target_isSome :
    (nativeStep? (law .positionalSuperko)
      (setupReplay .positionalSuperko).final (.play c2)).isSome = true := by
  decide

def c2Target : Frame 3 :=
  (nativeStep? (law .positionalSuperko)
    (setupReplay .positionalSuperko).final (.play c2)).get c2_target_isSome

def c2Ply : GeneratedReplay.ActualPly
    (setupReplay .positionalSuperko) where
  target := c2Target
  emitted := .play c2
  step := by
    unfold LegalStep c2Target
    exact (Option.some_get c2_target_isSome).symm

inductive KataIncidence where
  | opponentTurn
  | c2Stone
  | threatControl
  | b3Vacancy
  deriving DecidableEq, Repr

def setupOpponentTurnRelation : RelationProbe 3 where
  holds := fun frame => decide
    (frame.visible.toMove ≠
      (setupReplay .positionalSuperko).final.visible.toMove)

def c2StoneRelation : RelationProbe 3 where
  holds := fun frame => decide
    (frame.visible.board c2 = some .positive)

def b3VacancyRelation : RelationProbe 3 where
  holds := fun frame => decide (frame.visible.board p01 = none)

def setupOpponentTurnLineage : RelationLineage 1 koPhaseTransport
    (setupReplay .positionalSuperko) setupOpponentTurnRelation .impose :=
  .marked (setupReplay .positionalSuperko) setupOpponentTurnRelation
    (by trivial)

def c2StoneLineage : RelationLineage 1 koPhaseTransport
    (setupReplay .positionalSuperko) c2StoneRelation .impose :=
  .marked (setupReplay .positionalSuperko) c2StoneRelation (by trivial)

def b3VacancyLineage : RelationLineage 1 koPhaseTransport
    (setupReplay .positionalSuperko) b3VacancyRelation .impose :=
  .marked (setupReplay .positionalSuperko) b3VacancyRelation (by trivial)

def kataFace : OpenRelationObligationFace
    (setupReplay .positionalSuperko) KataIncidence where
  incidences := {.opponentTurn, .c2Stone, .threatControl, .b3Vacancy}
  horizon := fun _ => 1
  transport := fun _ => koPhaseTransport
  relation := fun key =>
    match key.1 with
    | .opponentTurn => setupOpponentTurnRelation
    | .c2Stone => c2StoneRelation
    | .threatControl => koThreatControlProbe .positionalSuperko
    | .b3Vacancy => b3VacancyRelation
  state := fun _ => .impose
  lineage := fun key =>
    match key.1 with
    | .opponentTurn => setupOpponentTurnLineage
    | .c2Stone => c2StoneLineage
    | .threatControl => koThreatControlLineage .positionalSuperko
    | .b3Vacancy => b3VacancyLineage

def opponentKey : kataFace.SourceKey :=
  ⟨.opponentTurn, by simp [kataFace]⟩
def c2StoneKey : kataFace.SourceKey :=
  ⟨.c2Stone, by simp [kataFace]⟩
def threatKey : kataFace.SourceKey :=
  ⟨.threatControl, by simp [kataFace]⟩
def vacancyKey : kataFace.SourceKey :=
  ⟨.b3Vacancy, by simp [kataFace]⟩

def strongUpdate : GeneratedObligationUpdate kataFace c2Ply :=
  GeneratedObligationUpdate.compile kataFace c2Ply

def candidateUpdate : GeneratedObligationUpdate kataFace
    (capturePly .positionalSuperko) :=
  GeneratedObligationUpdate.compile kataFace
    (capturePly .positionalSuperko)

private theorem grows_from_setup_false_to_true
    {ply : GeneratedReplay.ActualPly (setupReplay .positionalSuperko)}
    (relation : RelationProbe 3)
    (sourceFalse : relation.holds
      (setupReplay .positionalSuperko).final = false)
    (targetTrue : relation.holds ply.extended.final = true) :
    FreedomGrowsAt ply 1 relation := by
  refine ⟨?_, [], ?_, ?_⟩
  · rw [relationFreedom_eq_empty_of_root_false _ 1 relation sourceFalse]
    exact Finset.empty_subset _
  · exact emptyWord_mem_relationFreedom_of_root_true
      ply.extended 1 relation targetTrue
  · rw [relationFreedom_eq_empty_of_root_false _ 1 relation sourceFalse]
    simp

private theorem shrinks_from_setup_true_to_false
    {ply : GeneratedReplay.ActualPly (setupReplay .positionalSuperko)}
    (relation : RelationProbe 3)
    (sourceTrue : relation.holds
      (setupReplay .positionalSuperko).final = true)
    (targetFalse : relation.holds ply.extended.final = false) :
    FreedomShrinksAt ply 1 relation := by
  refine ⟨?_, [], ?_, ?_⟩
  · rw [relationFreedom_eq_empty_of_root_false _ 1 relation targetFalse]
    exact Finset.empty_subset _
  · exact emptyWord_mem_relationFreedom_of_root_true
      (setupReplay .positionalSuperko) 1 relation sourceTrue
  · rw [relationFreedom_eq_empty_of_root_false _ 1 relation targetFalse]
    simp

theorem c2_opponent_turn_grows :
    (kataFace.edgeAt c2Ply opponentKey).comparison = .grow := by
  apply (relationComparisonAt_retain_eq_grow_iff c2Ply 1
    setupOpponentTurnRelation).mpr
  exact grows_from_setup_false_to_true setupOpponentTurnRelation
    (by decide) (by decide)

theorem c2_stone_relation_grows :
    (kataFace.edgeAt c2Ply c2StoneKey).comparison = .grow := by
  apply (relationComparisonAt_retain_eq_grow_iff c2Ply 1
    c2StoneRelation).mpr
  exact grows_from_setup_false_to_true c2StoneRelation
    (by decide) (by decide)

theorem c2_threat_control_shrinks :
    (kataFace.edgeAt c2Ply threatKey).comparison = .shrink := by
  apply (relationComparisonAt_retain_eq_shrink_iff c2Ply 1
    (koThreatControlProbe .positionalSuperko)).mpr
  exact shrinks_from_setup_true_to_false
    (koThreatControlProbe .positionalSuperko) (by decide) (by decide)

theorem c2_vacancy_shrinks :
    (kataFace.edgeAt c2Ply vacancyKey).comparison = .shrink := by
  decide

theorem b3_opponent_turn_grows :
    (kataFace.edgeAt (capturePly .positionalSuperko)
      opponentKey).comparison = .grow := by
  apply (relationComparisonAt_retain_eq_grow_iff
    (capturePly .positionalSuperko) 1 setupOpponentTurnRelation).mpr
  exact grows_from_setup_false_to_true setupOpponentTurnRelation
    (by decide) (by decide)

theorem b3_threat_control_shrinks :
    (kataFace.edgeAt (capturePly .positionalSuperko)
      threatKey).comparison = .shrink := by
  simpa [kataFace, threatKey, OpenRelationObligationFace.edgeAt,
    RelationPhaseEdge.comparison, capturePhaseEdge] using
      capture_comparison_eq_shrink .positionalSuperko

theorem b3_vacancy_shrinks :
    (kataFace.edgeAt (capturePly .positionalSuperko)
      vacancyKey).comparison = .shrink := by
  apply (relationComparisonAt_retain_eq_shrink_iff
    (capturePly .positionalSuperko) 1 b3VacancyRelation).mpr
  exact shrinks_from_setup_true_to_false b3VacancyRelation
    (by decide) (by decide)

theorem b3_c2_stone_neither_settles_nor_debts :
    (kataFace.edgeAt (capturePly .positionalSuperko)
      c2StoneKey).comparison ≠ .grow ∧
      (kataFace.edgeAt (capturePly .positionalSuperko)
        c2StoneKey).comparison ≠ .shrink := by
  have sourceEmpty := relationFreedom_eq_empty_of_root_false
    (setupReplay .positionalSuperko) 1 c2StoneRelation (by decide)
  have targetEmpty := relationFreedom_eq_empty_of_root_false
    (capturePly .positionalSuperko).extended 1 c2StoneRelation (by decide)
  unfold OpenRelationObligationFace.edgeAt RelationPhaseEdge.comparison
    relationComparisonAt
  change compareFreedom
      (relationFreedom (setupReplay .positionalSuperko) 1 c2StoneRelation)
      (relationFreedom (capturePly .positionalSuperko).extended 1
        c2StoneRelation) ≠ .grow ∧ _
  rw [sourceEmpty, targetEmpty]
  decide

theorem strongUpdate_exact_closure :
    strongUpdate.settledKeys =
        {ObligationKey.open .opponentTurn,
          ObligationKey.open .c2Stone} ∧
      strongUpdate.newDebtKeys =
        {ObligationKey.generatedDebt .threatControl,
          ObligationKey.generatedDebt .b3Vacancy} ∧
      closureGain strongUpdate = 0 := by
  decide

theorem candidateUpdate_exact_closure :
    candidateUpdate.settledKeys =
        {ObligationKey.open .opponentTurn} ∧
      candidateUpdate.newDebtKeys =
        {ObligationKey.generatedDebt .threatControl,
          ObligationKey.generatedDebt .b3Vacancy} ∧
      closureGain candidateUpdate = -1 := by
  decide

def c2Observation : KataGoClosureObservation strongUpdate where
  fixture := checkedKoFixtureMetadata
  external := checkedC2Datum

def b3Observation : KataGoClosureObservation candidateUpdate where
  fixture := checkedKoFixtureMetadata
  external := checkedB3Datum

theorem fixture_moves_match_exact_actual_plies :
    c2Observation.fixture.setupMoves =
        ["B pass", "W A3", "B A2", "W C3", "B pass", "W B2"] ∧
      c2Observation.external.moveLabel = "C2" ∧
      c2Ply.emitted = .play c2 ∧
      b3Observation.external.moveLabel = "B3" ∧
      (capturePly .positionalSuperko).emitted = .play p01 := by
  decide

theorem both_candidates_use_same_source_obligation_face :
    strongUpdate.majorEffects = candidateUpdate.majorEffects ∧
      strongUpdate.majorEffects = kataFace.incidences.attach :=
  ⟨rfl, rfl⟩

theorem katago_and_generated_closure_prefer_c2 :
    ExternalScoreAndClosurePrefer c2Observation b3Observation := by
  unfold ExternalScoreAndClosurePrefer
  constructor
  · rfl
  · constructor
    · decide
    · rw [KataGoClosureObservation.closureReadout_eq_generatedClosure,
        KataGoClosureObservation.closureReadout_eq_generatedClosure,
        strongUpdate_exact_closure.2.2,
        candidateUpdate_exact_closure.2.2]
      decide

def alteredExternalC2 : KataGoClosureObservation strongUpdate where
  fixture := checkedKoFixtureMetadata
  external := checkedB3Datum

theorem external_score_cannot_redefine_generated_closure :
    c2Observation.closureReadout = alteredExternalC2.closureReadout ∧
      c2Observation.external.scoreLeadScaled100000000 ≠
        alteredExternalC2.external.scoreLeadScaled100000000 :=
  ⟨KataGoClosureObservation.externalData_cannot_redefine_closure _ _, by decide⟩

end G6KataGoConsumerRegression
end Go
end ProcessGame
end SaturationMonoid
