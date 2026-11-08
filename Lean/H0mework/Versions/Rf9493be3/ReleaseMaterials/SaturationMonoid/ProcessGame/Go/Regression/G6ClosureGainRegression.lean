import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Strategy.ClosureInvariance
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G4TacticalPhaseRegression
import Mathlib.Tactic.FinCases

/-!
# G6 closure-gain regression

Two source-generated relation pairs are evaluated on two consecutive exact
2×2 actual plies.  The first move settles two independent obligations and has
closure gain `2`; its exact response generates two maintenance debts and has
gain `-2`.
Colour presentation and a nontrivial local key permutation preserve the first
gain.  Repeated consumer readouts do not alter the canonical update.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G6ClosureGainRegression

open Obligation
open G3SearchExposureRegression G4FutureFreedomRegression
open G4TacticalPhaseRegression

/-! ## One actual ply settles two independent obligations -/

inductive GainIncidence where
  | opponentTurn
  | placedStone
  deriving DecidableEq, Repr

/-- Source-fixed relation: the played point is occupied by the source mover. -/
def placedStoneRelation : RelationProbe 2 where
  holds := fun frame => decide
    (frame.visible.board p00 = some .positive)

def placedStoneLineage : RelationLineage 1 retainedLaw emptyReplay
    placedStoneRelation .impose :=
  .marked emptyReplay placedStoneRelation (by trivial)

def gainFace : OpenRelationObligationFace emptyReplay GainIncidence where
  incidences := {.opponentTurn, .placedStone}
  horizon := fun _ => 1
  transport := fun _ => retainedLaw
  relation := fun key =>
    match key.1 with
    | .opponentTurn => emptyOpponentTurnRelation
    | .placedStone => placedStoneRelation
  state := fun _ => .impose
  lineage := fun key =>
    match key.1 with
    | .opponentTurn => emptyOpponentTurnLineage
    | .placedStone => placedStoneLineage

def gainUpdate : GeneratedObligationUpdate gainFace chosenPly :=
  GeneratedObligationUpdate.compile gainFace chosenPly

def gainOpponentKey : gainFace.SourceKey :=
  ⟨.opponentTurn, by simp [gainFace]⟩

def gainStoneKey : gainFace.SourceKey :=
  ⟨.placedStone, by simp [gainFace]⟩

theorem gainUpdate_exact_ranks :
    gainUpdate.settledKeys =
        {ObligationKey.open .opponentTurn,
          ObligationKey.open .placedStone} ∧
      gainUpdate.newDebtKeys = ∅ ∧
      settledRank gainUpdate = 2 ∧
      newDebtRank gainUpdate = 0 := by
  decide

theorem one_move_two_obligations_gain_gt_one :
    closureGain gainUpdate = 2 ∧ MultiPurposeMove gainUpdate := by
  constructor
  · decide
  · unfold MultiPurposeMove
    decide

theorem gain_obligations_are_semantically_distinct :
    emptyOpponentTurnRelation ≠ placedStoneRelation := by
  intro equal
  have sameAtResponse := congrArg
    (fun relation : RelationProbe 2 =>
      relation.holds responsePly.extended.final) equal
  have different :
      emptyOpponentTurnRelation.holds responsePly.extended.final ≠
        placedStoneRelation.holds responsePly.extended.final := by
    decide
  exact different sameAtResponse

theorem repeated_readout_does_not_inflate_gain :
    gainUpdate.settledReadoutKeys
        [gainOpponentKey, gainOpponentKey, gainStoneKey] =
      gainUpdate.settledReadoutKeys [gainOpponentKey, gainStoneKey] ∧
    gainUpdate.newDebtReadoutKeys
        [gainOpponentKey, gainOpponentKey, gainStoneKey] =
      gainUpdate.newDebtReadoutKeys [gainOpponentKey, gainStoneKey] ∧
    closureGain gainUpdate = 2 := by
  exact ⟨(closureGain_ignores_duplicate_consumer_readout gainUpdate
    gainOpponentKey [gainStoneKey]).1,
    (closureGain_ignores_duplicate_consumer_readout gainUpdate
      gainOpponentKey [gainStoneKey]).2.1,
    one_move_two_obligations_gain_gt_one.1⟩

/-! ## The same actual ply generates two maintenance debts -/

inductive DebtIncidence where
  | control
  | playedPointVacancy
  deriving DecidableEq, Repr

def responsePointVacancyRelation : RelationProbe 2 where
  holds := fun frame => decide (frame.visible.board p11 = none)

def responsePointVacancyLineage : RelationLineage 1 retainedLaw
    chosenPly.extended responsePointVacancyRelation .impose :=
  .marked chosenPly.extended responsePointVacancyRelation (by trivial)

def debtFace : OpenRelationObligationFace
    chosenPly.extended DebtIncidence where
  incidences := {.control, .playedPointVacancy}
  horizon := fun _ => 1
  transport := fun _ => retainedLaw
  relation := fun key =>
    match key.1 with
    | .control => nextTurnRelation
    | .playedPointVacancy => responsePointVacancyRelation
  state := fun _ => .impose
  lineage := fun key =>
    match key.1 with
    | .control => opponentResponseLineage
    | .playedPointVacancy => responsePointVacancyLineage

def debtUpdate : GeneratedObligationUpdate debtFace responsePly :=
  GeneratedObligationUpdate.compile debtFace responsePly

theorem debtUpdate_exact_ranks :
    debtUpdate.settledKeys = ∅ ∧
      debtUpdate.newDebtKeys =
        {ObligationKey.generatedDebt .control,
          ObligationKey.generatedDebt .playedPointVacancy} ∧
      settledRank debtUpdate = 0 ∧
      newDebtRank debtUpdate = 2 := by
  decide

theorem heavy_move_generates_high_maintenance_debit :
    closureGain debtUpdate = -2 ∧
      MaintenanceDebit debtUpdate = 2 ∧
      HeavyMove debtUpdate := by
  constructor
  · decide
  · constructor
    · decide
    · unfold HeavyMove MaintenanceDebit
      decide

theorem debt_heavy_move_is_bad_and_incoherent :
    BadMove debtUpdate ∧ ¬ ContinuationCoherent debtUpdate := by
  constructor
  · unfold BadMove ContinuationCoherent
    decide
  · unfold ContinuationCoherent
    decide

/-! ## Exact G2 Z2 colour-presentation invariance -/

abbrev Z2GainIncidence := Bool × GainIncidence

def z2IncidenceEquiv : Z2GainIncidence ≃ Z2GainIncidence where
  toFun := fun incidence =>
    (GeneratedReplay.z2Swap true incidence.1, incidence.2)
  invFun := fun incidence =>
    (GeneratedReplay.z2Swap true incidence.1, incidence.2)
  left_inv := by
    intro incidence
    rcases incidence with ⟨label, incidence⟩
    cases label <;> rfl
  right_inv := by
    intro incidence
    rcases incidence with ⟨label, incidence⟩
    cases label <;> rfl

def z2LeftFace : OpenRelationObligationFace emptyReplay Z2GainIncidence where
  incidences := {(false, .opponentTurn), (false, .placedStone)}
  horizon := fun _ => 1
  transport := fun _ => retainedLaw
  relation := fun key =>
    match key.1.2 with
    | .opponentTurn => emptyOpponentTurnRelation
    | .placedStone => placedStoneRelation
  state := fun _ => .impose
  lineage := fun key =>
    match key.1.2 with
    | .opponentTurn => emptyOpponentTurnLineage
    | .placedStone => placedStoneLineage

def z2RightFace : OpenRelationObligationFace emptyReplay Z2GainIncidence where
  incidences := {(true, .opponentTurn), (true, .placedStone)}
  horizon := fun _ => 1
  transport := fun _ => retainedLaw
  relation := fun key =>
    match key.1.2 with
    | .opponentTurn => emptyOpponentTurnRelation
    | .placedStone => placedStoneRelation
  state := fun _ => .impose
  lineage := fun key =>
    match key.1.2 with
    | .opponentTurn => emptyOpponentTurnLineage
    | .placedStone => placedStoneLineage

def z2GeneratedEquivalence : GeneratedClosureUpdateEquivalence
    z2LeftFace z2RightFace chosenPly chosenPly where
  incidenceEquiv := z2IncidenceEquiv
  incidence_mem_iff := by
    intro incidence
    rcases incidence with ⟨label, incidence⟩
    cases label <;> cases incidence <;> decide
  comparison_commutes := by
    intro key
    rcases key with ⟨⟨label, incidence⟩, member⟩
    cases incidence <;> rfl

def z2LeftUpdate : GeneratedObligationUpdate z2LeftFace chosenPly :=
  GeneratedObligationUpdate.compile z2LeftFace chosenPly

def z2RightUpdate : GeneratedObligationUpdate z2RightFace chosenPly :=
  GeneratedObligationUpdate.compile z2RightFace chosenPly

theorem generated_Z2_colour_presentation_preserves_closure :
    z2LeftUpdate.settledKeys.image
          (obligationKeyEquiv z2IncidenceEquiv) =
        z2RightUpdate.settledKeys ∧
      z2LeftUpdate.newDebtKeys.image
          (obligationKeyEquiv z2IncidenceEquiv) =
        z2RightUpdate.newDebtKeys ∧
      closureGain z2LeftUpdate = closureGain z2RightUpdate :=
  ⟨z2GeneratedEquivalence.settledKeys_image,
    z2GeneratedEquivalence.newDebtKeys_image,
    z2GeneratedEquivalence.closureGain_eq⟩

/-! ## Exact empty-board p00 ↔ p11 local graph equivalence -/

def mirrorPoint : Point 2 := (1, 1)

theorem mirror_target_isSome :
    (nativeStep? testLaw emptyReplay.final (.play mirrorPoint)).isSome = true := by
  decide

def mirrorTarget : Frame 2 :=
  (nativeStep? testLaw emptyReplay.final (.play mirrorPoint)).get
    mirror_target_isSome

def mirrorPly : GeneratedReplay.ActualPly emptyReplay where
  target := mirrorTarget
  emitted := .play mirrorPoint
  step := by
    unfold LegalStep mirrorTarget
    exact (Option.some_get mirror_target_isSome).symm

def occupiedPointRelation (point : Point 2) : RelationProbe 2 where
  holds := fun frame => decide (frame.visible.board point = some .positive)

def occupiedPointLineage (point : Point 2) : RelationLineage 1 retainedLaw
    emptyReplay (occupiedPointRelation point) .impose :=
  .marked emptyReplay (occupiedPointRelation point) (by trivial)

def finRev2Equiv : Fin 2 ≃ Fin 2 where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_involutive
  right_inv := Fin.rev_involutive

def pointRevEquiv : Point 2 ≃ Point 2 :=
  Equiv.prodCongr finRev2Equiv finRev2Equiv

def localIncidenceEquiv : Option (Point 2) ≃ Option (Point 2) :=
  Equiv.optionCongr pointRevEquiv

def p00Face : OpenRelationObligationFace emptyReplay (Option (Point 2)) where
  incidences := {none, some p00}
  horizon := fun _ => 1
  transport := fun _ => retainedLaw
  relation := fun key =>
    match key.1 with
    | none => emptyOpponentTurnRelation
    | some point => occupiedPointRelation point
  state := fun _ => .impose
  lineage := fun key =>
    match key.1 with
    | none => emptyOpponentTurnLineage
    | some point => occupiedPointLineage point

def p11Face : OpenRelationObligationFace emptyReplay (Option (Point 2)) where
  incidences := {none, some mirrorPoint}
  horizon := fun _ => 1
  transport := fun _ => retainedLaw
  relation := fun key =>
    match key.1 with
    | none => emptyOpponentTurnRelation
    | some point => occupiedPointRelation point
  state := fun _ => .impose
  lineage := fun key =>
    match key.1 with
    | none => emptyOpponentTurnLineage
    | some point => occupiedPointLineage point

def localGraphGeneratedEquivalence : GeneratedClosureUpdateEquivalence
    p00Face p11Face chosenPly mirrorPly where
  incidenceEquiv := localIncidenceEquiv
  incidence_mem_iff := by intro incidence; fin_cases incidence <;> decide
  comparison_commutes := by intro key; fin_cases key <;> decide

def p00Update : GeneratedObligationUpdate p00Face chosenPly :=
  GeneratedObligationUpdate.compile p00Face chosenPly

def p11Update : GeneratedObligationUpdate p11Face mirrorPly :=
  GeneratedObligationUpdate.compile p11Face mirrorPly

theorem generated_local_graph_equivalence_preserves_closure :
    p00Update.settledKeys.image
          (obligationKeyEquiv localIncidenceEquiv) = p11Update.settledKeys ∧
      p00Update.newDebtKeys.image
          (obligationKeyEquiv localIncidenceEquiv) = p11Update.newDebtKeys ∧
      closureGain p00Update = closureGain p11Update ∧
      localIncidenceEquiv (some p00) = some mirrorPoint :=
  ⟨localGraphGeneratedEquivalence.settledKeys_image,
    localGraphGeneratedEquivalence.newDebtKeys_image,
    localGraphGeneratedEquivalence.closureGain_eq, by decide⟩

end G6ClosureGainRegression
end Go
end ProcessGame
end SaturationMonoid
