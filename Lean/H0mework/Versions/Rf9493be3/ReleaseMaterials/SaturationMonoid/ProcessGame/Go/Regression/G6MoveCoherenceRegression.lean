import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Strategy.MoveCoherence
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G6ClosureGainRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Ko.PhasePath

/-!
# G6 move-coherence regression

Canonical obligation updates satisfy the exact `MakesSense` factorization and
debt-completeness equivalence.  Positive closure is coherent; a compiler-valid
heavy move can still be strategically bad because its generated maintenance
debt outranks settlement.  The ko recapture supplies the light disposition:
one positive stone is sacrificed while an exact turn-relation lineage and a
nonempty future-freedom fibre are transported.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G6MoveCoherenceRegression

open Obligation
open G6ClosureGainRegression
open Ko KoReachableCycle

/-! ## MakesSense is exact compiler coherence -/

theorem multipurpose_update_makes_sense_and_is_coherent :
    MakesSense gainUpdate ∧ MoveCoherent gainUpdate := by
  refine ⟨generatedUpdate_makesSense gainUpdate,
    generatedUpdate_makesSense gainUpdate, ?_⟩
  unfold ContinuationCoherent
  decide

theorem makesSense_exact_iff_on_multipurpose_update :
    MakesSense gainUpdate ↔
      MajorEffectsFactorThroughOpen gainUpdate ∧
        GeneratedNewDebtComplete gainUpdate :=
  makesSense_iff_effectFactorization_and_debtComplete gainUpdate

/-- The target equation is consumed from the canonical compiler; no proposed
target debt set appears in the theorem mouth. -/
theorem multipurpose_target_debt_is_complete :
    GeneratedNewDebtComplete gainUpdate ∧
      gainUpdate.targetFace =
        (gainFace.openKeys \ gainUpdate.settledKeys) ∪
          gainUpdate.newDebtKeys :=
  ⟨(generatedUpdate_makesSense gainUpdate).2,
    gainUpdate.targetFace_eq⟩

/-- High-debt play is still a well-formed compiler update, but it fails the
strategic continuation-coherence face. -/
theorem heavy_update_makes_sense_but_is_bad :
    MakesSense debtUpdate ∧ BadMove debtUpdate ∧
      ¬ MoveCoherent debtUpdate := by
  exact ⟨generatedUpdate_makesSense debtUpdate,
    debt_heavy_move_is_bad_and_incoherent.1,
    badMove_not_moveCoherent debtUpdate
      debt_heavy_move_is_bad_and_incoherent.1⟩

/-! ## Light material sacrifice with transported relation freedom -/

inductive LightIncidence where
  | turnCarry
  deriving DecidableEq, Repr

def lightReplay := beforeRecaptureReplay .positionalSuperko

def lightRelation : RelationProbe 3 :=
  sourceTurnRelationAt lightReplay

def lightTransport : RelationTransportLaw 3 :=
  RelationTransportLaw.advanceTurn 3

def lightLineage : RelationLineage 1 lightTransport lightReplay
    lightRelation .impose :=
  .marked lightReplay lightRelation rfl

def lightFace : OpenRelationObligationFace lightReplay LightIncidence where
  incidences := {.turnCarry}
  horizon := fun _ => 1
  transport := fun _ => lightTransport
  relation := fun _ => lightRelation
  state := fun _ => .impose
  lineage := fun _ => lightLineage

def lightKey : lightFace.SourceKey :=
  ⟨.turnCarry, by simp [lightFace]⟩

def lightUpdate : GeneratedObligationUpdate lightFace
    (recapturePly .positionalSuperko) :=
  GeneratedObligationUpdate.compile lightFace
    (recapturePly .positionalSuperko)

theorem recapture_sacrifices_positive_material :
    MaterialSacrificeAt (recapturePly .positionalSuperko) .positive := by
  unfold MaterialSacrificeAt stoneCount
  decide

theorem light_key_is_carried_and_target_freedom_nonempty :
    ObligationKey.open .turnCarry ∈ lightUpdate.targetFace ∧
      ([.resign] : List (Move 3)) ∈
        relationFreedom (recapturePly .positionalSuperko).extended 1
          (lightFace.edgeAt (recapturePly .positionalSuperko)
            lightKey).targetRelation := by
  constructor <;> decide

def exactLightMove : LightMoveWitness lightUpdate where
  sacrificedPolarity := .positive
  materialSacrifice := recapture_sacrifices_positive_material
  carried := lightKey
  carriedInTarget := light_key_is_carried_and_target_freedom_nonempty.1
  futureWord := [.resign]
  futureWord_nonempty := by simp
  futureWordMem := light_key_is_carried_and_target_freedom_nonempty.2

theorem light_move_transports_lineage_and_future_freedom :
    MaterialSacrificeAt (recapturePly .positionalSuperko)
        exactLightMove.sacrificedPolarity ∧
      Nonempty (RelationLineage 1 lightTransport
        (recapturePly .positionalSuperko).extended
        (lightFace.edgeAt (recapturePly .positionalSuperko)
          lightKey).targetRelation
        (lightFace.edgeAt (recapturePly .positionalSuperko)
          lightKey).targetState) ∧
      exactLightMove.futureWord ∈
        relationFreedom (recapturePly .positionalSuperko).extended 1
          (lightFace.edgeAt (recapturePly .positionalSuperko)
            lightKey).targetRelation ∧
      ∃ continuation : GeneratedReplay (law .positionalSuperko)
          (recapturePly .positionalSuperko).extended.final
          exactLightMove.futureWord,
        continuation.stateTrace ∈
            rootedPaths (futureConeAt
              (recapturePly .positionalSuperko).extended 1) ∧
          continuation.stateTrace.all
            (lightFace.edgeAt (recapturePly .positionalSuperko)
              lightKey).targetRelation.holds = true :=
  ⟨exactLightMove.materialSacrifice,
    exactLightMove.relationLineage_transport,
    exactLightMove.futureWordMem,
    exactLightMove.futureFreedom_factors_through_targetCone⟩

end G6MoveCoherenceRegression
end Go
end ProcessGame
end SaturationMonoid
