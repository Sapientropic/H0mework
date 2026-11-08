import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Strategy.ClosureGain

/-!
# Move coherence and `MakesSense`

The actual obligation compiler already fixes every target debt face.  This
module reads two exact properties from that output: major effects factor
through source-open obligations, and the generated target face contains all
and only carried obligations plus compiler-generated new debt.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

open Obligation

universe u

/-- Every major effect is indexed by an actually open source incidence. -/
def MajorEffectsFactorThroughOpen
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) : Prop :=
  ∀ effect, effect ∈ update.majorEffects →
    ObligationKey.open effect.1 ∈ face.openKeys

/-- Target-debt completeness is the exact compiler equation, stated as a
membership mouth so downstream consumers cannot supply a target set. -/
def GeneratedNewDebtComplete
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) : Prop :=
  ∀ key : ObligationKey Incidence,
    key ∈ update.targetFace ↔
      (key ∈ face.openKeys ∧ key ∉ update.settledKeys) ∨
        key ∈ update.newDebtKeys

/-- A move makes structural sense exactly when its principal effects factor
through open obligations and its generated new-debt face is complete. -/
def MakesSense
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) : Prop :=
  MajorEffectsFactorThroughOpen update ∧ GeneratedNewDebtComplete update

theorem makesSense_iff_effectFactorization_and_debtComplete
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) :
    MakesSense update ↔
      MajorEffectsFactorThroughOpen update ∧
        GeneratedNewDebtComplete update :=
  Iff.rfl

/-- Every compiler-generated update satisfies `MakesSense`; this theorem
consumes the fixed target-face completeness theorem rather than receiving a
caller target. -/
theorem generatedUpdate_makesSense
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) :
    MakesSense update := by
  constructor
  · intro effect member
    exact update.majorEffect_mem_open effect member
  · intro key
    exact update.targetFace_complete_iff key

/-- Stone-count material readout; it has no role in closure-gain formation. -/
def stoneCount {n : Nat} (board : Board n) (polarity : Polarity) : Nat :=
  (Finset.univ.filter fun point => board point = some polarity).card

def MaterialSacrificeAt
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay)
    (polarity : Polarity) : Prop :=
  stoneCount ply.target.visible.board polarity <
    stoneCount replay.final.visible.board polarity

/-- A light disposition allows exact local material loss while one source
obligation remains carried, its relation lineage advances, and its target
future-freedom fibre is still inhabited. -/
structure LightMoveWitness
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) where
  sacrificedPolarity : Polarity
  materialSacrifice : MaterialSacrificeAt ply sacrificedPolarity
  carried : face.SourceKey
  carriedInTarget : ObligationKey.open carried.1 ∈ update.targetFace
  futureWord : List (Move n)
  futureWord_nonempty : futureWord ≠ []
  futureWordMem : futureWord ∈ relationFreedom ply.extended
    (face.horizon carried) (face.edgeAt ply carried).targetRelation

namespace LightMoveWitness

/-- Lineage transport is generated by the exact actual edge and is not a
field supplied by the lightness witness. -/
theorem relationLineage_transport
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    {update : GeneratedObligationUpdate face ply}
    (light : LightMoveWitness update) :
    Nonempty (RelationLineage (face.horizon light.carried)
      (face.transport light.carried) ply.extended
      (face.edgeAt ply light.carried).targetRelation
      (face.edgeAt ply light.carried).targetState) :=
  (face.edgeAt ply light.carried).targetLineage_preserves_relation_bearer

/-- The nonempty future word reconstructs an exact compiler continuation in
the same target future cone. -/
theorem futureFreedom_factors_through_targetCone
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    {update : GeneratedObligationUpdate face ply}
    (light : LightMoveWitness update) :
    ∃ continuation : GeneratedReplay law ply.extended.final light.futureWord,
      continuation.stateTrace ∈
          rootedPaths (futureConeAt ply.extended
            (face.horizon light.carried)) ∧
        continuation.stateTrace.all
          (face.edgeAt ply light.carried).targetRelation.holds = true :=
  relationFreedom_member_factors_through_futureCone ply.extended
    (face.horizon light.carried)
    (face.edgeAt ply light.carried).targetRelation light.futureWordMem

end LightMoveWitness

/-- Full move coherence combines compiler completeness with nonnegative
continuation balance. -/
def MoveCoherent
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) : Prop :=
  MakesSense update ∧ ContinuationCoherent update

theorem badMove_not_moveCoherent
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply)
    (bad : BadMove update) :
    ¬ MoveCoherent update := by
  intro coherent
  exact bad coherent.2

end Go
end ProcessGame
end SaturationMonoid
