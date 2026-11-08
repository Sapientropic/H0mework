import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.AttackDefensePhaseReadout

/-!
# Finite exact relation obligations and deduplicated actual updates

An open obligation is an incidence in one immutable presentation of exact
replay-anchored relation lineages.  The presentation is neither a mutable
registry nor a second ledger: every edge is regenerated from its fixed
lineage and one exact `ActualPly`.

Updates accept only source keys from that finite face.  Settlement and new
debt are calculated from the generated freedom comparison.  Repeated effects
for one incidence collapse in `Finset`; distinct incidences remain distinct.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace Obligation

universe u

/-- Stable incidence identity across one actual update.  New debt is tagged
separately from the source occurrence which generated it. -/
inductive ObligationKey (Incidence : Type u) where
  | open (incidence : Incidence)
  | generatedDebt (incidence : Incidence)
  deriving DecidableEq, Repr

namespace ObligationKey

def incidence {Incidence : Type u} : ObligationKey Incidence → Incidence
  | .open value => value
  | .generatedDebt value => value

end ObligationKey

/-- Finite source face of exact relation obligations at one actual replay.
Each incidence determines its horizon, transport law, marked relation, phase
state and exact lineage. -/
structure OpenRelationObligationFace {n : Nat} {law : Law}
    {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (Incidence : Type u) [DecidableEq Incidence] where
  incidences : Finset Incidence
  horizon : { incidence // incidence ∈ incidences } → Nat
  transport : { incidence // incidence ∈ incidences } →
    RelationTransportLaw n
  relation : { incidence // incidence ∈ incidences } → RelationProbe n
  state : { incidence // incidence ∈ incidences } → TacticalState
  lineage : ∀ key,
    RelationLineage (horizon key) (transport key) replay (relation key)
      (state key)

namespace OpenRelationObligationFace

abbrev SourceKey {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    (face : OpenRelationObligationFace replay Incidence) :=
  { incidence // incidence ∈ face.incidences }

/-- Source obligations as stable open tags. -/
def openKeys {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    (face : OpenRelationObligationFace replay Incidence) :
    Finset (ObligationKey Incidence) :=
  face.incidences.image ObligationKey.open

/-- The sole actual edge for one source incidence. -/
def edgeAt {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    (face : OpenRelationObligationFace replay Incidence)
    (ply : GeneratedReplay.ActualPly replay) (key : face.SourceKey) :
    RelationPhaseEdge (face.horizon key) (face.transport key) ply where
  sourceRelation := face.relation key
  sourceState := face.state key
  sourceLineage := face.lineage key

def targetLineageFor {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    (face : OpenRelationObligationFace replay Incidence)
    (ply : GeneratedReplay.ActualPly replay) (key : face.SourceKey) :=
  (face.edgeAt ply key).targetLineage

end OpenRelationObligationFace

/-- The unique compiler output for one source face and exact actual ply.
There are no caller-supplied effect, settlement, debt or target fields. -/
inductive GeneratedObligationUpdate {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    (face : OpenRelationObligationFace replay Incidence)
    (ply : GeneratedReplay.ActualPly replay) where
  | generated

namespace GeneratedObligationUpdate

def compile {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    (face : OpenRelationObligationFace replay Incidence)
    (ply : GeneratedReplay.ActualPly replay) :
    GeneratedObligationUpdate face ply :=
  .generated

/-- Every open source incidence is a major effect exactly once. -/
def majorEffects {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (_update : GeneratedObligationUpdate face ply) : Finset face.SourceKey :=
  face.incidences.attach

def effectSettles {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (_update : GeneratedObligationUpdate face ply) (key : face.SourceKey) : Bool :=
  decide ((face.edgeAt ply key).comparison = .grow)

def effectCreatesDebt {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (_update : GeneratedObligationUpdate face ply) (key : face.SourceKey) : Bool :=
  decide ((face.edgeAt ply key).comparison = .shrink)

/-- Deduplicated source obligations settled by strict freedom growth. -/
def settledKeys {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) :
    Finset (ObligationKey Incidence) :=
  (update.majorEffects.filter fun key => update.effectSettles key).image
    (fun key => ObligationKey.open key.1)

/-- Deduplicated new debts generated by strict freedom contraction. -/
def newDebtKeys {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) :
    Finset (ObligationKey Incidence) :=
  (update.majorEffects.filter fun key =>
    update.effectCreatesDebt key).image
      (fun key => ObligationKey.generatedDebt key.1)

/-- Exact target face generated by the update compiler. -/
def targetFace {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) :
    Finset (ObligationKey Incidence) :=
  (face.openKeys \ update.settledKeys) ∪ update.newDebtKeys

theorem targetFace_eq {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) :
    update.targetFace =
      (face.openKeys \ update.settledKeys) ∪ update.newDebtKeys :=
  rfl

theorem targetFace_complete_iff {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply)
    (key : ObligationKey Incidence) :
    key ∈ update.targetFace ↔
      (key ∈ face.openKeys ∧ key ∉ update.settledKeys) ∨
        key ∈ update.newDebtKeys := by
  simp [targetFace]

theorem majorEffect_mem_open {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply)
    (effect : face.SourceKey) (_member : effect ∈ update.majorEffects) :
    ObligationKey.open effect.1 ∈ face.openKeys := by
  exact Finset.mem_image.mpr ⟨effect.1, effect.2, rfl⟩

theorem settledKeys_subset_open {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) :
    update.settledKeys ⊆ face.openKeys := by
  intro key member
  rcases Finset.mem_image.mp member with ⟨effect, _member, keyEq⟩
  subst key
  exact Finset.mem_image.mpr ⟨effect.1, effect.2, rfl⟩

theorem open_mem_settledKeys_iff {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) (incidence : Incidence) :
    ObligationKey.open incidence ∈ update.settledKeys ↔
      ∃ key : face.SourceKey,
        key ∈ update.majorEffects ∧ key.1 = incidence ∧
          (face.edgeAt ply key).comparison = .grow := by
  constructor
  · intro member
    rcases Finset.mem_image.mp member with ⟨key, filtered, keyEq⟩
    have facts := Finset.mem_filter.mp filtered
    have listMember : key ∈ update.majorEffects := by simpa using facts.1
    have comparison : (face.edgeAt ply key).comparison = .grow := by
      exact of_decide_eq_true facts.2
    injection keyEq with incidenceEq
    exact ⟨key, listMember, incidenceEq, comparison⟩
  · rintro ⟨key, listMember, incidenceEq, comparison⟩
    apply Finset.mem_image.mpr
    refine ⟨key, Finset.mem_filter.mpr ⟨by simpa, ?_⟩, ?_⟩
    · exact decide_eq_true comparison
    · exact congrArg ObligationKey.open incidenceEq

theorem newDebtKeys_subset_targetFace {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) :
    update.newDebtKeys ⊆ update.targetFace := by
  intro key member
  exact Finset.mem_union_right _ member

theorem generatedDebt_mem_newDebtKeys_iff {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) (incidence : Incidence) :
    ObligationKey.generatedDebt incidence ∈ update.newDebtKeys ↔
      ∃ key : face.SourceKey,
        key ∈ update.majorEffects ∧ key.1 = incidence ∧
          (face.edgeAt ply key).comparison = .shrink := by
  constructor
  · intro member
    rcases Finset.mem_image.mp member with ⟨key, filtered, keyEq⟩
    have facts := Finset.mem_filter.mp filtered
    have listMember : key ∈ update.majorEffects := by simpa using facts.1
    have comparison : (face.edgeAt ply key).comparison = .shrink := by
      exact of_decide_eq_true facts.2
    injection keyEq with incidenceEq
    exact ⟨key, listMember, incidenceEq, comparison⟩
  · rintro ⟨key, listMember, incidenceEq, comparison⟩
    apply Finset.mem_image.mpr
    refine ⟨key, Finset.mem_filter.mpr ⟨by simpa, ?_⟩, ?_⟩
    · exact decide_eq_true comparison
    · exact congrArg ObligationKey.generatedDebt incidenceEq

theorem newDebtKeys_disjoint_open {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) :
    Disjoint update.newDebtKeys face.openKeys := by
  apply Finset.disjoint_left.mpr
  intro key newMember openMember
  rcases Finset.mem_image.mp newMember with ⟨newSource, _newMem, newEq⟩
  simp only [OpenRelationObligationFace.openKeys, Finset.mem_image] at openMember
  rcases openMember with ⟨openSource, _openMem, openEq⟩
  rw [← newEq] at openEq
  cases openEq

/-- Consumer-only projection of possibly repeated readouts.  It cannot alter
the authoritative update or target face. -/
def settledReadoutKeys {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply)
    (readouts : List face.SourceKey) : Finset (ObligationKey Incidence) :=
  (readouts.toFinset.filter fun key => update.effectSettles key).image
    (fun key => ObligationKey.open key.1)

def newDebtReadoutKeys {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply)
    (readouts : List face.SourceKey) : Finset (ObligationKey Incidence) :=
  (readouts.toFinset.filter fun key => update.effectCreatesDebt key).image
    (fun key => ObligationKey.generatedDebt key.1)

theorem majorEffect_complete {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) (key : face.SourceKey) :
    key ∈ update.majorEffects := by
  simp [majorEffects]

theorem settledReadoutKeys_duplicate {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply)
    (key : face.SourceKey) (rest : List face.SourceKey) :
    update.settledReadoutKeys (key :: key :: rest) =
      update.settledReadoutKeys (key :: rest) := by
  simp [settledReadoutKeys, effectSettles]

theorem newDebtReadoutKeys_duplicate {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply)
    (key : face.SourceKey) (rest : List face.SourceKey) :
    update.newDebtReadoutKeys (key :: key :: rest) =
      update.newDebtReadoutKeys (key :: rest) := by
  simp [newDebtReadoutKeys, effectCreatesDebt]

end GeneratedObligationUpdate

end Obligation
end Go
end ProcessGame
end SaturationMonoid
