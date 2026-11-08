import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.FutureFreedom
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.TacticalPhaseAlgebra

/-!
# Relation-generated tactical phase on exact Go plies

This module turns changes of the finite future-freedom fibre into a local
four-phase connection.  A phase edge is indexed by an exact `ActualPly` and a
replay-anchored marked-relation lineage.  Relation transport computes its
target probe; callers cannot submit a target relation, phase, tactical role or
constraint owner.

The phase attached to an edge is the difference between the generated source
and target tactical states.  It is deliberately not the difference of a
global function on `Frame`: two lifted edges with equal visible endpoints may
still carry different relation lineages and phase steps.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

/-! ## Total comparison on the common bounded move-word carrier -/

/-- The exhaustive relation between two finite freedom fibres. -/
inductive FreedomComparison where
  | equal
  | shrink
  | grow
  | incomparable
  deriving DecidableEq, Repr

/-- Total deterministic comparison.  The two strict directions use the
source-fixed `StrictFreedomSubset`; the final branch is genuine
incomparability, not an unverified remainder. -/
def compareFreedom {n : Nat}
    (before after : Finset (List (Move n))) : FreedomComparison :=
  if before = after then
    .equal
  else if after ⊆ before then
    .shrink
  else if before ⊆ after then
    .grow
  else
    .incomparable

theorem strictFreedomSubset_iff_subset_ne {n : Nat}
    {left right : Finset (List (Move n))} :
    StrictFreedomSubset left right ↔ left ⊆ right ∧ left ≠ right := by
  constructor
  · rintro ⟨subset, word, wordRight, wordNotLeft⟩
    refine ⟨subset, ?_⟩
    intro equal
    subst right
    exact wordNotLeft wordRight
  · rintro ⟨subset, different⟩
    exact ⟨subset,
      (Finset.ssubset_iff_of_subset subset).mp
        ((Finset.ssubset_iff_subset_ne).mpr ⟨subset, different⟩)⟩

theorem compareFreedom_eq_equal_iff {n : Nat}
    (before after : Finset (List (Move n))) :
    compareFreedom before after = .equal ↔ before = after := by
  constructor
  · intro classified
    unfold compareFreedom at classified
    split at classified
    · assumption
    · split at classified
      · cases classified
      · split at classified <;> cases classified
  · rintro rfl
    simp [compareFreedom]

theorem compareFreedom_eq_shrink_iff {n : Nat}
    (before after : Finset (List (Move n))) :
    compareFreedom before after = .shrink ↔
      StrictFreedomSubset after before := by
  constructor
  · intro classified
    unfold compareFreedom at classified
    split at classified
    · cases classified
    · rename_i different
      split at classified
      · rename_i subset
        exact strictFreedomSubset_iff_subset_ne.mpr
          ⟨subset, fun reverse => different reverse.symm⟩
      · split at classified <;> cases classified
  · intro shrinks
    have facts := strictFreedomSubset_iff_subset_ne.mp shrinks
    have different : before ≠ after := fun equal => facts.2 equal.symm
    simp [compareFreedom, different, facts.1]

theorem strictFreedomSubset_asymm {n : Nat}
    {left right : Finset (List (Move n))}
    (leftRight : StrictFreedomSubset left right) :
    ¬ StrictFreedomSubset right left := by
  rintro ⟨rightLeft, word, wordLeft, wordNotRight⟩
  exact wordNotRight (leftRight.1 wordLeft)

theorem compareFreedom_eq_grow_iff {n : Nat}
    (before after : Finset (List (Move n))) :
    compareFreedom before after = .grow ↔
      StrictFreedomSubset before after := by
  constructor
  · intro classified
    unfold compareFreedom at classified
    split at classified
    · cases classified
    · rename_i different
      split at classified
      · cases classified
      · rename_i notAfterSubset
        split at classified
        · rename_i beforeSubset
          exact strictFreedomSubset_iff_subset_ne.mpr
            ⟨beforeSubset, different⟩
        · cases classified
  · intro grows
    have facts := strictFreedomSubset_iff_subset_ne.mp grows
    have notAfterSubset : ¬ after ⊆ before := by
      intro afterSubset
      exact facts.2 (Finset.Subset.antisymm facts.1 afterSubset)
    simp [compareFreedom, facts.2, notAfterSubset, facts.1]

theorem compareFreedom_eq_incomparable_iff {n : Nat}
    (before after : Finset (List (Move n))) :
    compareFreedom before after = .incomparable ↔
      before ≠ after ∧
      ¬ StrictFreedomSubset after before ∧
      ¬ StrictFreedomSubset before after := by
  constructor
  · intro classified
    unfold compareFreedom at classified
    split at classified
    · cases classified
    · rename_i different
      split at classified
      · cases classified
      · rename_i notAfterSubset
        split at classified
        · cases classified
        · rename_i notBeforeSubset
          refine ⟨different, ?_, ?_⟩
          · intro shrinks
            exact notAfterSubset
              (strictFreedomSubset_iff_subset_ne.mp shrinks).1
          · intro grows
            exact notBeforeSubset
              (strictFreedomSubset_iff_subset_ne.mp grows).1
  · rintro ⟨different, notShrinks, notGrows⟩
    have notAfterSubset : ¬ after ⊆ before := by
      intro subset
      apply notShrinks
      exact strictFreedomSubset_iff_subset_ne.mpr
        ⟨subset, fun reverse => different reverse.symm⟩
    have notBeforeSubset : ¬ before ⊆ after := by
      intro subset
      apply notGrows
      exact strictFreedomSubset_iff_subset_ne.mpr ⟨subset, different⟩
    simp [compareFreedom, different, notAfterSubset, notBeforeSubset]

/-! ## Four absolute states and local `C4` transitions -/

/-- Absolute positions in a typed tactical exchange. -/
inductive TacticalState where
  | impose
  | receive
  | redirect
  | reverse
  deriving DecidableEq, Repr

namespace TacticalState

/-- Canonical state coordinate in `C4`.  This is not itself an edge phase. -/
def code : TacticalState → TacticalPhase
  | .impose => 0
  | .receive => 1
  | .redirect => 2
  | .reverse => 3

theorem code_injective : Function.Injective code := by
  intro left right
  cases left <;> cases right <;> decide

/-- The local cochain value carried by a transition. -/
def transition (source target : TacticalState) : TacticalPhase :=
  code target - code source

@[simp] theorem transition_self (state : TacticalState) :
    transition state state = 0 := by
  simp [transition]

theorem transition_eq_zero_iff (source target : TacticalState) :
    transition source target = 0 ↔ source = target := by
  constructor
  · intro zero
    apply code_injective
    have := sub_eq_zero.mp zero
    exact this.symm
  · rintro rfl
    exact transition_self source

/-- Chronological composition: first `source → middle`, then
`middle → target`.  The later edge is the left factor, matching the
transition convention consumed by the holonomy layer. -/
theorem transition_compose (source middle target : TacticalState) :
    TacticalPhase.compose (transition middle target)
        (transition source middle) =
      transition source target := by
  simp [TacticalPhase.compose, transition]

end TacticalState

/-! ## Fixed relation transport and generated phase update -/

/-- A fixed transport law either retains the exact marked relation occurrence
or advances to the source-turn relation generated by the exact actual child.
There is deliberately no constructor carrying a free target probe. -/
inductive RelationTransportResult {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay)
    (source : RelationProbe n) where
  | retained
  | advanceTurn

namespace RelationTransportResult

def target {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {ply : GeneratedReplay.ActualPly replay}
    {source : RelationProbe n} :
    RelationTransportResult ply source → RelationProbe n
  | .retained => source
  | .advanceTurn => sourceTurnRelationAt ply.extended

def wasTransferred {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {ply : GeneratedReplay.ActualPly replay}
    {source : RelationProbe n} :
    RelationTransportResult ply source → Bool
  | .retained => false
  | .advanceTurn => true

end RelationTransportResult

/-- Closed source-fixed relation transport.  G4 exposes only identity
retention and the exact actual-child turn compiler; arbitrary target
functions are not representable. -/
inductive RelationTransportLaw (n : Nat) where
  | keep
  | turn
  deriving DecidableEq, Repr

namespace RelationTransportLaw

/-- The fixed no-conversion law. -/
def retain (n : Nat) : RelationTransportLaw n :=
  .keep

/-- Exact source-generated conversion: the target relation is compiled from
the actual child replay and cannot be supplied by the caller. -/
def advanceTurn (n : Nat) : RelationTransportLaw n :=
  .turn

def result {n : Nat} (transport : RelationTransportLaw n)
    {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay)
    (source : RelationProbe n) : RelationTransportResult ply source :=
  match transport with
  | .keep => .retained
  | .turn => .advanceTurn

/-- The exact relation occurrences eligible for one fixed transport law. -/
def EligibleAt {n : Nat} (transport : RelationTransportLaw n)
    {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (relation : RelationProbe n) : Prop :=
  match transport with
  | .keep => True
  | .turn => relation = sourceTurnRelationAt replay

theorem target_eligible {n : Nat} (transport : RelationTransportLaw n)
    {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay) (source : RelationProbe n) :
    EligibleAt transport ply.extended
      (transport.result ply source).target := by
  cases transport <;> trivial

end RelationTransportLaw

/-- Exact before/after comparison after applying the fixed relation transport
law to the exact actual edge. -/
def relationComparisonAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay) (horizon : Nat)
    (transport : RelationTransportLaw n) (source : RelationProbe n) :
    FreedomComparison :=
  compareFreedom
    (relationFreedom replay horizon source)
    (relationFreedom ply.extended horizon
      (transport.result ply source).target)

theorem relationComparisonAt_retain_eq_shrink_iff {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay) (horizon : Nat)
    (relation : RelationProbe n) :
    relationComparisonAt ply horizon (RelationTransportLaw.retain n)
        relation = .shrink ↔
      FreedomShrinksAt ply horizon relation := by
  exact compareFreedom_eq_shrink_iff _ _

theorem relationComparisonAt_retain_eq_grow_iff {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay) (horizon : Nat)
    (relation : RelationProbe n) :
    relationComparisonAt ply horizon (RelationTransportLaw.retain n)
        relation = .grow ↔
      FreedomGrowsAt ply horizon relation := by
  exact compareFreedom_eq_grow_iff _ _

/-- The local `C4` increment generated by total comparison of the exact
freedom fibres. -/
def freedomPhaseStep : FreedomComparison → TacticalPhase
  | .equal => 0
  | .shrink => 1
  | .incomparable => 2
  | .grow => 3

/-- The generated action of a freedom comparison on an absolute tactical
state.  A strict shrink advances one quarter-turn, so repeated pressure runs
through `impose → receive → redirect → reverse → impose`.
Growth is the inverse quarter-turn; incomparability is the half-turn. -/
def advanceStateByComparison (sourceState : TacticalState)
    (comparison : FreedomComparison) : TacticalState :=
  match comparison, sourceState with
  | .equal, state => state
  | .shrink, .impose => .receive
  | .shrink, .receive => .redirect
  | .shrink, .redirect => .reverse
  | .shrink, .reverse => .impose
  | .incomparable, .impose => .redirect
  | .incomparable, .receive => .reverse
  | .incomparable, .redirect => .impose
  | .incomparable, .reverse => .receive
  | .grow, .impose => .reverse
  | .grow, .receive => .impose
  | .grow, .redirect => .receive
  | .grow, .reverse => .redirect

theorem transition_advanceStateByComparison (sourceState : TacticalState)
    (comparison : FreedomComparison) :
    TacticalState.transition sourceState
        (advanceStateByComparison sourceState comparison) =
      freedomPhaseStep comparison := by
  cases sourceState <;> cases comparison <;>
    decide

/-- Exact relation transport contributes its own half-turn even when the
extensional freedom fibres happen to be equal. -/
def relationPhaseStep {n : Nat} (transport : RelationTransportLaw n)
    (comparison : FreedomComparison) : TacticalPhase :=
  match transport with
  | .keep => freedomPhaseStep comparison
  | .turn => 2

def generatedTargetState {n : Nat} (transport : RelationTransportLaw n)
    (sourceState : TacticalState) (comparison : FreedomComparison) :
    TacticalState :=
  match transport with
  | .keep => advanceStateByComparison sourceState comparison
  | .turn => advanceStateByComparison sourceState .incomparable

theorem transition_generatedTargetState {n : Nat}
    (transport : RelationTransportLaw n) (sourceState : TacticalState)
    (comparison : FreedomComparison) :
    TacticalState.transition sourceState
        (generatedTargetState transport sourceState comparison) =
      relationPhaseStep transport comparison := by
  cases transport with
  | keep => exact transition_advanceStateByComparison sourceState comparison
  | turn =>
      simpa [generatedTargetState, relationPhaseStep, freedomPhaseStep] using
        transition_advanceStateByComparison sourceState .incomparable

/-- Constraint-bearer transport is a generated disposition, not a pair of
caller-supplied owners. -/
inductive ConstraintBearerDisposition where
  | retained
  | handoff
  deriving DecidableEq, Repr

def generatedBearerDisposition {n : Nat}
    (transport : RelationTransportLaw n) :
    FreedomComparison → ConstraintBearerDisposition
  | .equal => match transport with
      | .keep => .retained
      | .turn => .handoff
  | .shrink => .handoff
  | .grow => .handoff
  | .incomparable => .handoff

/-! ## Replay-anchored relation lineage -/

/-- A marked relation lineage is anchored in one generated actual replay.
The marked relation is an external mathematical object, as required by the
memo's "for marked `R`" mouth; its phase and every later target relation are
generated here.  The inductive spine is a proof of exact transport, not a
registry or second ledger. -/
inductive RelationLineage {n : Nat} {law : Law}
    (horizon : Nat) (transport : RelationTransportLaw n) :
    {moves : List (Move n)} →
    (replay : GeneratedReplay law (Frame.initial n) moves) →
    RelationProbe n → TacticalState → Type where
  | marked {moves : List (Move n)}
      (replay : GeneratedReplay law (Frame.initial n) moves)
      (relation : RelationProbe n)
      (eligible : RelationTransportLaw.EligibleAt transport replay relation) :
      RelationLineage horizon transport replay relation .impose
  | advance {moves : List (Move n)}
      {replay : GeneratedReplay law (Frame.initial n) moves}
      {source : RelationProbe n} {sourceState : TacticalState}
      (lineage : RelationLineage horizon transport replay source sourceState)
      (ply : GeneratedReplay.ActualPly replay) :
      RelationLineage horizon transport ply.extended
        (transport.result ply source).target
        (generatedTargetState transport sourceState
          (relationComparisonAt ply horizon transport source))

/-- Every public lineage occurrence carries the fixed law's exact eligibility;
an actual advance regenerates it for the compiler-produced target relation. -/
theorem RelationLineage.eligible {n : Nat} {law : Law}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {relation : RelationProbe n} {state : TacticalState}
    (lineage : RelationLineage horizon transport replay relation state) :
    RelationTransportLaw.EligibleAt transport replay relation := by
  cases lineage with
  | marked _ _ eligible => exact eligible
  | @advance _ _ source _ _ ply =>
      exact RelationTransportLaw.target_eligible transport ply source

/-- One public local phase edge.  Its target relation, target state and target
lineage are all calculated from its exact source lineage and actual ply. -/
structure RelationPhaseEdge {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (horizon : Nat) (transport : RelationTransportLaw n)
    (ply : GeneratedReplay.ActualPly replay) where
  sourceRelation : RelationProbe n
  sourceState : TacticalState
  sourceLineage : RelationLineage horizon transport replay sourceRelation
    sourceState

namespace RelationPhaseEdge

def transportResult {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply) :
    RelationTransportResult ply edge.sourceRelation :=
  transport.result ply edge.sourceRelation

def targetRelation {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply) : RelationProbe n :=
  edge.transportResult.target

def comparison {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply) : FreedomComparison :=
  relationComparisonAt ply horizon transport edge.sourceRelation

def targetState {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply) : TacticalState :=
  generatedTargetState transport edge.sourceState edge.comparison

/-- The edge-local `C4` cochain. -/
def phaseStep {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply) : TacticalPhase :=
  TacticalState.transition edge.sourceState edge.targetState

def targetLineage {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply) :
    RelationLineage horizon transport ply.extended edge.targetRelation
      edge.targetState :=
  .advance edge.sourceLineage ply

def bearerDisposition {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply) :
    ConstraintBearerDisposition :=
  generatedBearerDisposition transport edge.comparison

/-- Phase state is total and unique on every exact public edge, including
equal and incomparable freedom pairs. -/
theorem targetState_total_unique {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {ply : GeneratedReplay.ActualPly replay}
    (edge : RelationPhaseEdge horizon transport ply) :
    ∃! state : TacticalState, state = edge.targetState := by
  exact ⟨edge.targetState, rfl, fun candidate equal => equal⟩

end RelationPhaseEdge

/-! ## Exact phase-run composition for the G5 consumer -/

/-- Accumulated local connection along an exact relation lineage.  The later
edge is composed on the left.  No phase is reconstructed from a `Frame`
potential. -/
def RelationLineage.phaseProduct {n : Nat} {law : Law}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {relation : RelationProbe n} {state : TacticalState}
    (lineage : RelationLineage horizon transport replay relation state) :
    TacticalPhase :=
  match lineage with
  | .marked _ _ _ => 0
  | @RelationLineage.advance _ _ _ _ _ _ source sourceState prior ply =>
      let comparison := relationComparisonAt ply horizon transport source
      let targetState := generatedTargetState transport sourceState comparison
      TacticalPhase.compose
        (TacticalState.transition sourceState targetState)
        prior.phaseProduct

@[simp] theorem RelationLineage.phaseProduct_marked {n : Nat} {law : Law}
    {horizon : Nat} {transport : RelationTransportLaw n}
    {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (relation : RelationProbe n)
    (eligible : RelationTransportLaw.EligibleAt transport replay relation) :
    (RelationLineage.marked (horizon := horizon) (transport := transport)
      replay relation eligible).phaseProduct = 0 :=
  rfl

end Go
end ProcessGame
end SaturationMonoid
