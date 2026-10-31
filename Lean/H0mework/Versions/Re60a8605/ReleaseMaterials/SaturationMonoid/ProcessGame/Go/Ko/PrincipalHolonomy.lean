import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Ko.PhasePath
import H0mework.Realization.Descent.P260

/-!
# Principal holonomy of a projected Go loop

This module is the P259/P260 adapter for a lifted Go phase path.  Its three
indices distinguish the projected source, the exact lifted detour and the
projected return.  The detour transition carries the path's accumulated
`C4` phase, while the direct transition between projection-equal endpoints is
the identity.

The resulting transition family is deliberately not defined as the
difference of a potential on projected positions.  A nontrivial lifted phase
therefore produces P259 discrete holonomy and a P260 one-point topological
transition obstruction.  Exact potentials and the all-zero phase remain
flat negative controls.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace Ko

open AffineRelaxation

/-! ## Projected triangle adapter -/

/-- The P259 triangle: projected source, lifted detour, projected return. -/
inductive ProjectedLoopIndex where
  | source
  | lifted
  | returned
  deriving DecidableEq, Repr

/-- Transition cochain induced by one exact lifted phase product.  Only the
source-to-lifted edge carries that product.  The lifted-to-returned projection
identification and the source-to-returned direct projected edge are identity. -/
noncomputable def projectedLoopTransition (phaseProduct : TacticalPhase) :
    ProjectedLoopIndex → ProjectedLoopIndex → Circle
  | .source, .lifted => TacticalPhase.rotation phaseProduct
  | _, _ => 1

theorem projectedLoopTransition_source_lifted
    (phaseProduct : TacticalPhase) :
    projectedLoopTransition phaseProduct .source .lifted =
      TacticalPhase.rotation phaseProduct :=
  rfl

theorem projectedLoopTransition_lifted_returned
    (phaseProduct : TacticalPhase) :
    projectedLoopTransition phaseProduct .lifted .returned = 1 :=
  rfl

theorem projectedLoopTransition_source_returned
    (phaseProduct : TacticalPhase) :
    projectedLoopTransition phaseProduct .source .returned = 1 :=
  rfl

/-- P259 triangular holonomy is exactly the rotation accumulated by the
lifted path. -/
theorem projectedLoop_principalTriangleHolonomy_eq_rotation
    (phaseProduct : TacticalPhase) :
    principalTriangleHolonomy (projectedLoopTransition phaseProduct)
        .source .lifted .returned =
      TacticalPhase.rotation phaseProduct := by
  simp [principalTriangleHolonomy, projectedLoopTransition]

theorem projectedLoop_principalHolonomyObstruction
    {phaseProduct : TacticalPhase}
    (nontrivial : TacticalPhase.rotation phaseProduct ≠ 1) :
    PrincipalHolonomyObstruction
      (projectedLoopTransition phaseProduct) := by
  refine ⟨.source, .lifted, .returned, ?_⟩
  rw [projectedLoop_principalTriangleHolonomy_eq_rotation]
  exact nontrivial

/-- Direct P259 obstruction-to-non-flatness consumer. -/
theorem projectedLoop_not_flat
    {phaseProduct : TacticalPhase}
    (nontrivial : TacticalPhase.rotation phaseProduct ≠ 1) :
    ¬ FlatPrincipalConnection (projectedLoopTransition phaseProduct) :=
  (principalHolonomyObstruction_iff_not_flat
    (projectedLoopTransition phaseProduct)).mp
      (projectedLoop_principalHolonomyObstruction nontrivial)

/-! ## P259 transport mismatch -/

/-- P259 identifies the exact two-hop/direct mismatch with holonomy action. -/
theorem projectedLoop_transport_comp_eq_holonomy
    (phaseProduct : TacticalPhase) :
    principalTransport (projectedLoopTransition phaseProduct)
        .lifted .returned
        (principalTransport (projectedLoopTransition phaseProduct)
          .source .lifted (1 : Circle)) =
      principalTriangleHolonomy (projectedLoopTransition phaseProduct)
          .source .lifted .returned •
        principalTransport (projectedLoopTransition phaseProduct)
          .source .returned (1 : Circle) :=
  principalTransport_comp_eq_holonomy
    (projectedLoopTransition phaseProduct)
    .source .lifted .returned (1 : Circle)

/-- Nontrivial lifted phase makes two-hop transport differ from direct
projected transport. -/
theorem projectedLoop_transport_comp_mismatch
    {phaseProduct : TacticalPhase}
    (nontrivial : TacticalPhase.rotation phaseProduct ≠ 1) :
    principalTransport (projectedLoopTransition phaseProduct)
        .lifted .returned
        (principalTransport (projectedLoopTransition phaseProduct)
          .source .lifted (1 : Circle)) ≠
      principalTransport (projectedLoopTransition phaseProduct)
        .source .returned (1 : Circle) := by
  simpa [principalTransport, projectedLoopTransition] using nontrivial

/-! ## P260 topological consumer -/

/-- The minimal topological base needed to feed the same exact transition
family into P260.  Every chart covers the one base point. -/
def projectedLoopCover :
    TopologicalPrincipalCover Unit ProjectedLoopIndex where
  U := fun _ => Set.univ
  isOpen_U := fun _ => isOpen_univ
  covers := fun point => ⟨.source, Set.mem_univ point⟩

/-- The discrete Go transition cochain viewed as a constant transition
function over the one-point topological base. -/
noncomputable def topologicalProjectedLoopTransition
    (phaseProduct : TacticalPhase) :
    ProjectedLoopIndex → ProjectedLoopIndex → Unit → Circle :=
  fun first last _ => projectedLoopTransition phaseProduct first last

theorem topologicalProjectedLoopTransition_continuous
    (phaseProduct : TacticalPhase) :
    ContinuousOnPrincipalTransitions projectedLoopCover
      (topologicalProjectedLoopTransition phaseProduct) := by
  intro first last
  exact continuousOn_const

theorem unit_mem_projectedLoop_tripleOverlap :
    () ∈ projectedLoopCover.tripleOverlap
      ProjectedLoopIndex.source ProjectedLoopIndex.lifted
        ProjectedLoopIndex.returned := by
  simp [projectedLoopCover, TopologicalPrincipalCover.tripleOverlap]

/-- P260 pointwise holonomy is the same lifted rotation. -/
theorem topologicalProjectedLoop_holonomy_eq_rotation
    (phaseProduct : TacticalPhase) :
    topologicalPrincipalTriangleHolonomy
        (topologicalProjectedLoopTransition phaseProduct)
        .source .lifted .returned () =
      TacticalPhase.rotation phaseProduct := by
  simp [topologicalPrincipalTriangleHolonomy,
    topologicalProjectedLoopTransition, projectedLoopTransition]

theorem topologicalProjectedLoop_obstruction
    {phaseProduct : TacticalPhase}
    (nontrivial : TacticalPhase.rotation phaseProduct ≠ 1) :
    TopologicalPrincipalHolonomyObstruction projectedLoopCover
      (topologicalProjectedLoopTransition phaseProduct) := by
  refine ⟨.source, .lifted, .returned, (),
    unit_mem_projectedLoop_tripleOverlap, ?_⟩
  rw [topologicalProjectedLoop_holonomy_eq_rotation]
  exact nontrivial

/-- Direct P260 obstruction-to-non-flatness consumer. -/
theorem topologicalProjectedLoop_not_flat
    {phaseProduct : TacticalPhase}
    (nontrivial : TacticalPhase.rotation phaseProduct ≠ 1) :
    ¬ TopologicalPrincipalFlatOn projectedLoopCover
      (topologicalProjectedLoopTransition phaseProduct) :=
  (topologicalPrincipalHolonomyObstruction_iff_not_flat
    projectedLoopCover
    (topologicalProjectedLoopTransition phaseProduct)).mp
      (topologicalProjectedLoop_obstruction nontrivial)

/-- P260 identifies the topological two-hop/direct comparison with the same
pointwise holonomy action. -/
theorem topologicalProjectedLoop_transport_comp_eq_holonomy
    (phaseProduct : TacticalPhase) :
    topologicalPrincipalTransport
        (topologicalProjectedLoopTransition phaseProduct)
        .lifted .returned ()
        (topologicalPrincipalTransport
          (topologicalProjectedLoopTransition phaseProduct)
          .source .lifted () (1 : Circle)) =
      topologicalPrincipalTriangleHolonomy
          (topologicalProjectedLoopTransition phaseProduct)
          .source .lifted .returned () •
        topologicalPrincipalTransport
          (topologicalProjectedLoopTransition phaseProduct)
          .source .returned () (1 : Circle) :=
  topologicalPrincipalTransport_comp_eq_holonomy
    (topologicalProjectedLoopTransition phaseProduct)
    .source .lifted .returned () (1 : Circle)

/-- P260 transport-composition mismatch on the unique triple-overlap point. -/
theorem topologicalProjectedLoop_transport_comp_mismatch
    {phaseProduct : TacticalPhase}
    (nontrivial : TacticalPhase.rotation phaseProduct ≠ 1) :
    topologicalPrincipalTransport
        (topologicalProjectedLoopTransition phaseProduct)
        .lifted .returned ()
        (topologicalPrincipalTransport
          (topologicalProjectedLoopTransition phaseProduct)
          .source .lifted () (1 : Circle)) ≠
      topologicalPrincipalTransport
        (topologicalProjectedLoopTransition phaseProduct)
        .source .returned () (1 : Circle) := by
  simpa [topologicalPrincipalTransport,
    topologicalProjectedLoopTransition, projectedLoopTransition] using
      nontrivial

/-! ## Reachable Go ko principal holonomy -/

/-- P259 transition cochain generated by the exact four-edge ko phase path. -/
noncomputable def koPrincipalTransition (rule : RepetitionRule) :
    ProjectedLoopIndex → ProjectedLoopIndex → Circle :=
  projectedLoopTransition (koPhaseProduct rule)

/-- The P259 principal holonomy is exactly the rotation of the same exact
four-edge lineage product. -/
theorem koPrincipalTriangleHolonomy_eq_phaseRotation
    (rule : RepetitionRule) :
    principalTriangleHolonomy (koPrincipalTransition rule)
        .source .lifted .returned =
      TacticalPhase.rotation (koPhaseProduct rule) :=
  projectedLoop_principalTriangleHolonomy_eq_rotation _

theorem koPrincipalTriangleHolonomy_ne_one (rule : RepetitionRule) :
    principalTriangleHolonomy (koPrincipalTransition rule)
        .source .lifted .returned ≠ 1 := by
  rw [koPrincipalTriangleHolonomy_eq_phaseRotation]
  exact koPhaseRotation_ne_one rule

/-- Direct P259 principal obstruction on every supported repetition law. -/
theorem koPrincipalHolonomyObstruction (rule : RepetitionRule) :
    PrincipalHolonomyObstruction (koPrincipalTransition rule) :=
  projectedLoop_principalHolonomyObstruction
    (koPhaseRotation_ne_one rule)

theorem koPrincipalConnection_not_flat (rule : RepetitionRule) :
    ¬ FlatPrincipalConnection (koPrincipalTransition rule) :=
  projectedLoop_not_flat (koPhaseRotation_ne_one rule)

/-- The reachable ko cochain cannot be reconstructed as the difference of a
global potential on the projected indices. -/
theorem koPrincipalTransition_not_oneCoboundary
    (rule : RepetitionRule) :
    ¬ PrincipalOneCoboundary (koPrincipalTransition rule) := by
  intro exactPotential
  exact koPrincipalConnection_not_flat rule
    (principalOneCoboundary_flat
      (koPrincipalTransition rule) exactPotential)

/-- Direct P259 two-hop/direct transport mismatch. -/
theorem koPrincipalTransport_comp_mismatch (rule : RepetitionRule) :
    principalTransport (koPrincipalTransition rule)
        .lifted .returned
        (principalTransport (koPrincipalTransition rule)
          .source .lifted (1 : Circle)) ≠
      principalTransport (koPrincipalTransition rule)
        .source .returned (1 : Circle) :=
  projectedLoop_transport_comp_mismatch (koPhaseRotation_ne_one rule)

/-- The holonomy mouth retains both sides of the exact projection contract:
the local endpoints close, while board and occurrence history remain lifted
and distinct. -/
theorem koPrincipalHolonomy_has_exact_projectedLoop_provenance
    (rule : RepetitionRule) :
    KoReachableCycle.localProjection
          (KoReachableCycle.setupReplay rule).final =
        KoReachableCycle.localProjection
          (KoReachableCycle.cycleReplay rule).final ∧
      (generatedKoPhasePath rule).lineage =
        (recapturePhaseEdge rule).targetLineage ∧
      (KoReachableCycle.setupReplay rule).final.visible.board ≠
        (KoReachableCycle.cycleReplay rule).final.visible.board ∧
      (KoReachableCycle.setupReplay rule).final.positionHistory ≠
        (KoReachableCycle.cycleReplay rule).final.positionHistory ∧
      principalTriangleHolonomy (koPrincipalTransition rule)
          .source .lifted .returned ≠ 1 := by
  refine ⟨(koPhasePath_projects_to_reachable_loop rule).1,
    (koPhasePath_projects_to_reachable_loop rule).2.1,
    KoReachableCycle.global_board_ne rule,
    KoReachableCycle.lifted_history_ne rule, ?_⟩
  exact koPrincipalTriangleHolonomy_ne_one rule

/-- P260 transition family generated by the same exact ko phase path. -/
noncomputable def topologicalKoPrincipalTransition
    (rule : RepetitionRule) :
    ProjectedLoopIndex → ProjectedLoopIndex → Unit → Circle :=
  topologicalProjectedLoopTransition (koPhaseProduct rule)

theorem topologicalKoPrincipalTransition_continuous
    (rule : RepetitionRule) :
    ContinuousOnPrincipalTransitions projectedLoopCover
      (topologicalKoPrincipalTransition rule) :=
  topologicalProjectedLoopTransition_continuous _

theorem topologicalKoPrincipalHolonomyObstruction
    (rule : RepetitionRule) :
    TopologicalPrincipalHolonomyObstruction projectedLoopCover
      (topologicalKoPrincipalTransition rule) :=
  topologicalProjectedLoop_obstruction (koPhaseRotation_ne_one rule)

/-- Direct P260 non-flatness consumer. -/
theorem topologicalKoPrincipal_not_flat (rule : RepetitionRule) :
    ¬ TopologicalPrincipalFlatOn projectedLoopCover
      (topologicalKoPrincipalTransition rule) :=
  topologicalProjectedLoop_not_flat (koPhaseRotation_ne_one rule)

/-- Nor can the exact topological transition family be a projected local
potential difference. -/
theorem topologicalKoPrincipal_not_exactTransition
    (rule : RepetitionRule) :
    ¬ ∃ potential : ProjectedLoopIndex → Unit → Circle,
      topologicalKoPrincipalTransition rule =
        topologicalPrincipalExactTransition potential := by
  rintro ⟨potential, exactEq⟩
  have exactFlat :=
    topologicalPrincipalExactTransition_flatOn
      projectedLoopCover potential
  apply topologicalKoPrincipal_not_flat rule
  simpa [exactEq] using exactFlat

theorem topologicalKoPrincipal_transport_comp_mismatch
    (rule : RepetitionRule) :
    topologicalPrincipalTransport (topologicalKoPrincipalTransition rule)
        .lifted .returned ()
        (topologicalPrincipalTransport (topologicalKoPrincipalTransition rule)
          .source .lifted () (1 : Circle)) ≠
      topologicalPrincipalTransport (topologicalKoPrincipalTransition rule)
        .source .returned () (1 : Circle) :=
  topologicalProjectedLoop_transport_comp_mismatch
    (koPhaseRotation_ne_one rule)

/-! ## Exact and zero-phase negative controls -/

/-- Any transition cochain generated from a projected potential has trivial
P259 holonomy. -/
theorem projectedExactPotential_holonomy_one
    (potential : ProjectedLoopIndex → Circle) :
    principalTriangleHolonomy (principalExactTransition potential)
        .source .lifted .returned = 1 :=
  principalExactTransition_holonomy_one potential
    .source .lifted .returned

theorem projectedExactPotential_not_obstruction
    (potential : ProjectedLoopIndex → Circle) :
    ¬ PrincipalHolonomyObstruction
      (principalExactTransition potential) :=
  principalOneCoboundary_not_obstruction
    (principalExactTransition potential)
    (principalExactTransition_oneCoboundary potential)

theorem projectedLoop_zero_holonomy_one :
    principalTriangleHolonomy (projectedLoopTransition 0)
        .source .lifted .returned = 1 := by
  rw [projectedLoop_principalTriangleHolonomy_eq_rotation]
  exact TacticalPhase.rotation_zero

theorem projectedLoop_zero_not_obstruction :
    ¬ PrincipalHolonomyObstruction (projectedLoopTransition 0) := by
  intro obstruction
  have notFlat :=
    (principalHolonomyObstruction_iff_not_flat
      (projectedLoopTransition 0)).mp obstruction
  apply notFlat
  intro first middle last
  cases first <;> cases middle <;> cases last <;>
    simp [projectedLoopTransition, TacticalPhase.rotation_zero]

theorem topologicalProjectedLoop_zero_holonomy_one :
    topologicalPrincipalTriangleHolonomy
        (topologicalProjectedLoopTransition 0)
        .source .lifted .returned () = 1 := by
  rw [topologicalProjectedLoop_holonomy_eq_rotation]
  exact TacticalPhase.rotation_zero

theorem topologicalProjectedLoop_zero_not_obstruction :
    ¬ TopologicalPrincipalHolonomyObstruction projectedLoopCover
      (topologicalProjectedLoopTransition 0) := by
  intro obstruction
  have notFlat :=
    (topologicalPrincipalHolonomyObstruction_iff_not_flat
      projectedLoopCover
      (topologicalProjectedLoopTransition 0)).mp obstruction
  apply notFlat
  intro first middle last point _pointMem
  cases first <;> cases middle <;> cases last <;>
    simp [topologicalProjectedLoopTransition, projectedLoopTransition,
      TacticalPhase.rotation_zero]

/-- P260 exact-potential transitions remain obstruction-free on the same
topological cover. -/
theorem topologicalProjectedExactPotential_not_obstruction
    (potential : ProjectedLoopIndex → Unit → Circle) :
    ¬ TopologicalPrincipalHolonomyObstruction projectedLoopCover
      (topologicalPrincipalExactTransition potential) :=
  topologicalPrincipalExactTransition_not_obstruction
    projectedLoopCover potential

end Ko
end Go
end ProcessGame
end SaturationMonoid
