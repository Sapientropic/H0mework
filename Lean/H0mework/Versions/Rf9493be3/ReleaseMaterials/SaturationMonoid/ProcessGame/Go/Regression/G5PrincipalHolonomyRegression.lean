import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Ko.PrincipalHolonomy

/-!
# G5 principal-holonomy regression

The same exact four-ply ko phase path drives the P259 discrete and P260
topological transition families under simple ko, positional superko and
situational superko.  The local projection closes, but its lifted phase
product is `1 : C4`, so the principal holonomy is the nonidentity rotation
`i`.  Exact projected potentials and the all-zero phase are strict negative
controls.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G5PrincipalHolonomyRegression

open AffineRelaxation Ko KoReachableCycle

/-! ## Exact lifted-path provenance -/

theorem positional_projected_loop_keeps_lifted_difference :
    localProjection (setupReplay .positionalSuperko).final =
        localProjection (cycleReplay .positionalSuperko).final ∧
      (setupReplay .positionalSuperko).final.visible.board ≠
        (cycleReplay .positionalSuperko).final.visible.board ∧
      (setupReplay .positionalSuperko).final.positionHistory ≠
        (cycleReplay .positionalSuperko).final.positionHistory ∧
      koPhaseProduct .positionalSuperko = 1 ∧
      principalTriangleHolonomy
          (koPrincipalTransition .positionalSuperko)
          .source .lifted .returned ≠ 1 := by
  have provenance :=
    koPrincipalHolonomy_has_exact_projectedLoop_provenance
      .positionalSuperko
  exact ⟨provenance.1, provenance.2.2.1, provenance.2.2.2.1,
    koPhaseProduct_eq_one .positionalSuperko, provenance.2.2.2.2⟩

/-- The concrete holonomy is the quarter-turn `i`, not merely an abstract
nonidentity element. -/
theorem positional_principal_holonomy_is_i :
    ((principalTriangleHolonomy
      (koPrincipalTransition .positionalSuperko)
      .source .lifted .returned : Circle) : ℂ) = Complex.I := by
  rw [koPrincipalTriangleHolonomy_eq_phaseRotation,
    koPhaseProduct_eq_one]
  exact TacticalPhase.rotation_one_complex

/-! ## P259 direct consumers -/

theorem all_three_repetition_laws_have_principal_obstruction :
    PrincipalHolonomyObstruction
        (koPrincipalTransition .simpleKo) ∧
      PrincipalHolonomyObstruction
        (koPrincipalTransition .positionalSuperko) ∧
      PrincipalHolonomyObstruction
        (koPrincipalTransition .situationalSuperko) :=
  ⟨koPrincipalHolonomyObstruction .simpleKo,
    koPrincipalHolonomyObstruction .positionalSuperko,
    koPrincipalHolonomyObstruction .situationalSuperko⟩

theorem all_three_repetition_laws_are_nonflat :
    ¬ FlatPrincipalConnection (koPrincipalTransition .simpleKo) ∧
      ¬ FlatPrincipalConnection
        (koPrincipalTransition .positionalSuperko) ∧
      ¬ FlatPrincipalConnection
        (koPrincipalTransition .situationalSuperko) :=
  ⟨koPrincipalConnection_not_flat .simpleKo,
    koPrincipalConnection_not_flat .positionalSuperko,
    koPrincipalConnection_not_flat .situationalSuperko⟩

theorem positional_cochain_is_not_a_projected_potential_difference :
    ¬ PrincipalOneCoboundary
        (koPrincipalTransition .positionalSuperko) ∧
      ¬ ∃ potential : ProjectedLoopIndex → Unit → Circle,
        topologicalKoPrincipalTransition .positionalSuperko =
          topologicalPrincipalExactTransition potential :=
  ⟨koPrincipalTransition_not_oneCoboundary .positionalSuperko,
    topologicalKoPrincipal_not_exactTransition .positionalSuperko⟩

/-- The named P259 factorization theorem is consumed before asserting the
strict transport mismatch. -/
theorem positional_transport_factor_and_mismatch :
    principalTransport (koPrincipalTransition .positionalSuperko)
        .lifted .returned
        (principalTransport (koPrincipalTransition .positionalSuperko)
          .source .lifted (1 : Circle)) =
      principalTriangleHolonomy
          (koPrincipalTransition .positionalSuperko)
          .source .lifted .returned •
        principalTransport (koPrincipalTransition .positionalSuperko)
          .source .returned (1 : Circle) ∧
      principalTransport (koPrincipalTransition .positionalSuperko)
          .lifted .returned
          (principalTransport (koPrincipalTransition .positionalSuperko)
            .source .lifted (1 : Circle)) ≠
        principalTransport (koPrincipalTransition .positionalSuperko)
          .source .returned (1 : Circle) :=
  ⟨projectedLoop_transport_comp_eq_holonomy
      (koPhaseProduct .positionalSuperko),
    koPrincipalTransport_comp_mismatch .positionalSuperko⟩

/-! ## P260 direct consumers -/

theorem positional_topological_transition_is_continuous_and_obstructed :
    ContinuousOnPrincipalTransitions projectedLoopCover
        (topologicalKoPrincipalTransition .positionalSuperko) ∧
      TopologicalPrincipalHolonomyObstruction projectedLoopCover
        (topologicalKoPrincipalTransition .positionalSuperko) ∧
      ¬ TopologicalPrincipalFlatOn projectedLoopCover
        (topologicalKoPrincipalTransition .positionalSuperko) :=
  ⟨topologicalKoPrincipalTransition_continuous .positionalSuperko,
    topologicalKoPrincipalHolonomyObstruction .positionalSuperko,
    topologicalKoPrincipal_not_flat .positionalSuperko⟩

theorem all_three_topological_obstructions :
    TopologicalPrincipalHolonomyObstruction projectedLoopCover
        (topologicalKoPrincipalTransition .simpleKo) ∧
      TopologicalPrincipalHolonomyObstruction projectedLoopCover
        (topologicalKoPrincipalTransition .positionalSuperko) ∧
      TopologicalPrincipalHolonomyObstruction projectedLoopCover
        (topologicalKoPrincipalTransition .situationalSuperko) :=
  ⟨topologicalKoPrincipalHolonomyObstruction .simpleKo,
    topologicalKoPrincipalHolonomyObstruction .positionalSuperko,
    topologicalKoPrincipalHolonomyObstruction .situationalSuperko⟩

theorem positional_topological_transport_factor_and_mismatch :
    topologicalPrincipalTransport
        (topologicalKoPrincipalTransition .positionalSuperko)
        .lifted .returned ()
        (topologicalPrincipalTransport
          (topologicalKoPrincipalTransition .positionalSuperko)
          .source .lifted () (1 : Circle)) =
      topologicalPrincipalTriangleHolonomy
          (topologicalKoPrincipalTransition .positionalSuperko)
          .source .lifted .returned () •
        topologicalPrincipalTransport
          (topologicalKoPrincipalTransition .positionalSuperko)
          .source .returned () (1 : Circle) ∧
      topologicalPrincipalTransport
          (topologicalKoPrincipalTransition .positionalSuperko)
          .lifted .returned ()
          (topologicalPrincipalTransport
            (topologicalKoPrincipalTransition .positionalSuperko)
            .source .lifted () (1 : Circle)) ≠
        topologicalPrincipalTransport
          (topologicalKoPrincipalTransition .positionalSuperko)
          .source .returned () (1 : Circle) :=
  ⟨topologicalProjectedLoop_transport_comp_eq_holonomy
      (koPhaseProduct .positionalSuperko),
    topologicalKoPrincipal_transport_comp_mismatch .positionalSuperko⟩

/-! ## Exact-potential and zero-phase negative controls -/

noncomputable def exactPotential : ProjectedLoopIndex → Circle
  | .source => 1
  | .lifted => TacticalPhase.rotation 1
  | .returned => TacticalPhase.rotation 2

theorem exact_potential_is_flat_and_holonomy_trivial :
    FlatPrincipalConnection (principalExactTransition exactPotential) ∧
      principalTriangleHolonomy (principalExactTransition exactPotential)
          .source .lifted .returned = 1 ∧
      ¬ PrincipalHolonomyObstruction
        (principalExactTransition exactPotential) :=
  ⟨principalExactTransition_flat exactPotential,
    projectedExactPotential_holonomy_one exactPotential,
    projectedExactPotential_not_obstruction exactPotential⟩

theorem all_zero_phase_is_trivial :
    principalTriangleHolonomy (projectedLoopTransition 0)
        .source .lifted .returned = 1 ∧
      ¬ PrincipalHolonomyObstruction (projectedLoopTransition 0) ∧
      topologicalPrincipalTriangleHolonomy
          (topologicalProjectedLoopTransition 0)
          .source .lifted .returned () = 1 ∧
      ¬ TopologicalPrincipalHolonomyObstruction projectedLoopCover
        (topologicalProjectedLoopTransition 0) :=
  ⟨projectedLoop_zero_holonomy_one,
    projectedLoop_zero_not_obstruction,
    topologicalProjectedLoop_zero_holonomy_one,
    topologicalProjectedLoop_zero_not_obstruction⟩

noncomputable def exactTopologicalPotential :
    ProjectedLoopIndex → Unit → Circle :=
  fun index _ => exactPotential index

theorem exact_topological_potential_has_no_obstruction :
    ¬ TopologicalPrincipalHolonomyObstruction projectedLoopCover
      (topologicalPrincipalExactTransition exactTopologicalPotential) :=
  topologicalProjectedExactPotential_not_obstruction exactTopologicalPotential

end G5PrincipalHolonomyRegression
end Go
end ProcessGame
end SaturationMonoid
