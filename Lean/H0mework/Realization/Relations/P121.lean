/-
  Proposition 121: residual magnitude descends to the cohomology quotient.

  Proposition 117 proves that the three-agent ring residual magnitude is zero
  exactly on selected-edge exact cochains.  This file proves the missing
  quotient-facing law: adding a 0-coboundary does not change the residual, hence
  does not change its integer magnitude.

  This is the purely mathematical part of the "memory strength" slogan.  The
  magnitude is a cohomological obstruction magnitude: it measures the selected
  ring's distance from being globally potential-explainable in the only sense
  currently formalized here, namely a residual invariant on cohomology classes.
  Product-level or cognitive "strength" remains a modeling bridge.
-/

import H0mework.Realization.CyclicMemory.P117

/-! ## Cohomology relation on the three-agent ring -/

/-- Two three-agent ring cochains are cohomologous when they differ by a
0-coboundary on the identity-pair / zero-triple cover. -/
def ThreeAgentRingCohomologous
    {A : Type*} [AddCommGroup A]
    (c d : ThreeCycleTime -> ThreeCycleTime -> A) : Prop :=
  exists s : ThreeCycleTime -> A,
    d = fun i j =>
      c i j +
        CechAdditiveCover.d0
          (identityPairZeroTripleCover ThreeCycleTime A) s i j

/-- THEOREM 1: cohomology by 0-coboundary is reflexive. -/
theorem threeAgentRingCohomologous_refl
    {A : Type*} [AddCommGroup A]
    (c : ThreeCycleTime -> ThreeCycleTime -> A) :
    ThreeAgentRingCohomologous c c := by
  refine ⟨fun _ => 0, ?_⟩
  funext i j
  simp [CechAdditiveCover.d0, identityPairZeroTripleCover]

/-- THEOREM 2: cohomology by 0-coboundary is symmetric. -/
theorem threeAgentRingCohomologous_symm
    {A : Type*} [AddCommGroup A]
    {c d : ThreeCycleTime -> ThreeCycleTime -> A}
    (h : ThreeAgentRingCohomologous c d) :
    ThreeAgentRingCohomologous d c := by
  rcases h with ⟨s, hs⟩
  refine ⟨fun i => -s i, ?_⟩
  funext i j
  rw [hs]
  simp [CechAdditiveCover.d0, identityPairZeroTripleCover]
  abel

/-- THEOREM 3: cohomology by 0-coboundary is transitive. -/
theorem threeAgentRingCohomologous_trans
    {A : Type*} [AddCommGroup A]
    {c d e : ThreeCycleTime -> ThreeCycleTime -> A}
    (hcd : ThreeAgentRingCohomologous c d)
    (hde : ThreeAgentRingCohomologous d e) :
    ThreeAgentRingCohomologous c e := by
  rcases hcd with ⟨s, hs⟩
  rcases hde with ⟨t, ht⟩
  refine ⟨fun i => s i + t i, ?_⟩
  funext i j
  rw [ht, hs]
  simp [CechAdditiveCover.d0, identityPairZeroTripleCover]
  abel

/-- THEOREM 4: the cohomology relation is an equivalence relation. -/
theorem threeAgentRingCohomologous_equivalence
    {A : Type*} [AddCommGroup A] :
    Equivalence
      (ThreeAgentRingCohomologous :
        (ThreeCycleTime -> ThreeCycleTime -> A) ->
          (ThreeCycleTime -> ThreeCycleTime -> A) -> Prop) where
  refl := threeAgentRingCohomologous_refl
  symm := by
    intro c d h
    exact threeAgentRingCohomologous_symm h
  trans := by
    intro c d e hcd hde
    exact threeAgentRingCohomologous_trans hcd hde

/-! ## Residual is invariant under coboundary shifts -/

/-- THEOREM 5: a pure 0-coboundary has zero selected ring residual. -/
theorem threeAgentRingResidual_coboundary_zero
    {A : Type*} [AddCommGroup A]
    (s : ThreeCycleTime -> A) :
    threeAgentRingResidual
      (CechAdditiveCover.d0
        (identityPairZeroTripleCover ThreeCycleTime A) s) = 0 := by
  have hsum := cyclic_coboundary_residual_zero threeCycleNext s
  rw [threeCycleNext_sum_eq_residual] at hsum
  exact hsum

/-- THEOREM 6: adding a 0-coboundary does not change selected ring residual. -/
theorem threeAgentRingResidual_add_coboundary
    {A : Type*} [AddCommGroup A]
    (c : ThreeCycleTime -> ThreeCycleTime -> A) (s : ThreeCycleTime -> A) :
    threeAgentRingResidual
      (fun i j =>
        c i j +
          CechAdditiveCover.d0
            (identityPairZeroTripleCover ThreeCycleTime A) s i j) =
      threeAgentRingResidual c := by
  have hzero := threeAgentRingResidual_coboundary_zero s
  simp [threeAgentRingResidual, CechAdditiveCover.d0,
    identityPairZeroTripleCover] at hzero ⊢
  abel

/-- THEOREM 7: cohomologous three-agent ring cochains have the same residual. -/
theorem threeAgentRingResidual_eq_of_cohomologous
    {A : Type*} [AddCommGroup A]
    {c d : ThreeCycleTime -> ThreeCycleTime -> A}
    (h : ThreeAgentRingCohomologous c d) :
    threeAgentRingResidual d = threeAgentRingResidual c := by
  rcases h with ⟨s, hs⟩
  rw [hs]
  exact threeAgentRingResidual_add_coboundary c s

/-! ## Integer residual magnitude descends to the quotient -/

/-- THEOREM 8: integer residual magnitude is invariant under coboundary shifts.
-/
theorem threeAgentRingResidualMagnitude_add_coboundary
    (c : ThreeCycleTime -> ThreeCycleTime -> Int)
    (s : ThreeCycleTime -> Int) :
    threeAgentRingResidualMagnitude
      (fun i j =>
        c i j +
          CechAdditiveCover.d0
            (identityPairZeroTripleCover ThreeCycleTime Int) s i j) =
      threeAgentRingResidualMagnitude c := by
  unfold threeAgentRingResidualMagnitude
  rw [threeAgentRingResidual_add_coboundary c s]

/-- THEOREM 9: cohomologous integer cochains have the same residual magnitude.
-/
theorem threeAgentRingResidualMagnitude_eq_of_cohomologous
    {c d : ThreeCycleTime -> ThreeCycleTime -> Int}
    (h : ThreeAgentRingCohomologous c d) :
    threeAgentRingResidualMagnitude d =
      threeAgentRingResidualMagnitude c := by
  rcases h with ⟨s, hs⟩
  rw [hs]
  exact threeAgentRingResidualMagnitude_add_coboundary c s

/-- THEOREM 10: the residual magnitude is a quotient-level zero test: every
cohomologous representative has zero magnitude iff the chosen representative is
selected-edge exact. -/
theorem threeAgentRingResidualMagnitude_zero_on_class_iff_edgeExact
    (c : ThreeCycleTime -> ThreeCycleTime -> Int) :
    (forall d,
        ThreeAgentRingCohomologous c d ->
          threeAgentRingResidualMagnitude d = 0) <->
      ThreeAgentRingEdgeExact c := by
  constructor
  · intro h
    have hc0 := h c (threeAgentRingCohomologous_refl c)
    exact (threeAgentRingResidualMagnitude_eq_zero_iff_edgeExact c).mp hc0
  · intro hexact d hcd
    have hmag := threeAgentRingResidualMagnitude_eq_of_cohomologous hcd
    have hc0 :
        threeAgentRingResidualMagnitude c = 0 :=
      (threeAgentRingResidualMagnitude_eq_zero_iff_edgeExact c).mpr hexact
    rw [hmag, hc0]

/-!
  Summary:
  - The three-agent selected-ring residual is invariant under adding a
    0-coboundary.
  - Integer residual magnitude is therefore well-defined on the corresponding
    cohomology classes.
  - Its zero class is exactly selected-edge exactness.  Calling the resulting
    number "memory strength" still requires a product/observation bridge, but
    the cohomological seminorm skeleton is now a theorem rather than a slogan.
-/
