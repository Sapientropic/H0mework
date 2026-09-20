/-
  Proposition 125: finite-cycle residual quotients and saturation attenuation.

  Proposition 121 proves quotient-level residual invariance for the selected
  three-agent ring.  Proposition 124 proves that saturation-rate attenuation
  acts on that residual by keeping the fraction `1 - σ`.

  This file lifts the algebraic part to arbitrary finite interaction rings.
  The statement is intentionally one-way where it must be: for an arbitrary
  permutation `next`, the selected edges may decompose into several cycles, so
  a zero *total* residual need not imply edge exactness on every component.
  Nonzero total residual is still a canonical obstruction witness, and
  saturation attenuation acts on that witness by the same noisy-OR residual
  law.
-/

import H0mework.Realization.RelaxationFlow.P124

/-! ## Finite-cycle residual and cohomology relation -/

/-- Accumulated phase around the selected finite interaction ring. -/
def finiteCycleResidual
    {Index A : Type*} [Fintype Index] [AddCommGroup A]
    (next : Equiv.Perm Index) (c : Index -> Index -> A) : A :=
  ∑ i, c i (next i)

/-- Two finite-ring cochains are cohomologous when they differ by a
0-coboundary on the identity-pair / zero-triple cover. -/
def FiniteCycleCohomologous
    {Index A : Type*} [Fintype Index] [AddCommGroup A]
    (c d : Index -> Index -> A) : Prop :=
  exists s : Index -> A,
    d = fun i j =>
      c i j +
        CechAdditiveCover.d0
          (identityPairZeroTripleCover Index A) s i j

/-- THEOREM 1: finite-cycle cohomology by 0-coboundary is reflexive. -/
theorem finiteCycleCohomologous_refl
    {Index A : Type*} [Fintype Index] [AddCommGroup A]
    (c : Index -> Index -> A) :
    FiniteCycleCohomologous c c := by
  refine ⟨fun _ => 0, ?_⟩
  funext i j
  simp [CechAdditiveCover.d0, identityPairZeroTripleCover]

/-- THEOREM 2: finite-cycle cohomology by 0-coboundary is symmetric. -/
theorem finiteCycleCohomologous_symm
    {Index A : Type*} [Fintype Index] [AddCommGroup A]
    {c d : Index -> Index -> A}
    (h : FiniteCycleCohomologous c d) :
    FiniteCycleCohomologous d c := by
  rcases h with ⟨s, hs⟩
  refine ⟨fun i => -s i, ?_⟩
  funext i j
  rw [hs]
  simp [CechAdditiveCover.d0, identityPairZeroTripleCover]
  abel

/-- THEOREM 3: finite-cycle cohomology by 0-coboundary is transitive. -/
theorem finiteCycleCohomologous_trans
    {Index A : Type*} [Fintype Index] [AddCommGroup A]
    {c d e : Index -> Index -> A}
    (hcd : FiniteCycleCohomologous c d)
    (hde : FiniteCycleCohomologous d e) :
    FiniteCycleCohomologous c e := by
  rcases hcd with ⟨s, hs⟩
  rcases hde with ⟨t, ht⟩
  refine ⟨fun i => s i + t i, ?_⟩
  funext i j
  rw [ht, hs]
  simp [CechAdditiveCover.d0, identityPairZeroTripleCover]
  abel

/-- THEOREM 4: finite-cycle cohomology is an equivalence relation. -/
theorem finiteCycleCohomologous_equivalence
    {Index A : Type*} [Fintype Index] [AddCommGroup A] :
    Equivalence
      (FiniteCycleCohomologous :
        (Index -> Index -> A) -> (Index -> Index -> A) -> Prop) where
  refl := finiteCycleCohomologous_refl
  symm := by
    intro c d h
    exact finiteCycleCohomologous_symm h
  trans := by
    intro c d e hcd hde
    exact finiteCycleCohomologous_trans hcd hde

/-! ## Residual descends to the quotient -/

/-- THEOREM 5: a pure 0-coboundary has zero accumulated finite-cycle residual.
-/
theorem finiteCycleResidual_coboundary_zero
    {Index A : Type*} [Fintype Index] [AddCommGroup A]
    (next : Equiv.Perm Index) (s : Index -> A) :
    finiteCycleResidual next
      (CechAdditiveCover.d0
        (identityPairZeroTripleCover Index A) s) = 0 :=
  cyclic_coboundary_residual_zero next s

/-- THEOREM 6: adding a 0-coboundary does not change the accumulated
finite-cycle residual. -/
theorem finiteCycleResidual_add_coboundary
    {Index A : Type*} [Fintype Index] [AddCommGroup A]
    (next : Equiv.Perm Index) (c : Index -> Index -> A) (s : Index -> A) :
    finiteCycleResidual next
      (fun i j =>
        c i j +
          CechAdditiveCover.d0
            (identityPairZeroTripleCover Index A) s i j) =
      finiteCycleResidual next c := by
  unfold finiteCycleResidual
  rw [Finset.sum_add_distrib]
  rw [cyclic_coboundary_residual_zero next s]
  simp

/-- THEOREM 7: cohomologous finite-ring cochains have the same accumulated
residual. -/
theorem finiteCycleResidual_eq_of_cohomologous
    {Index A : Type*} [Fintype Index] [AddCommGroup A]
    {next : Equiv.Perm Index} {c d : Index -> Index -> A}
    (h : FiniteCycleCohomologous c d) :
    finiteCycleResidual next d = finiteCycleResidual next c := by
  rcases h with ⟨s, hs⟩
  rw [hs]
  exact finiteCycleResidual_add_coboundary next c s

/-- Integer magnitude of a finite-cycle residual.  It is a quotient-level
invariant, but for multi-cycle permutations zero total residual is weaker than
selected-edge exactness on every component. -/
def finiteCycleResidualMagnitude
    {Index : Type*} [Fintype Index]
    (next : Equiv.Perm Index) (c : Index -> Index -> Int) : Nat :=
  Int.natAbs (finiteCycleResidual next c)

/-- THEOREM 8: integer finite-cycle residual magnitude is invariant under
cohomology. -/
theorem finiteCycleResidualMagnitude_eq_of_cohomologous
    {Index : Type*} [Fintype Index]
    {next : Equiv.Perm Index} {c d : Index -> Index -> Int}
    (h : FiniteCycleCohomologous c d) :
    finiteCycleResidualMagnitude next d =
      finiteCycleResidualMagnitude next c := by
  unfold finiteCycleResidualMagnitude
  rw [finiteCycleResidual_eq_of_cohomologous h]

/-- THEOREM 9: positive finite-cycle residual magnitude gives an H¹
obstruction. -/
theorem finiteCycleResidualMagnitude_pos_h1
    {Index : Type*} [Fintype Index]
    (next : Equiv.Perm Index) (c : Index -> Index -> Int)
    (hpos : 0 < finiteCycleResidualMagnitude next c) :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover Index Int) c := by
  have hres : NoncancelledCycleResidual next c := by
    simpa [finiteCycleResidualMagnitude, finiteCycleResidual,
      NoncancelledCycleResidual] using (Int.natAbs_pos).mp hpos
  exact ⟨identityPairZeroTripleCover_all_cochains_cocycle c,
    not_coboundary_of_noncancelled_cycle_residual next c hres⟩

/-! ## Saturation attenuation acts on finite-cycle cohomology -/

/-- Saturation-rate attenuation for finite-ring cochains: keep fraction
`1 - σ` of every phase value. -/
def finiteCohomologyConsolidationStep
    {Index α : Type*} [Field α]
    (σ : α) (c : Index -> Index -> α) : Index -> Index -> α :=
  fun i j => (1 - σ) * c i j

/-- THEOREM 10: finite cohomology-layer attenuation composes by the same
noisy-OR law as saturation rates. -/
theorem finiteCohomologyConsolidationStep_compose
    {Index α : Type*} [Field α]
    (σ₁ σ₂ : α) (c : Index -> Index -> α) :
    finiteCohomologyConsolidationStep σ₂
        (finiteCohomologyConsolidationStep σ₁ c) =
      finiteCohomologyConsolidationStep (satOrField σ₁ σ₂) c := by
  funext i j
  simp [finiteCohomologyConsolidationStep, satOrField]
  ring

/-- THEOREM 11: finite cohomology-layer attenuation preserves the cohomology
relation, so it is a quotient-level operation. -/
theorem finiteCycleCohomologous_consolidationStep
    {Index α : Type*} [Fintype Index] [Field α]
    {c d : Index -> Index -> α}
    (σ : α)
    (h : FiniteCycleCohomologous c d) :
    FiniteCycleCohomologous
      (finiteCohomologyConsolidationStep σ c)
      (finiteCohomologyConsolidationStep σ d) := by
  rcases h with ⟨s, hs⟩
  refine ⟨fun i => (1 - σ) * s i, ?_⟩
  funext i j
  rw [hs]
  simp [finiteCohomologyConsolidationStep, CechAdditiveCover.d0,
    identityPairZeroTripleCover]
  ring

/-- THEOREM 12: the finite-cycle residual is attenuated by exactly the residual
rate `1 - σ`. -/
theorem finiteCycleResidual_consolidationStep
    {Index α : Type*} [Fintype Index] [Field α]
    (next : Equiv.Perm Index) (σ : α) (c : Index -> Index -> α) :
    finiteCycleResidual next (finiteCohomologyConsolidationStep σ c) =
      (1 - σ) * finiteCycleResidual next c := by
  unfold finiteCycleResidual finiteCohomologyConsolidationStep
  rw [Finset.mul_sum]

/-- THEOREM 13: two finite cohomology-layer consolidation steps attenuate the
residual by the composed noisy-OR residual rate. -/
theorem finiteCycleResidual_consolidationStep_compose
    {Index α : Type*} [Fintype Index] [Field α]
    (next : Equiv.Perm Index) (σ₁ σ₂ : α)
    (c : Index -> Index -> α) :
    finiteCycleResidual next
        (finiteCohomologyConsolidationStep σ₂
          (finiteCohomologyConsolidationStep σ₁ c)) =
      (1 - satOrField σ₁ σ₂) * finiteCycleResidual next c := by
  rw [finiteCohomologyConsolidationStep_compose,
    finiteCycleResidual_consolidationStep]

/-- THEOREM 14: full saturation gives a selected-edge global potential
explanation for any finite ring. -/
theorem finiteCohomologyConsolidationStep_one_cycleEdgePotentialExplained
    {Index α : Type*} [Fintype Index] [Field α]
    (next : Equiv.Perm Index) (c : Index -> Index -> α) :
    CycleEdgePotentialExplained next
      (finiteCohomologyConsolidationStep (1 : α) c) := by
  refine ⟨fun _ => 0, ?_⟩
  intro i
  simp [finiteCohomologyConsolidationStep, CechAdditiveCover.d0,
    identityPairZeroTripleCover]

/-- THEOREM 15: if the keep-rate is nonzero, attenuation preserves a nontrivial
finite-cycle H¹ obstruction. -/
theorem finiteCohomologyConsolidationStep_preserves_h1_of_keep_nonzero
    {Index α : Type*} [Fintype Index] [Field α]
    (next : Equiv.Perm Index) (σ : α) (c : Index -> Index -> α)
    (hkeep : 1 - σ ≠ 0)
    (hres : finiteCycleResidual next c ≠ 0) :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover Index α)
      (finiteCohomologyConsolidationStep σ c) := by
  have hstepResidual :
      finiteCycleResidual next
          (finiteCohomologyConsolidationStep σ c) ≠ 0 := by
    rw [finiteCycleResidual_consolidationStep]
    exact mul_ne_zero hkeep hres
  have hnc :
      NoncancelledCycleResidual next
        (finiteCohomologyConsolidationStep σ c) := by
    simpa [NoncancelledCycleResidual, finiteCycleResidual] using hstepResidual
  exact ⟨identityPairZeroTripleCover_all_cochains_cocycle
      (finiteCohomologyConsolidationStep σ c),
    not_coboundary_of_noncancelled_cycle_residual
      next (finiteCohomologyConsolidationStep σ c) hnc⟩

/-!
  Summary:
  - Finite-cycle residual and integer residual magnitude descend to the
    coboundary quotient for arbitrary finite interaction rings.
  - Positive finite residual magnitude is a genuine H¹ obstruction witness.
  - Saturation-rate attenuation is a quotient-level operation, composes by the
    same noisy-OR law, scales the finite-cycle residual by the keep-rate, kills
    the selected residual at full saturation, and preserves nontrivial H¹ for
    nonzero keep-rates.
  - Unlike the single three-agent cycle, arbitrary permutations may contain
    several cycles, so this file does not claim zero total residual is
    equivalent to selected-edge exactness on every component.
-/
