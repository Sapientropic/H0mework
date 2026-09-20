/-
  Proposition 126: componentwise cycle residuals, not total residual alone.

  Proposition 125 deliberately avoids the false converse "zero total residual
  implies selected-edge exactness" for arbitrary finite permutations: several
  disjoint cycles can cancel each other's accumulated residuals.

  This file proves the product/decomposition law that explains the caveat.
  For a disjoint sum of two selected cycle systems, selected-edge exactness
  holds exactly when it holds on each component.  In particular, for two
  three-agent rings it is equivalent to the two component residuals vanishing
  separately.  A concrete witness shows total residual can be zero while the
  combined system is still not exact.
-/

import H0mework.Realization.CyclicMemory.P125

/-! ## Disjoint sums of selected cycle systems -/

/-- Disjoint sum of two selected-edge permutations. -/
def sumPerm {L R : Type*}
    (nextL : Equiv.Perm L) (nextR : Equiv.Perm R) :
    Equiv.Perm (Sum L R) where
  toFun
    | Sum.inl i => Sum.inl (nextL i)
    | Sum.inr j => Sum.inr (nextR j)
  invFun
    | Sum.inl i => Sum.inl (nextL.symm i)
    | Sum.inr j => Sum.inr (nextR.symm j)
  left_inv := by
    intro x
    cases x <;> simp
  right_inv := by
    intro x
    cases x <;> simp

/-- Restrict a sum cochain to the left component. -/
def leftSelectedCochain {L R A : Type*}
    (c : Sum L R -> Sum L R -> A) : L -> L -> A :=
  fun i j => c (Sum.inl i) (Sum.inl j)

/-- Restrict a sum cochain to the right component. -/
def rightSelectedCochain {L R A : Type*}
    (c : Sum L R -> Sum L R -> A) : R -> R -> A :=
  fun i j => c (Sum.inr i) (Sum.inr j)

/-- THEOREM 1: selected-edge exactness for a disjoint sum decomposes into
selected-edge exactness on each component. -/
theorem sumPerm_cycleEdgePotentialExplained_iff
    {L R A : Type*} [Fintype L] [Fintype R] [AddCommGroup A]
    (nextL : Equiv.Perm L) (nextR : Equiv.Perm R)
    (c : Sum L R -> Sum L R -> A) :
    CycleEdgePotentialExplained (sumPerm nextL nextR) c <->
      CycleEdgePotentialExplained nextL (leftSelectedCochain c) /\
        CycleEdgePotentialExplained nextR (rightSelectedCochain c) := by
  constructor
  · rintro ⟨p, hp⟩
    constructor
    · refine ⟨fun i => p (Sum.inl i), ?_⟩
      intro i
      have h := hp (Sum.inl i)
      simpa [sumPerm, leftSelectedCochain, CechAdditiveCover.d0,
        identityPairZeroTripleCover] using h
    · refine ⟨fun i => p (Sum.inr i), ?_⟩
      intro i
      have h := hp (Sum.inr i)
      simpa [sumPerm, rightSelectedCochain, CechAdditiveCover.d0,
        identityPairZeroTripleCover] using h
  · rintro ⟨⟨pL, hpL⟩, ⟨pR, hpR⟩⟩
    refine ⟨fun x => Sum.elim pL pR x, ?_⟩
    intro x
    cases x with
    | inl i =>
        have h := hpL i
        simpa [sumPerm, leftSelectedCochain, CechAdditiveCover.d0,
          identityPairZeroTripleCover] using h
    | inr i =>
        have h := hpR i
        simpa [sumPerm, rightSelectedCochain, CechAdditiveCover.d0,
          identityPairZeroTripleCover] using h

/-- THEOREM 2: finite total residual of a disjoint sum is the sum of the two
component residuals. -/
theorem finiteCycleResidual_sumPerm
    {L R A : Type*} [Fintype L] [Fintype R] [AddCommGroup A]
    (nextL : Equiv.Perm L) (nextR : Equiv.Perm R)
    (c : Sum L R -> Sum L R -> A) :
    finiteCycleResidual (sumPerm nextL nextR) c =
      finiteCycleResidual nextL (leftSelectedCochain c) +
        finiteCycleResidual nextR (rightSelectedCochain c) := by
  simp [finiteCycleResidual, sumPerm, leftSelectedCochain,
    rightSelectedCochain]

/-! ## Two three-agent rings: componentwise residuals are complete -/

/-- THEOREM 3: for the disjoint sum of two three-agent rings, selected-edge
exactness is equivalent to both component residuals vanishing separately. -/
theorem twoThreeCycleExact_iff_component_residuals_zero
    (c :
      Sum ThreeCycleTime ThreeCycleTime ->
        Sum ThreeCycleTime ThreeCycleTime -> Int) :
    CycleEdgePotentialExplained (sumPerm threeCycleNext threeCycleNext) c <->
      threeAgentRingResidual (leftSelectedCochain c) = 0 /\
        threeAgentRingResidual (rightSelectedCochain c) = 0 := by
  calc
    CycleEdgePotentialExplained (sumPerm threeCycleNext threeCycleNext) c <->
        CycleEdgePotentialExplained threeCycleNext (leftSelectedCochain c) /\
          CycleEdgePotentialExplained threeCycleNext
            (rightSelectedCochain c) :=
      sumPerm_cycleEdgePotentialExplained_iff
        threeCycleNext threeCycleNext c
    _ <-> threeAgentRingResidual (leftSelectedCochain c) = 0 /\
        threeAgentRingResidual (rightSelectedCochain c) = 0 := by
      constructor
      · intro h
        constructor
        · exact (threeAgentRingEdgeExact_iff_residual_zero
            (leftSelectedCochain c)).mp
            (by simpa [ThreeAgentRingEdgeExact] using h.1)
        · exact (threeAgentRingEdgeExact_iff_residual_zero
            (rightSelectedCochain c)).mp
            (by simpa [ThreeAgentRingEdgeExact] using h.2)
      · intro h
        constructor
        · simpa [ThreeAgentRingEdgeExact] using
            (threeAgentRingEdgeExact_iff_residual_zero
              (leftSelectedCochain c)).mpr h.1
        · simpa [ThreeAgentRingEdgeExact] using
            (threeAgentRingEdgeExact_iff_residual_zero
              (rightSelectedCochain c)).mpr h.2

/-! ## A concrete cancellation witness -/

/-- Two disjoint three-rings with opposite component residuals.  The total
finite residual cancels, but selected-edge exactness still fails componentwise.
-/
def opposingTwoThreeCycleCochain :
    Sum ThreeCycleTime ThreeCycleTime ->
      Sum ThreeCycleTime ThreeCycleTime -> Int
  | Sum.inl ThreeCycleTime.t0, Sum.inl ThreeCycleTime.t1 => 1
  | Sum.inr ThreeCycleTime.t0, Sum.inr ThreeCycleTime.t1 => -1
  | _, _ => 0

/-- THEOREM 4: the left component residual of the cancellation witness is +1.
-/
theorem opposingTwoThreeCycle_leftResidual :
    threeAgentRingResidual
      (leftSelectedCochain opposingTwoThreeCycleCochain) = 1 := by
  simp [threeAgentRingResidual, leftSelectedCochain,
    opposingTwoThreeCycleCochain]

/-- THEOREM 5: the right component residual of the cancellation witness is -1.
-/
theorem opposingTwoThreeCycle_rightResidual :
    threeAgentRingResidual
      (rightSelectedCochain opposingTwoThreeCycleCochain) = -1 := by
  simp [threeAgentRingResidual, rightSelectedCochain,
    opposingTwoThreeCycleCochain]

/-- THEOREM 6: the combined total residual cancels to zero. -/
theorem opposingTwoThreeCycle_totalResidual_zero :
    finiteCycleResidual (sumPerm threeCycleNext threeCycleNext)
      opposingTwoThreeCycleCochain = 0 := by
  rw [finiteCycleResidual_sumPerm]
  have hleft :
      finiteCycleResidual threeCycleNext
          (leftSelectedCochain opposingTwoThreeCycleCochain) = 1 := by
    rw [show finiteCycleResidual threeCycleNext
          (leftSelectedCochain opposingTwoThreeCycleCochain) =
        threeAgentRingResidual
          (leftSelectedCochain opposingTwoThreeCycleCochain) by
        exact threeCycleNext_sum_eq_residual
          (leftSelectedCochain opposingTwoThreeCycleCochain)]
    exact opposingTwoThreeCycle_leftResidual
  have hright :
      finiteCycleResidual threeCycleNext
          (rightSelectedCochain opposingTwoThreeCycleCochain) = -1 := by
    rw [show finiteCycleResidual threeCycleNext
          (rightSelectedCochain opposingTwoThreeCycleCochain) =
        threeAgentRingResidual
          (rightSelectedCochain opposingTwoThreeCycleCochain) by
        exact threeCycleNext_sum_eq_residual
          (rightSelectedCochain opposingTwoThreeCycleCochain)]
    exact opposingTwoThreeCycle_rightResidual
  rw [hleft, hright]
  norm_num

/-- THEOREM 7: despite zero total residual, the cancellation witness is not
selected-edge exact. -/
theorem opposingTwoThreeCycle_not_exact :
    Not (CycleEdgePotentialExplained
      (sumPerm threeCycleNext threeCycleNext)
      opposingTwoThreeCycleCochain) := by
  intro hexact
  have hcomp :=
    (twoThreeCycleExact_iff_component_residuals_zero
      opposingTwoThreeCycleCochain).mp hexact
  have hleftZero :
      threeAgentRingResidual
        (leftSelectedCochain opposingTwoThreeCycleCochain) = 0 :=
    hcomp.1
  rw [opposingTwoThreeCycle_leftResidual] at hleftZero
  norm_num at hleftZero

/-!
  Summary:
  - Disjoint selected cycle systems glue by product: exactness is componentwise
    exactness, and total residual is the sum of component residuals.
  - For two three-agent rings, component residual zero is complete.
  - The explicit `+1` / `-1` witness proves that zero total residual is not a
    complete invariant for multi-cycle systems.  The complete invariant must be
    componentwise, which is exactly the missing structure noted in P125.
-/
