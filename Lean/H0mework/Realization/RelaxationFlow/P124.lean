/-
  Proposition 124: saturation decay acts on the H¹ residual.

  Propositions 119-121 prove that finite reflexive rings generate their phase
  cochain structurally, that observation visibility is a projection/kernel
  question, and that the three-agent ring residual magnitude descends to the
  cohomology quotient.

  This file connects that H¹ side back to the original saturation algebra from
  `Basic.lean`.  A consolidation / attenuation step on a phase cochain keeps
  the residual fraction `1 - σ`.  Therefore two such steps compose by the same
  noisy-OR law as salience saturation:

      step σ₂ (step σ₁ c) = step (σ₁ ⋆ σ₂) c

  This is the pure algebraic part of the slogan "consolidation is saturation
  decay at the cohomology layer."  It is not a theorem about any concrete
  neural or product-level forgetting mechanism.
-/

import H0mework.Realization.Observation.Saturation
import H0mework.Realization.Relations.P121

/-! ## Saturation-rate attenuation of a three-agent phase cochain -/

/-- A cohomology-layer consolidation step: keep the residual fraction `1 - σ`
of every phase value.  This is the residual-rate side of the saturation bump. -/
def cohomologyConsolidationStep
    {α : Type*} [Field α]
    (σ : α) (c : ThreeCycleTime -> ThreeCycleTime -> α) :
    ThreeCycleTime -> ThreeCycleTime -> α :=
  fun i j => (1 - σ) * c i j

/-- THEOREM 1: consolidation steps compose by the same noisy-OR law as
saturation rates. -/
theorem cohomologyConsolidationStep_compose
    {α : Type*} [Field α]
    (σ₁ σ₂ : α) (c : ThreeCycleTime -> ThreeCycleTime -> α) :
    cohomologyConsolidationStep σ₂
        (cohomologyConsolidationStep σ₁ c) =
      cohomologyConsolidationStep (satOrField σ₁ σ₂) c := by
  funext i j
  simp [cohomologyConsolidationStep, satOrField]
  ring

/-- THEOREM 2: the selected ring residual is attenuated by exactly the residual
rate `1 - σ`. -/
theorem threeAgentRingResidual_consolidationStep
    {α : Type*} [Field α]
    (σ : α) (c : ThreeCycleTime -> ThreeCycleTime -> α) :
    threeAgentRingResidual (cohomologyConsolidationStep σ c) =
      (1 - σ) * threeAgentRingResidual c := by
  simp [threeAgentRingResidual, cohomologyConsolidationStep]
  ring

/-- THEOREM 3: two consolidation steps attenuate the residual by the composed
noisy-OR residual rate. -/
theorem threeAgentRingResidual_consolidationStep_compose
    {α : Type*} [Field α]
    (σ₁ σ₂ : α) (c : ThreeCycleTime -> ThreeCycleTime -> α) :
    threeAgentRingResidual
        (cohomologyConsolidationStep σ₂
          (cohomologyConsolidationStep σ₁ c)) =
      (1 - satOrField σ₁ σ₂) * threeAgentRingResidual c := by
  rw [cohomologyConsolidationStep_compose,
    threeAgentRingResidual_consolidationStep]

/-! ## Exactness and H¹ under attenuation -/

/-- THEOREM 4: after attenuation, selected-edge exactness is exactly vanishing
of the attenuated residual. -/
theorem cohomologyConsolidationStep_edgeExact_iff
    {α : Type*} [Field α]
    (σ : α) (c : ThreeCycleTime -> ThreeCycleTime -> α) :
    ThreeAgentRingEdgeExact (cohomologyConsolidationStep σ c) <->
      (1 - σ) * threeAgentRingResidual c = 0 := by
  calc
    ThreeAgentRingEdgeExact (cohomologyConsolidationStep σ c) <->
        threeAgentRingResidual (cohomologyConsolidationStep σ c) = 0 :=
      threeAgentRingEdgeExact_iff_residual_zero
        (cohomologyConsolidationStep σ c)
    _ <-> (1 - σ) * threeAgentRingResidual c = 0 := by
      rw [threeAgentRingResidual_consolidationStep]

/-- THEOREM 5: full saturation (`σ = 1`) kills the selected H¹ residual and
therefore makes the selected ring exact. -/
theorem cohomologyConsolidationStep_one_edgeExact
    {α : Type*} [Field α]
    (c : ThreeCycleTime -> ThreeCycleTime -> α) :
    ThreeAgentRingEdgeExact (cohomologyConsolidationStep (1 : α) c) := by
  exact (cohomologyConsolidationStep_edgeExact_iff (1 : α) c).mpr (by ring)

/-- THEOREM 6: if the residual rate is nonzero, attenuation preserves a
nontrivial H¹ obstruction. -/
theorem cohomologyConsolidationStep_preserves_h1_of_keep_nonzero
    {α : Type*} [Field α]
    (σ : α) (c : ThreeCycleTime -> ThreeCycleTime -> α)
    (hkeep : 1 - σ ≠ 0)
    (hres : threeAgentRingResidual c ≠ 0) :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover ThreeCycleTime α)
      (cohomologyConsolidationStep σ c) := by
  have hstep :
      threeAgentRingResidual (cohomologyConsolidationStep σ c) ≠ 0 := by
    rw [threeAgentRingResidual_consolidationStep]
    exact mul_ne_zero hkeep hres
  exact threeAgentRingResidual_nonzero_h1
    (cohomologyConsolidationStep σ c) hstep

/-!
  Summary:
  - The cohomology-layer attenuation step is not a new arbitrary operator: its
    composition law is the same noisy-OR saturation law already proved for
    salience updates.
  - The H¹ residual is scaled by the saturation residual rate `1 - σ`.
  - Full saturation kills the selected residual; any nonzero keep-rate
    preserves nontrivial H¹ when the original residual was nonzero.
  - This proves the algebraic skeleton of "consolidation as saturation decay",
    while leaving concrete runtime/neural interpretations as separate
    mechanism-faithfulness claims.
-/
