/-
  Proposition 120: observation-layer visibility for generated cyclic memory.

  Proposition 119 proves that finite reflexive interaction rings generate a
  phase cochain in the additive observation group returned by their reads.  A
  production system may expose only a projection of that layer.  This file
  makes the remaining visibility boundary algebraic:

      visible residual = projection(generated residual)

  If the projection does not kill the generated residual, then the projected
  cochain has a genuine H¹ obstruction and some selected edge has visible
  nonzero phase.  That visible nonzero phase also proves the original
  downstream read changed.  If the projection kills the residual, the boundary
  is exactly a kernel/visibility boundary, not a missing phase-map artifact.
-/

import H0mework.Realization.CyclicMemory.P119

namespace FiniteReflexiveInteractionRing

variable {Index State A B : Type*}
variable [Fintype Index] [AddCommGroup A] [AddCommGroup B]

/-! ## Projecting generated phase to a visible observation layer -/

/-- Project the generated phase cochain through an additive observation map. -/
def visibleInteractionPhase
    (R : FiniteReflexiveInteractionRing Index State A)
    (π : A →+ B) : Index -> Index -> B :=
  fun i j => π (R.generatedInteractionPhase i j)

/-- Accumulated selected-edge residual after observation projection. -/
def visibleResidual
    (R : FiniteReflexiveInteractionRing Index State A)
    (π : A →+ B) : B :=
  ∑ i, R.visibleInteractionPhase π i (R.next i)

/-- THEOREM 1: visible residual is exactly the projection of generated
residual. -/
theorem visibleResidual_eq_map_generatedResidual
    (R : FiniteReflexiveInteractionRing Index State A)
    (π : A →+ B) :
    R.visibleResidual π = π R.generatedResidual := by
  simp [visibleResidual, visibleInteractionPhase, generatedResidual]

/-- The projection captures this ring's residual exactly when it does not send
the generated residual to zero. -/
def ResidualCaptured
    (R : FiniteReflexiveInteractionRing Index State A)
    (π : A →+ B) : Prop :=
  π R.generatedResidual ≠ 0

/-- THEOREM 2: residual capture is equivalent to nonzero visible residual. -/
theorem residualCaptured_iff_visibleResidual_nonzero
    (R : FiniteReflexiveInteractionRing Index State A)
    (π : A →+ B) :
    R.ResidualCaptured π <-> R.visibleResidual π ≠ 0 := by
  rw [ResidualCaptured, visibleResidual_eq_map_generatedResidual]

/-! ## Visible noncancellation gives H¹ and a changed read -/

/-- THEOREM 3: if the visible residual is nonzero, the visible phase cochain is
noncancelled on the selected ring. -/
theorem visibleResidual_nonzero_iff_noncancelled
    (R : FiniteReflexiveInteractionRing Index State A)
    (π : A →+ B) :
    R.visibleResidual π ≠ 0 <->
      NoncancelledCycleResidual R.next (R.visibleInteractionPhase π) := by
  rfl

/-- THEOREM 4: visible residual nonzero gives H¹ in the visible coefficient
group. -/
theorem visibleResidual_nonzero_h1
    (R : FiniteReflexiveInteractionRing Index State A)
    (π : A →+ B)
    (hvis : R.visibleResidual π ≠ 0) :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover Index B)
      (R.visibleInteractionPhase π) := by
  have hnc : NoncancelledCycleResidual R.next (R.visibleInteractionPhase π) := by
    exact (R.visibleResidual_nonzero_iff_noncancelled π).mp hvis
  exact ⟨identityPairZeroTripleCover_all_cochains_cocycle
      (R.visibleInteractionPhase π),
    not_coboundary_of_noncancelled_cycle_residual
      R.next (R.visibleInteractionPhase π) hnc⟩

/-- THEOREM 5: a visible nonzero edge phase implies the original downstream read
changed. -/
theorem visible_edge_nonzero_implies_readChanged
    (R : FiniteReflexiveInteractionRing Index State A)
    (π : A →+ B) (i : Index)
    (hi : R.visibleInteractionPhase π i (R.next i) ≠ 0) :
    R.EdgeReadChanged i := by
  have hphase : R.generatedInteractionPhase i (R.next i) ≠ 0 := by
    intro hzero
    exact hi (by simp [visibleInteractionPhase, hzero])
  exact (R.generatedInteractionPhase_edge_nonzero_iff_readChanged i).mp hphase

/-- THEOREM 6: visible residual nonzero forces at least one original downstream
read change. -/
theorem visibleResidual_nonzero_exists_readChanged
    (R : FiniteReflexiveInteractionRing Index State A)
    (π : A →+ B)
    (hvis : R.visibleResidual π ≠ 0) :
    exists i, R.EdgeReadChanged i := by
  have hnc : NoncancelledCycleResidual R.next (R.visibleInteractionPhase π) := by
    exact (R.visibleResidual_nonzero_iff_noncancelled π).mp hvis
  rcases finiteResidual_nonzero_exists_edge_nonzero hnc with ⟨i, hi⟩
  exact ⟨i, R.visible_edge_nonzero_implies_readChanged π i hi⟩

/-- THEOREM 7: residual captured by the observation projection gives both H¹
in the visible layer and a changed original downstream read. -/
theorem residualCaptured_h1_and_readChanged
    (R : FiniteReflexiveInteractionRing Index State A)
    (π : A →+ B)
    (hcap : R.ResidualCaptured π) :
    CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover Index B)
        (R.visibleInteractionPhase π) /\
      exists i, R.EdgeReadChanged i := by
  have hvis : R.visibleResidual π ≠ 0 :=
    (R.residualCaptured_iff_visibleResidual_nonzero π).mp hcap
  exact ⟨R.visibleResidual_nonzero_h1 π hvis,
    R.visibleResidual_nonzero_exists_readChanged π hvis⟩

/-! ## Kernel boundary -/

/-- THEOREM 8: if the observation projection kills the generated residual, the
visible residual is zero. -/
theorem visibleResidual_zero_of_map_generatedResidual_zero
    (R : FiniteReflexiveInteractionRing Index State A)
    (π : A →+ B)
    (hzero : π R.generatedResidual = 0) :
    R.visibleResidual π = 0 := by
  rw [visibleResidual_eq_map_generatedResidual]
  exact hzero

end FiniteReflexiveInteractionRing

/-!
  Summary:
  - The visible phase layer is not a new runtime artifact; it is an additive
    projection of the generated phase layer.
  - If the projection captures the generated residual, H¹ and changed-read
    witnesses follow by pure algebra.
  - If the projection sends the residual to zero, the remaining boundary is
    exactly the observation-kernel question: the cyclic memory class may exist
    in the generated coefficient layer while being invisible to this projected
    observation layer.
-/
