/-
  Proposition 130: visible cyclic H¹ produces canonical reflexive memory.

  P119/P120 prove that finite reflexive interaction rings generate their own
  phase cochains: a noncancelled residual is not a runtime-supplied artifact,
  but the accumulated read/write observation difference around the ring.

  P45/P51 prove the corrected memory ontology for reflexive algebra:
  read-after-write observation change is exactly canonical reflexive memory
  production, and equivalently recollectable memory potential.

  This file composes those two lines.  If a generated or visible cyclic
  residual is nonzero, then the ring has a genuine H¹ obstruction and at least
  one selected edge produces canonical reflexive memory.  No seven-case
  AIppocampus taxonomy classifier is used here; this is the adapter-free
  one-atom memory object forced by the reflexive loop itself.
-/

import H0mework.Realization.CyclicMemory.P120
import H0mework.Realization.Memory.StorageDistinction

namespace FiniteReflexiveInteractionRing

variable {Index State A B : Type*}
variable [Fintype Index] [AddCommGroup A] [AddCommGroup B]

/-! ## Edge-induced reflexive query -/

/-- The one-edge reflexive query induced by an interaction-ring edge.  Agent
`i` writes from its base state; the downstream agent `next i` reads the result.
The write is constant in the local input because the edge event is the fixed
upstream write that triggered this downstream read. -/
def edgeReflexiveQuery
    (R : FiniteReflexiveInteractionRing Index State A)
    (i : Index) : ReflexiveQuery State A where
  read := (R.query (R.next i)).read
  write := fun _ => (R.query i).write (R.base i)

/-- THEOREM 1: the ring's edge changed-read predicate is exactly the local
reflexive λ obstruction of the edge-induced query at the downstream base
state. -/
theorem edgeReadChanged_iff_edgeReflexiveObstruction
    (R : FiniteReflexiveInteractionRing Index State A) (i : Index) :
    R.EdgeReadChanged i <->
      ReflexiveLambdaObstruction (R.edgeReflexiveQuery i)
        (R.base (R.next i)) := by
  rfl

/-- THEOREM 2: an edge changed-read is exactly canonical reflexive memory
production for the edge-induced query. -/
theorem edgeReadChanged_iff_edgeReflexiveMemoryProduction
    (R : FiniteReflexiveInteractionRing Index State A) (i : Index) :
    R.EdgeReadChanged i <->
      ReflexiveMemoryProduction (R.edgeReflexiveQuery i)
        (R.base (R.next i)) ReflexiveMemoryAtom.observationChanged := by
  exact (R.edgeReadChanged_iff_edgeReflexiveObstruction i).trans
    (reflexiveObstruction_iff_reflexiveMemoryProduction
      (R.edgeReflexiveQuery i) (R.base (R.next i)))

/-- THEOREM 3: the same edge changed-read is exactly recollectable memory
potential for the canonical recollection act induced by that edge query. -/
theorem edgeReadChanged_iff_edgeRecollectablePotential
    (R : FiniteReflexiveInteractionRing Index State A) (i : Index) :
    R.EdgeReadChanged i <->
      RecollectableMemoryPotential
        (reflexiveRecollectionAct (R.edgeReflexiveQuery i))
        (R.base (R.next i)) := by
  exact (R.edgeReadChanged_iff_edgeReflexiveObstruction i).trans
    (reflexiveObstruction_iff_recollectablePotential
      (R.edgeReflexiveQuery i) (R.base (R.next i)))

/-! ## Generated cyclic residuals produce canonical memory -/

/-- THEOREM 4: a nonzero generated cyclic residual gives H¹ and canonical
reflexive memory production on at least one selected edge. -/
theorem generatedResidual_nonzero_h1_and_edgeReflexiveMemoryProduction
    (R : FiniteReflexiveInteractionRing Index State A)
    (hres : R.generatedResidual ≠ 0) :
    CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover Index A)
        R.generatedInteractionPhase /\
      exists i,
        ReflexiveMemoryProduction (R.edgeReflexiveQuery i)
          (R.base (R.next i)) ReflexiveMemoryAtom.observationChanged := by
  rcases R.generatedResidual_nonzero_h1_and_readChanged hres with
    ⟨hh1, i, hchanged⟩
  exact ⟨hh1, i,
    (R.edgeReadChanged_iff_edgeReflexiveMemoryProduction i).mp hchanged⟩

/-- THEOREM 5: a nonzero generated cyclic residual gives H¹ and recollectable
memory potential on at least one selected edge. -/
theorem generatedResidual_nonzero_h1_and_edgeRecollectablePotential
    (R : FiniteReflexiveInteractionRing Index State A)
    (hres : R.generatedResidual ≠ 0) :
    CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover Index A)
        R.generatedInteractionPhase /\
      exists i,
        RecollectableMemoryPotential
          (reflexiveRecollectionAct (R.edgeReflexiveQuery i))
          (R.base (R.next i)) := by
  rcases R.generatedResidual_nonzero_h1_and_readChanged hres with
    ⟨hh1, i, hchanged⟩
  exact ⟨hh1, i,
    (R.edgeReadChanged_iff_edgeRecollectablePotential i).mp hchanged⟩

/-! ## Visible cyclic residuals produce canonical memory -/

/-- THEOREM 6: if the observation projection captures the residual, the visible
H¹ class and canonical edge reflexive memory production appear together. -/
theorem residualCaptured_h1_and_edgeReflexiveMemoryProduction
    (R : FiniteReflexiveInteractionRing Index State A)
    (π : A →+ B)
    (hcap : R.ResidualCaptured π) :
    CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover Index B)
        (R.visibleInteractionPhase π) /\
      exists i,
        ReflexiveMemoryProduction (R.edgeReflexiveQuery i)
          (R.base (R.next i)) ReflexiveMemoryAtom.observationChanged := by
  rcases R.residualCaptured_h1_and_readChanged π hcap with
    ⟨hh1, i, hchanged⟩
  exact ⟨hh1, i,
    (R.edgeReadChanged_iff_edgeReflexiveMemoryProduction i).mp hchanged⟩

/-- THEOREM 7: if the observation projection captures the residual, the visible
H¹ class and recollectable memory potential appear together. -/
theorem residualCaptured_h1_and_edgeRecollectablePotential
    (R : FiniteReflexiveInteractionRing Index State A)
    (π : A →+ B)
    (hcap : R.ResidualCaptured π) :
    CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover Index B)
        (R.visibleInteractionPhase π) /\
      exists i,
        RecollectableMemoryPotential
          (reflexiveRecollectionAct (R.edgeReflexiveQuery i))
          (R.base (R.next i)) := by
  rcases R.residualCaptured_h1_and_readChanged π hcap with
    ⟨hh1, i, hchanged⟩
  exact ⟨hh1, i,
    (R.edgeReadChanged_iff_edgeRecollectablePotential i).mp hchanged⟩

end FiniteReflexiveInteractionRing

/-!
  Summary:
  - P130 connects generated/visible cyclic H¹ to memory production without a
    seven-case taxonomy adapter.
  - A captured cyclic residual gives both an H¹ obstruction and canonical
    reflexive memory production on some edge.
  - The recollectable-potential corollaries state the same result in the
    corrected memory ontology from P51: memory is recollectability, not passive
    stored state.

  Remaining boundary:
  - A production runtime still has to instantiate the finite reflexive
    interaction ring and justify that the chosen additive observation
    projection is the product-visible layer.
-/
