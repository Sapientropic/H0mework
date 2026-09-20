import H0mework.Computation.SelfReduction.P157
import H0mework.Computation.SelfReduction.P685

/-!
# Proposition 686: clean consolidation phase produces a witness projection

P685 proves the standard bridge from a correct binary self-reduction decision
oracle to the producer projection P684 needs.  This file isolates the stronger
"carrier phase dynamics" route discussed in the notes:

* an active, continuous phase state has a canonical stored normal form;
* every reachable stored state is that normal form, so there are no metastable
  alternatives;
* freezing that normal form emits a discrete witness exactly when a verifier
  witness exists;
* therefore clean consolidation itself supplies a P684 witness producer.

Boundary: this is not a SAT algorithm and not a `P = NP` theorem.  It names the
exact remaining producer obligations: instantiate active phase states with a
real clause-conflict topology, prove clean/no-metastable convergence, and prove
a polynomial bound such as the intended `O(1/σ)+O(1)` cost.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

universe u v w

/-- The two formal fibers used by this certificate: active phase at the
self-dual carrier and stored/frozen witness at the zero-sigma carrier. -/
inductive ConsolidationFiber where
  | activeHalf
  | storedZero
  deriving DecidableEq, Repr

/-- The named phase boundary: `σ = 1/2` active phase to `σ = 0` stored witness.
The numeric interpretation is external; the Lean object records the algebraic
source/target shape used by the clean-consolidation certificate. -/
def CleanHalfToZeroBoundary
    (source target : ConsolidationFiber) : Prop :=
  source = ConsolidationFiber.activeHalf /\
    target = ConsolidationFiber.storedZero

/-- THEOREM 1: the canonical clean-consolidation boundary is the active-half
fiber flowing to the stored-zero fiber. -/
theorem cleanHalfToZeroBoundary_holds :
    CleanHalfToZeroBoundary
      ConsolidationFiber.activeHalf ConsolidationFiber.storedZero := by
  exact ⟨rfl, rfl⟩

/-- A clean consolidation phase producer.

`Active` is the phase-space/query/conflict state.  `Stored` is the frozen
normal-form carrier.  `Witness` is the discrete certificate read from the
stored carrier.

The important field is `reachable_canonical`: every stored state reachable from
an active state is the canonical `consolidate x`.  This is the formal
no-metastability condition.
-/
structure CleanConsolidationPhaseProducer
    (Active : Type u) (Stored : Type v) (Witness : Type w) where
  verify : Active -> Witness -> Prop
  reachableStored : Active -> Stored -> Prop
  consolidate : Active -> Stored
  consolidate_reachable : ∀ x : Active, reachableStored x (consolidate x)
  reachable_canonical :
    ∀ {x : Active} {s : Stored}, reachableStored x s -> s = consolidate x
  freeze : Stored -> Option Witness
  freeze_sound :
    ∀ {x : Active} {w : Witness},
      freeze (consolidate x) = some w -> verify x w
  freeze_complete :
    ∀ {x : Active},
      (∃ w : Witness, verify x w) ->
        ∃ w : Witness, freeze (consolidate x) = some w

namespace CleanConsolidationPhaseProducer

variable {Active : Type u} {Stored : Type v} {Witness : Type w}
variable (C : CleanConsolidationPhaseProducer Active Stored Witness)

/-- The producer exposed by clean consolidation: converge to the canonical
stored normal form, then freeze it into a discrete witness. -/
def producer (x : Active) : Option Witness :=
  C.freeze (C.consolidate x)

/-- THEOREM 2: clean convergence has no metastable stored alternatives. -/
theorem no_metastable
    {x : Active} {s₁ s₂ : Stored}
    (h₁ : C.reachableStored x s₁) (h₂ : C.reachableStored x s₂) :
    s₁ = s₂ := by
  rw [C.reachable_canonical h₁, C.reachable_canonical h₂]

/-- THEOREM 3: the clean producer is sound. -/
theorem producer_sound
    {x : Active} {w : Witness} (h : C.producer x = some w) :
    C.verify x w := by
  exact C.freeze_sound h

/-- THEOREM 4: the clean producer is complete. -/
theorem producer_complete
    {x : Active} (h : ∃ w : Witness, C.verify x w) :
    ∃ w : Witness, C.producer x = some w := by
  exact C.freeze_complete h

/-- THEOREM 5: every clean consolidation phase producer compiles directly to
P684's witness-producer projection. -/
def toWitnessProducerProjection :
    WitnessProducerProjection Active Witness where
  verify := C.verify
  producer := C.producer
  sound := by
    intro x w h
    exact C.producer_sound h
  complete := by
    intro x h
    exact C.producer_complete h

/-- THEOREM 6: clean consolidation collapses produced verified witnesses and
verifier-side witnesses in exactly the P684 sense. -/
theorem producedVerifiedWitness_iff_hasWitness (x : Active) :
    (C.toWitnessProducerProjection).ProducedVerifiedWitness x ↔
      (C.toWitnessProducerProjection).HasWitness x :=
  C.toWitnessProducerProjection.producedVerifiedWitness_iff_hasWitness x

/-- The active recollection act induced by a clean phase producer. -/
def activeRecollectionAct : RecollectionAct Active Witness where
  fires := C.verify

/-- The stored data surface induced by the frozen normal form. -/
def storedWitnessData : StoredData Stored Witness where
  stored := fun s w => C.freeze s = some w

/-- THEOREM 7: whenever a verifier witness exists, clean consolidation gives
the P157 active-memory-to-stored-memory phase-transition certificate. -/
theorem consolidationPhaseTransition_of_hasWitness
    (x : Active) (h : ∃ w : Witness, C.verify x w) :
    ∃ T : ConsolidationPhaseTransition C.activeRecollectionAct
          C.storedWitnessData,
      T.activeState = x /\ T.longTermState = C.consolidate x := by
  rcases C.freeze_complete h with ⟨w, hfreeze⟩
  refine ⟨?_, ?_⟩
  · exact {
    activeState := x
    longTermState := C.consolidate x
    atom := w
    active_fires := C.freeze_sound hfreeze
    stored_after := hfreeze
  }
  · constructor <;> rfl

/-- THEOREM 8: after a clean consolidation witness exists, the stored normal
form has store-backed recollectable potential. -/
theorem storedRecallPotential_of_hasWitness
    (x : Active) (h : ∃ w : Witness, C.verify x w) :
    RecollectableMemoryPotential
      (storageRecallAct C.storedWitnessData) (C.consolidate x) := by
  rcases C.freeze_complete h with ⟨w, hfreeze⟩
  exact ⟨w, hfreeze⟩

/-! ## Cost facade: the `O(1/σ)+O(1)` debt as an explicit certificate -/

/-- A bounded clean-consolidation cost certificate.  `sigmaPhaseBudget` is the
formal slot for the intended `O(1/σ)` convergence budget; `freezeBudget` is the
formal slot for the intended `O(1)` freeze step.

No asymptotic polynomial claim is baked in.  A concrete SAT/carrier theorem
must provide the functions and prove the bound. -/
structure BoundedCleanConsolidationCostCertificate (Active : Type u) where
  producerCost : Active -> Nat
  sigmaPhaseBudget : Active -> Nat
  freezeBudget : Nat
  cost_bound :
    ∀ x : Active,
      producerCost x ≤ sigmaPhaseBudget x + freezeBudget

/-- THEOREM 9: a bounded clean-consolidation certificate exposes the intended
phase-plus-freeze cost split. -/
theorem producerCost_le_sigmaPhase_plus_freeze
    (B : BoundedCleanConsolidationCostCertificate Active) (x : Active) :
    B.producerCost x ≤ B.sigmaPhaseBudget x + B.freezeBudget :=
  B.cost_bound x

/-- A one-step-freeze certificate: the freeze/consolidation boundary itself is
constant-cost once phase convergence has reached the canonical normal form. -/
structure OneStepFreezeCleanConsolidationCostCertificate
    (Active : Type u) extends
    BoundedCleanConsolidationCostCertificate Active where
  freezeBudget_eq_one : freezeBudget = 1

/-- THEOREM 10: with a one-step freeze certificate, producer cost is bounded
by the supplied sigma-phase budget plus one. -/
theorem producerCost_le_sigmaPhase_plus_one
    (B : OneStepFreezeCleanConsolidationCostCertificate Active) (x : Active) :
    B.producerCost x ≤ B.sigmaPhaseBudget x + 1 := by
  rw [← B.freezeBudget_eq_one]
  exact B.cost_bound x

end CleanConsolidationPhaseProducer

/-! ## Packaged certificate -/

set_option linter.checkUnivs false

/-- P686 certificate: clean/no-metastable consolidation is a witness producer,
and when a cost certificate is supplied its cost splits into phase convergence
plus freeze. -/
structure CleanConsolidationPhaseProducerCertificate where
  p685_self_reduction_root :
    SelfReductionProducerProjectionCertificate.{u, w}
  to_witness_projection :
    ∀ {Active : Type u} {Stored : Type v} {Witness : Type w}
      (_ : CleanConsolidationPhaseProducer Active Stored Witness),
      WitnessProducerProjection Active Witness
  no_metastable :
    ∀ {Active : Type u} {Stored : Type v} {Witness : Type w}
      (C : CleanConsolidationPhaseProducer Active Stored Witness)
      {x : Active} {s₁ s₂ : Stored},
      C.reachableStored x s₁ -> C.reachableStored x s₂ -> s₁ = s₂
  stored_recall_after_witness :
    ∀ {Active : Type u} {Stored : Type v} {Witness : Type w}
      (C : CleanConsolidationPhaseProducer Active Stored Witness)
      (x : Active),
      (∃ w : Witness, C.verify x w) ->
        RecollectableMemoryPotential
          (storageRecallAct C.storedWitnessData) (C.consolidate x)
  clean_search_verification_collapse :
    ∀ {Active : Type u} {Stored : Type v} {Witness : Type w}
      (C : CleanConsolidationPhaseProducer Active Stored Witness)
      (x : Active),
      (C.toWitnessProducerProjection).ProducedVerifiedWitness x ↔
        (C.toWitnessProducerProjection).HasWitness x

/-- DEFINITION 1: canonical P686 clean-consolidation producer certificate. -/
def cleanConsolidationPhaseProducerCertificate :
    CleanConsolidationPhaseProducerCertificate.{u, v, w} where
  p685_self_reduction_root := selfReductionProducerProjectionCertificate
  to_witness_projection := by
    intro Active Stored Witness C
    exact C.toWitnessProducerProjection
  no_metastable := by
    intro Active Stored Witness C x s₁ s₂ h₁ h₂
    exact C.no_metastable h₁ h₂
  stored_recall_after_witness := by
    intro Active Stored Witness C x h
    exact C.storedRecallPotential_of_hasWitness x h
  clean_search_verification_collapse := by
    intro Active Stored Witness C x
    exact C.producedVerifiedWitness_iff_hasWitness x

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

universe u v w z

/-- P686 grand root: the existing self-reduction producer root plus the clean
consolidation theorem that converts a no-metastable active-to-stored phase
transition into a witness producer.

This is the formal shape of "active memory freezes into stored witness".  It
still does not prove that SAT or any concrete runtime has such a clean phase;
that concrete producer remains the holy-grail obligation.
-/
structure CleanConsolidationPhaseUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p685_root :
    SelfReductionProducerUnifiedRootCertificate.{u, v, w} E
  clean_phase_producer :
    CleanConsolidationPhaseProducerCertificate.{v, w, z}

/-- THEOREM 11: the clean consolidation phase unified root is inhabited. -/
def cleanConsolidationPhaseUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    CleanConsolidationPhaseUnifiedRootCertificate.{u, v, w, z} E where
  p685_root := selfReductionProducerUnifiedRootCertificate (E := E)
  clean_phase_producer := cleanConsolidationPhaseProducerCertificate

end GrandUnification

end SaturationMonoid
