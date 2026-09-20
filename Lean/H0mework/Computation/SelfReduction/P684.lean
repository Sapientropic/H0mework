import H0mework.Physics.SourceForms.P683

/-!
# Proposition 684: producer projections collapse search to verification

P683 says that, on the finite input-output bridge, all proof obligations reduce
to the canonical question-answer pair.  This file records the computational
face of the same idea.

For an abstract verifier `verify : Instance -> Witness -> Prop`, search and
verification are not automatically the same.  They collapse only after a
producer projection is supplied: a canonical function

`producer : Instance -> Option Witness`

that is sound and complete for the verifier.  Then the existential verifier
question

`∃ w, verify x w`

is equivalent to the projected producer question

`∃ w, producer x = some w`,

and the produced witness is already verified.

Boundary: this is not a proof of `P = NP` and not a SAT algorithm.  It proves
the exact projection in which "search = verification" is true.  A genuine
`P = NP` theorem would still need an independent producer for SAT, plus a
formal polynomial-time bound for that producer.
-/

noncomputable section

namespace SaturationMonoid

/-! ## Abstract producer projection -/

namespace ComplexityProjection

universe u v

/-- A producer projection for an existential verification problem.

The producer is not inferred from the verifier.  It is extra structure: a
canonical projection that either emits a witness or says no witness exists.
-/
structure WitnessProducerProjection
    (Instance : Type u) (Witness : Type v) where
  verify : Instance -> Witness -> Prop
  producer : Instance -> Option Witness
  sound :
    ∀ {x : Instance} {w : Witness},
      producer x = some w -> verify x w
  complete :
    ∀ {x : Instance},
      (∃ w : Witness, verify x w) -> ∃ w : Witness, producer x = some w

namespace WitnessProducerProjection

variable {Instance : Type u} {Witness : Type v}
variable (C : WitnessProducerProjection Instance Witness)

/-- The ordinary verifier-side existential question. -/
def HasWitness (x : Instance) : Prop :=
  ∃ w : Witness, C.verify x w

/-- The producer-side projected question. -/
def ProducerHasWitness (x : Instance) : Prop :=
  ∃ w : Witness, C.producer x = some w

/-- The producer-side question with the soundness witness kept attached. -/
def ProducedVerifiedWitness (x : Instance) : Prop :=
  ∃ w : Witness, C.producer x = some w ∧ C.verify x w

/-- THEOREM 1: the producer projection decides exactly the verifier
existential. -/
theorem producerHasWitness_iff_hasWitness (x : Instance) :
    C.ProducerHasWitness x ↔ C.HasWitness x := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, C.sound hw⟩
  · intro h
    exact C.complete h

/-- THEOREM 2: the producer emits a verified witness exactly when a verifier
witness exists. -/
theorem producedVerifiedWitness_iff_hasWitness (x : Instance) :
    C.ProducedVerifiedWitness x ↔ C.HasWitness x := by
  constructor
  · rintro ⟨w, _hw, hv⟩
    exact ⟨w, hv⟩
  · intro h
    rcases C.complete h with ⟨w, hw⟩
    exact ⟨w, hw, C.sound hw⟩

/-- THEOREM 3: if the producer returns `none`, no verifier witness exists. -/
theorem noWitness_of_producer_none
    {x : Instance} (h : C.producer x = none) :
    ¬ C.HasWitness x := by
  intro hx
  rcases C.complete hx with ⟨w, hw⟩
  rw [h] at hw
  cases hw

/-- THEOREM 4: producer failure is equivalent to verifier nonexistence. -/
theorem producer_none_iff_noWitness (x : Instance) :
    C.producer x = none ↔ ¬ C.HasWitness x := by
  constructor
  · exact C.noWitness_of_producer_none
  · intro hnone
    cases hprod : C.producer x with
    | none => rfl
    | some w =>
        exfalso
        exact hnone ⟨w, C.sound hprod⟩

/-- Search and verification are collapsed by the producer projection. -/
def SearchVerificationCollapsed : Prop :=
  ∀ x : Instance, C.ProducedVerifiedWitness x ↔ C.HasWitness x

/-- THEOREM 5: every sound-and-complete producer projection collapses search
to verification. -/
theorem searchVerificationCollapsed :
    C.SearchVerificationCollapsed := by
  intro x
  exact C.producedVerifiedWitness_iff_hasWitness x

end WitnessProducerProjection

/-! ## Optional cost facade -/

/-- A bounded producer certificate.  The bound is deliberately abstract here:
this file only transports the search/verification collapse through a supplied
cost certificate.  To claim polynomial time for SAT, a later theorem must
instantiate `bound` with a genuine polynomial and a concrete SAT producer.
-/
structure BoundedProducerProjectionCertificate
    (Instance : Type u) (Witness : Type v) where
  projection : WitnessProducerProjection Instance Witness
  inputSize : Instance -> Nat
  producerCost : Instance -> Nat
  bound : Nat -> Nat
  cost_le_bound :
    ∀ x : Instance, producerCost x ≤ bound (inputSize x)

namespace BoundedProducerProjectionCertificate

variable {Instance : Type u} {Witness : Type v}
variable (C : BoundedProducerProjectionCertificate Instance Witness)

/-- THEOREM 6: bounded producer certificates inherit the same
search/verification collapse. -/
theorem producedVerifiedWitness_iff_hasWitness (x : Instance) :
    C.projection.ProducedVerifiedWitness x ↔ C.projection.HasWitness x :=
  C.projection.producedVerifiedWitness_iff_hasWitness x

/-- THEOREM 7: bounded producer certificates expose the claimed cost bound
without reclassifying it as polynomial. -/
theorem producerCost_le_bound (x : Instance) :
    C.producerCost x ≤ C.bound (C.inputSize x) :=
  C.cost_le_bound x

end BoundedProducerProjectionCertificate

/-! ## A compact reusable certificate -/

/-- P684 certificate: the abstract projection where "search = verification" is
valid is precisely a sound-and-complete witness producer projection. -/
structure ProducerProjectionCollapseCertificate where
  producer_hasWitness_iff :
    ∀ {Instance : Type u} {Witness : Type v}
      (C : WitnessProducerProjection Instance Witness) (x : Instance),
      C.ProducerHasWitness x ↔ C.HasWitness x
  produced_verified_iff :
    ∀ {Instance : Type u} {Witness : Type v}
      (C : WitnessProducerProjection Instance Witness) (x : Instance),
      C.ProducedVerifiedWitness x ↔ C.HasWitness x
  producer_none_iff_noWitness :
    ∀ {Instance : Type u} {Witness : Type v}
      (C : WitnessProducerProjection Instance Witness) (x : Instance),
      C.producer x = none ↔ ¬ C.HasWitness x
  search_verification_collapsed :
    ∀ {Instance : Type u} {Witness : Type v}
      (C : WitnessProducerProjection Instance Witness),
      C.SearchVerificationCollapsed

/-- THEOREM 8: canonical producer-projection collapse certificate. -/
theorem producerProjectionCollapseCertificate :
    ProducerProjectionCollapseCertificate.{u, v} := by
  refine
    { producer_hasWitness_iff := ?_
      produced_verified_iff := ?_
      producer_none_iff_noWitness := ?_
      search_verification_collapsed := ?_ }
  · intro Instance Witness C x
    exact C.producerHasWitness_iff_hasWitness x
  · intro Instance Witness C x
    exact C.producedVerifiedWitness_iff_hasWitness x
  · intro Instance Witness C x
    exact C.producer_none_iff_noWitness x
  · intro Instance Witness C
    exact C.searchVerificationCollapsed

end ComplexityProjection

/-! ## Grand-root packaging with the finite bridge proof principle -/

namespace GrandUnification

open StandardModelConstraint
open ComplexityProjection

universe u v w

/-- P684 grand root: P683's finite canonical question-answer bridge plus the
abstract producer projection in which existential search and verification
collapse.

This is the formal version of the answer "the faster projection is the
producer projection".  It is intentionally conditional on a producer; it does
not manufacture the producer for SAT or any other concrete problem. -/
structure ProducerProjectionUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p683_root :
    CanonicalProofPrincipleUnifiedRootCertificate E
  producer_projection_collapse :
    ProducerProjectionCollapseCertificate.{v, w}

/-- THEOREM 9: the producer-projection unified root is inhabited. -/
def producerProjectionUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    ProducerProjectionUnifiedRootCertificate.{u, v, w} E where
  p683_root := canonicalProofPrincipleUnifiedRootCertificate (E := E)
  producer_projection_collapse :=
    producerProjectionCollapseCertificate

end GrandUnification

end SaturationMonoid
