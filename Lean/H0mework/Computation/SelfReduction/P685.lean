import H0mework.Computation.SelfReduction.P684

/-!
# Proposition 685: self-reduction turns decision into a producer projection

P684 proves that search and verification collapse once a sound-and-complete
witness producer projection is supplied.  This file moves one step upstream:
for a binary self-reducible verifier, a sound-and-complete decision oracle
constructs such a producer by recursively choosing a live branch.

This is the classical SAT shape abstracted away from syntax:

* `rank` is the number of unresolved choices;
* `left` and `right` are the two restrictions;
* a true decision at a nonterminal node implies at least one child is true;
* child witnesses lift back to parent witnesses;
* terminal true nodes can emit a terminal witness.

Boundary: this still does not prove `P = NP`.  It proves the standard bridge
from a correct self-reduction decision procedure to a witness producer.  A
concrete SAT theorem must instantiate this interface with formulas and then
prove a polynomial cost bound for the resulting producer.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

set_option linter.checkUnivs false

universe u v

/-- A binary self-reducible verification problem with a decision oracle.

The oracle is represented by `decider`; its correctness is the logical bridge
between decision and existential verification.  The reduction data then turns
that decision bridge into an actual witness producer.
-/
structure BinarySelfReduction (Node : Type u) (Witness : Type v) where
  verify : Node -> Witness -> Prop
  decider : Node -> Bool
  decider_correct :
    ∀ x : Node, decider x = true ↔ ∃ w : Witness, verify x w
  rank : Node -> Nat
  terminal : Node -> Option Witness
  terminal_sound :
    ∀ {x : Node} {w : Witness}, terminal x = some w -> verify x w
  terminal_complete :
    ∀ {x : Node}, rank x = 0 -> (∃ w : Witness, verify x w) ->
      ∃ w : Witness, terminal x = some w ∧ verify x w
  left : Node -> Node
  right : Node -> Node
  left_sound :
    ∀ {x : Node} {w : Witness}, verify (left x) w -> verify x w
  right_sound :
    ∀ {x : Node} {w : Witness}, verify (right x) w -> verify x w
  child_complete :
    ∀ {x : Node}, 0 < rank x -> (∃ w : Witness, verify x w) ->
      (∃ w : Witness, verify (left x) w) ∨
        (∃ w : Witness, verify (right x) w)
  rank_left_lt :
    ∀ {x : Node}, 0 < rank x -> rank (left x) < rank x
  rank_right_lt :
    ∀ {x : Node}, 0 < rank x -> rank (right x) < rank x

namespace BinarySelfReduction

variable {Node : Type u} {Witness : Type v}
variable (C : BinarySelfReduction Node Witness)

/-- Fuel-bounded branch search.  The real producer calls this with
`fuel = rank x`; the more general fuel form gives a clean induction principle.
-/
def searchFuel : Nat -> Node -> Option Witness
  | 0, x =>
      if C.decider x then
        C.terminal x
      else
        none
  | n + 1, x =>
      if C.decider x then
        if C.rank x = 0 then
          C.terminal x
        else if C.decider (C.left x) then
          searchFuel n (C.left x)
        else
          searchFuel n (C.right x)
      else
        none

/-- THEOREM 1: any witness emitted by `searchFuel` verifies the original node.
-/
theorem searchFuel_sound :
    ∀ fuel x w, C.searchFuel fuel x = some w -> C.verify x w := by
  intro fuel
  induction fuel with
  | zero =>
      intro x w h
      by_cases hd : C.decider x = true
      · have hterm : C.terminal x = some w := by
          simpa [searchFuel, hd] using h
        exact C.terminal_sound hterm
      · have hdf : C.decider x = false := by
          cases hdec : C.decider x <;> simp_all
        simp [searchFuel, hdf] at h
  | succ n ih =>
      intro x w h
      by_cases hd : C.decider x = true
      · by_cases hr0 : C.rank x = 0
        · have hterm : C.terminal x = some w := by
            simpa [searchFuel, hd, hr0] using h
          exact C.terminal_sound hterm
        · by_cases hl : C.decider (C.left x) = true
          · have hleft : C.searchFuel n (C.left x) = some w := by
              simpa [searchFuel, hd, hr0, hl] using h
            exact C.left_sound (ih (C.left x) w hleft)
          · have hlf : C.decider (C.left x) = false := by
              cases hdec : C.decider (C.left x) <;> simp_all
            have hright : C.searchFuel n (C.right x) = some w := by
              simpa [searchFuel, hd, hr0, hlf] using h
            exact C.right_sound (ih (C.right x) w hright)
      · have hdf : C.decider x = false := by
          cases hdec : C.decider x <;> simp_all
        simp [searchFuel, hdf] at h

/-- If a child rank is strictly below a node rank and the node rank fits in
`n+1`, then the child rank fits in `n`. -/
private theorem child_rank_le_pred
    {a b n : Nat} (hlt : a < b) (hle : b ≤ n + 1) : a ≤ n := by
  exact Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hle)

/-- THEOREM 2: enough fuel plus an existential verifier witness makes
`searchFuel` emit a verified witness. -/
theorem searchFuel_complete :
    ∀ fuel x, C.rank x ≤ fuel -> (∃ w : Witness, C.verify x w) ->
      ∃ w : Witness, C.searchFuel fuel x = some w ∧ C.verify x w := by
  intro fuel
  induction fuel with
  | zero =>
      intro x hbudget hex
      have hr0 : C.rank x = 0 := Nat.eq_zero_of_le_zero hbudget
      have hd : C.decider x = true := (C.decider_correct x).mpr hex
      rcases C.terminal_complete hr0 hex with ⟨w, hterm, hv⟩
      exact ⟨w, by simp [searchFuel, hd, hterm], hv⟩
  | succ n ih =>
      intro x hbudget hex
      have hd : C.decider x = true := (C.decider_correct x).mpr hex
      by_cases hr0 : C.rank x = 0
      · rcases C.terminal_complete hr0 hex with ⟨w, hterm, hv⟩
        exact ⟨w, by simp [searchFuel, hd, hr0, hterm], hv⟩
      · have hpos : 0 < C.rank x := Nat.pos_of_ne_zero hr0
        by_cases hl : C.decider (C.left x) = true
        · have hleft_exists :
              ∃ w : Witness, C.verify (C.left x) w :=
            (C.decider_correct (C.left x)).mp hl
          have hleft_budget : C.rank (C.left x) ≤ n :=
            child_rank_le_pred (C.rank_left_lt hpos) hbudget
          rcases ih (C.left x) hleft_budget hleft_exists with
            ⟨w, hsearch, hv⟩
          exact
            ⟨w, by simp [searchFuel, hd, hr0, hl, hsearch],
              C.left_sound hv⟩
        · have hlf : C.decider (C.left x) = false := by
            cases hdec : C.decider (C.left x) <;> simp_all
          have hleft_no :
              ¬ ∃ w : Witness, C.verify (C.left x) w := by
            intro hleft
            have htrue : C.decider (C.left x) = true :=
              (C.decider_correct (C.left x)).mpr hleft
            simp [hlf] at htrue
          have hright_exists :
              ∃ w : Witness, C.verify (C.right x) w := by
            rcases C.child_complete hpos hex with hleft | hright
            · exact False.elim (hleft_no hleft)
            · exact hright
          have hright_budget : C.rank (C.right x) ≤ n :=
            child_rank_le_pred (C.rank_right_lt hpos) hbudget
          rcases ih (C.right x) hright_budget hright_exists with
            ⟨w, hsearch, hv⟩
          exact
            ⟨w, by simp [searchFuel, hd, hr0, hlf, hsearch],
              C.right_sound hv⟩

/-- The self-reduction producer: search with exactly the node rank as fuel. -/
def producer (x : Node) : Option Witness :=
  C.searchFuel (C.rank x) x

/-- THEOREM 3: the self-reduction producer is sound. -/
theorem producer_sound
    {x : Node} {w : Witness} (h : C.producer x = some w) :
    C.verify x w := by
  exact C.searchFuel_sound (C.rank x) x w h

/-- THEOREM 4: the self-reduction producer is complete. -/
theorem producer_complete
    {x : Node} (h : ∃ w : Witness, C.verify x w) :
    ∃ w : Witness, C.producer x = some w := by
  rcases C.searchFuel_complete (C.rank x) x (le_rfl) h with ⟨w, hw, _hv⟩
  exact ⟨w, hw⟩

/-- THEOREM 5: every binary self-reduction compiles to the P684 producer
projection. -/
def toWitnessProducerProjection :
    WitnessProducerProjection Node Witness where
  verify := C.verify
  producer := C.producer
  sound := by
    intro x w h
    exact C.producer_sound h
  complete := by
    intro x h
    exact C.producer_complete h

/-- THEOREM 6: therefore self-reduction collapses search and verification in
the precise P684 sense. -/
theorem producedVerifiedWitness_iff_hasWitness (x : Node) :
    (C.toWitnessProducerProjection).ProducedVerifiedWitness x ↔
      (C.toWitnessProducerProjection).HasWitness x :=
  C.toWitnessProducerProjection.producedVerifiedWitness_iff_hasWitness x

/-- THEOREM 7: decision false at the root means the self-reduction producer
returns no witness. -/
theorem producer_none_of_decider_false
    {x : Node} (h : C.decider x = false) :
    C.producer x = none := by
  have hno : ¬ (C.toWitnessProducerProjection).HasWitness x := by
    intro hex
    have htrue : C.decider x = true := (C.decider_correct x).mpr hex
    simp [h] at htrue
  exact
    (C.toWitnessProducerProjection.producer_none_iff_noWitness x).mpr hno

/-- THEOREM 8: decision true at the root makes the producer emit a verified
witness. -/
theorem exists_produced_verified_of_decider_true
    {x : Node} (h : C.decider x = true) :
    (C.toWitnessProducerProjection).ProducedVerifiedWitness x := by
  have hex : (C.toWitnessProducerProjection).HasWitness x :=
    (C.decider_correct x).mp h
  exact
    (C.toWitnessProducerProjection.producedVerifiedWitness_iff_hasWitness x).mpr
      hex

end BinarySelfReduction

/-! ## Packaged certificate -/

/-- P685 certificate: the self-reduction data is an upstream producer for the
P684 search/verification-collapse projection. -/
structure SelfReductionProducerProjectionCertificate where
  p684_projection_collapse :
    ProducerProjectionCollapseCertificate.{u, v}
  to_witness_projection :
    ∀ {Node : Type u} {Witness : Type v}
      (_ : BinarySelfReduction Node Witness),
      WitnessProducerProjection Node Witness
  producer_sound :
    ∀ {Node : Type u} {Witness : Type v}
      (C : BinarySelfReduction Node Witness) {x : Node} {w : Witness},
      C.producer x = some w -> C.verify x w
  producer_complete :
    ∀ {Node : Type u} {Witness : Type v}
      (C : BinarySelfReduction Node Witness) {x : Node},
      (∃ w : Witness, C.verify x w) -> ∃ w : Witness, C.producer x = some w
  search_verification_collapse :
    ∀ {Node : Type u} {Witness : Type v}
      (C : BinarySelfReduction Node Witness) (x : Node),
      (C.toWitnessProducerProjection).ProducedVerifiedWitness x ↔
        (C.toWitnessProducerProjection).HasWitness x

/-- DEFINITION 1: canonical self-reduction producer-projection certificate. -/
def selfReductionProducerProjectionCertificate :
    SelfReductionProducerProjectionCertificate.{u, v} where
  p684_projection_collapse := producerProjectionCollapseCertificate
  to_witness_projection := by
    intro Node Witness C
    exact C.toWitnessProducerProjection
  producer_sound := by
    intro Node Witness C x w h
    exact C.producer_sound h
  producer_complete := by
    intro Node Witness C x h
    exact C.producer_complete h
  search_verification_collapse := by
    intro Node Witness C x
    exact C.producedVerifiedWitness_iff_hasWitness x

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

universe u v w

/-- P685 grand root: P684's producer projection plus the upstream
self-reduction theorem that constructs such a producer from a correct binary
decision oracle.

This is the formal "decision projection can generate the witness producer"
bridge.  It is still not a `P = NP` theorem; the concrete SAT instantiation and
polynomial bound remain the next producer obligations.
-/
structure SelfReductionProducerUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p684_root :
    ProducerProjectionUnifiedRootCertificate.{u, v, w} E
  self_reduction_producer :
    SelfReductionProducerProjectionCertificate.{v, w}

/-- THEOREM 10: the self-reduction producer unified root is inhabited. -/
def selfReductionProducerUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    SelfReductionProducerUnifiedRootCertificate.{u, v, w} E where
  p684_root := producerProjectionUnifiedRootCertificate (E := E)
  self_reduction_producer :=
    selfReductionProducerProjectionCertificate

end GrandUnification

end SaturationMonoid
