import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationReception
import Mathlib.Data.Finset.Union

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeviationBudget

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def labelFor (key : Fin source.code.sites)
    (request : Request Party Good Port (Mandate.State Party Technology) Instrument) : Option (Scope × Bool) :=
  if request.signer = source.code.siteParty key then vocabulary.decode request.purpose else none

def labelsAt (n : Nat) (key : Fin source.code.sites) : List (Scope × Bool) :=
  (source.code.action protocol.work.val key
    ((AttestationTransport.state source input cut protocol rival n).frame.inbox key)).filterMap
      (labelFor source vocabulary key)

/-- Potential conflicting output of the actual selected work word. Admission
and resource failure still determine which of these labels become ballots. -/
def contradictory (labels : List (Scope × Bool)) : Bool :=
  (labels.product labels).any fun pair => decide (pair.1.1 = pair.2.1 ∧ pair.1.2 ≠ pair.2.2)

theorem contradictory_iff (labels : List (Scope × Bool)) : contradictory labels = true ↔
    ∃ one ∈ labels, ∃ two ∈ labels, one.1 = two.1 ∧ one.2 ≠ two.2 := by
  simp only [contradictory, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨one, two⟩, inside, conflict⟩
    obtain ⟨first, second⟩ := List.mem_product.mp inside
    exact ⟨one, first, two, second, conflict⟩
  · rintro ⟨one, first, two, second, conflict⟩
    exact ⟨(one, two), List.mem_product.mpr ⟨first, second⟩, conflict⟩

/-- The safety budget tracks changes in the actual selected output capability.
Control, admission and resource facts are still checked by the owned producer. -/
abbrev viewAt (n : Nat) (key : Fin source.code.sites) : List (Scope × Bool) :=
  labelsAt source input cut protocol rival vocabulary n key

def changesAt (n : Nat) : Finset (Fin source.code.sites) :=
  Finset.univ.filter fun key => viewAt source input cut protocol rival vocabulary n key ≠
    viewAt source input cut protocol rival vocabulary (n + 1) key

def hazardsAt (n : Nat) : Finset (Fin source.code.sites) :=
  Finset.univ.filter fun key => OwnedAttestation.owner source input cut protocol rival n = some key ∧
    contradictory (labelsAt source input cut protocol rival vocabulary n key) = true

def affectedThrough (horizon : Nat) : Finset (Fin source.code.sites) :=
  (Finset.range horizon).biUnion fun n =>
    changesAt source input cut protocol rival vocabulary n ∪ hazardsAt source input cut protocol rival vocabulary n

def budget (horizon : Nat) : Nat :=
  (affectedThrough source input cut protocol rival vocabulary horizon).card

theorem affected_iff_source_change_or_actual_work_hazard (horizon : Nat) (key : Fin source.code.sites) :
    key ∈ affectedThrough source input cut protocol rival vocabulary horizon ↔
      ∃ n < horizon,
        viewAt source input cut protocol rival vocabulary n key ≠
          viewAt source input cut protocol rival vocabulary (n + 1) key ∨
        (OwnedAttestation.owner source input cut protocol rival n = some key ∧
          contradictory (labelsAt source input cut protocol rival vocabulary n key) = true) := by
  simp [affectedThrough, changesAt, hazardsAt]

theorem unaffected_view_is_constant (horizon : Nat) (key : Fin source.code.sites)
    (unaffected : key ∉ affectedThrough source input cut protocol rival vocabulary horizon)
    (n : Nat) (bounded : n ≤ horizon) :
    viewAt source input cut protocol rival vocabulary n key =
      viewAt source input cut protocol rival vocabulary 0 key := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have same : viewAt source input cut protocol rival vocabulary n key =
        viewAt source input cut protocol rival vocabulary (n + 1) key := by
      by_contra different
      exact unaffected ((affected_iff_source_change_or_actual_work_hazard source input cut protocol rival vocabulary horizon key).mpr
        ⟨n, by omega, Or.inl different⟩)
    exact same.symm.trans (ih (by omega))

theorem issued_body_is_in_the_actual_local_word (n position : Nat) (body : OwnedAttestation.Ballot source)
    (issued : OwnedAttestation.issuedAt source input cut protocol rival vocabulary n position = some body) :
    OwnedAttestation.owner source input cut protocol rival n = some body.key ∧
      (body.scope, body.choice) ∈ labelsAt source input cut protocol rival vocabulary n body.key := by
  obtain ⟨site, item, owned, actual, _, signer, decoded, _, _, _, key, _⟩ :=
    OwnedAttestation.attested_has_owned_paid_origin source input cut protocol rival vocabulary n position body issued
  have empty := OwnedAttestation.owned_origin_has_no_preloaded_continuation source input cut protocol rival n site owned
  have word := OwnedAttestation.owned_activation_is_actual_selected_local_work source input cut protocol rival empty n site owned
  have requestIn : item.request ∈ (AttestationTransport.execution source input cut protocol rival n).submitted := by
    have requests := source.code.law.inventory_requests_exact
      (AttestationTransport.execution source input cut protocol rival n).before 0
      (AttestationTransport.execution source input cut protocol rival n).submitted
    rw [← requests]
    exact List.mem_map.mpr ⟨item, List.mem_of_getElem? actual, rfl⟩
  rw [word] at requestIn
  rw [key]
  refine ⟨owned, List.mem_filterMap.mpr ⟨item.request, requestIn, ?_⟩⟩
  simp only [labelFor, if_pos signer, decoded]

/-- The budget is generated before inspecting receiver certificates: conflicts
are covered by actual selected-label changes or a hazardous owned implementation word. -/
theorem authenticated_equivocation_is_covered (horizon : Nat)
    (one two : OwnedAttestation.Ballot source)
    (first : OwnedAttestation.verify source input cut protocol rival vocabulary one = true)
    (second : OwnedAttestation.verify source input cut protocol rival vocabulary two = true)
    (firstInside : one.cut < horizon) (secondInside : two.cut < horizon)
    (key : one.key = two.key) (scope : one.scope = two.scope) (different : one.choice ≠ two.choice) :
    one.key ∈ affectedThrough source input cut protocol rival vocabulary horizon := by
  obtain ⟨owned, firstLabel⟩ := issued_body_is_in_the_actual_local_word source input cut protocol rival vocabulary
    one.cut one.position one (of_decide_eq_true first)
  have secondLabel := (issued_body_is_in_the_actual_local_word source input cut protocol rival vocabulary
    two.cut two.position two (of_decide_eq_true second)).2
  rw [← key] at secondLabel
  by_contra unaffected
  have same := (unaffected_view_is_constant source input cut protocol rival vocabulary horizon one.key unaffected
    one.cut (by omega)).trans (unaffected_view_is_constant source input cut protocol rival vocabulary horizon one.key
      unaffected two.cut (by omega)).symm
  have labels : labelsAt source input cut protocol rival vocabulary one.cut one.key =
      labelsAt source input cut protocol rival vocabulary two.cut one.key := same
  have other : (one.scope, two.choice) ∈ labelsAt source input cut protocol rival vocabulary one.cut one.key := by
    rw [labels]
    simpa only [scope] using secondLabel
  have hazard := (contradictory_iff _).mpr ⟨(one.scope, one.choice), firstLabel,
    (one.scope, two.choice), other, rfl, different⟩
  exact unaffected ((affected_iff_source_change_or_actual_work_hazard source input cut protocol rival vocabulary horizon one.key).mpr
    ⟨one.cut, firstInside, Or.inr ⟨owned, hazard⟩⟩)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeviationBudget
