import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeAuthority.Inventory
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-! Complete entry-and-authority sections from finite original-inventory
programmes. Root, visit and the query domain remain fixed source indices;
this relative formation does not establish their mother-source provenance. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace MotherNativeAuthority

open Set UniformSpace
open scoped Classical Topology

universe u v

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}

noncomputable section

def formAtVisit (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (seed : InventorySeed root) (steps : Nat) : Option (AuthorityTotal root visit) :=
  (formFromInventory root seed steps).bind fun generated =>
    if same : generated.1 = visit then some (same ▸ generated.2) else none

theorem every_authority_at_visit (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (authority : AuthorityTotal root visit) :
    ∃ seed : InventorySeed root, ∃ steps : Nat,
      formAtVisit root visit seed steps = some authority := by
  obtain ⟨seed, steps, formed⟩ := every_authority_from_inventory root visit authority
  refine ⟨seed, steps, ?_⟩
  unfold formAtVisit
  rw [formed]
  simp

namespace Section

variable (root : SourceNativeLivingRootClosure N V)
  (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
  (Query : Type v)

abbrev Programme := List (Query × Option (InventorySeed root × Nat))

def finite : Programme root Query → Query → Option (AuthorityTotal root visit)
  | [], _ => none
  | (key, material) :: tail, query =>
      if query = key then material.bind (fun input => formAtVisit root visit input.1 input.2)
      else finite tail query

theorem finite_assignment (keys : Finset Query) (target : Query → Option (AuthorityTotal root visit)) :
    ∃ programme : Programme root Query, ∀ key ∈ keys, finite root visit Query programme key = target key := by
  classical
  induction keys using Finset.induction_on with
  | empty => exact ⟨[], fun _ impossible => nomatch impossible⟩
  | @insert key keys fresh ih =>
      obtain ⟨tail, tailExact⟩ := ih
      have material : ∃ input : Option (InventorySeed root × Nat),
          input.bind (fun value => formAtVisit root visit value.1 value.2) = target key := by
        cases same : target key with
        | none => exact ⟨none, rfl⟩
        | some authority =>
            obtain ⟨seed, steps, formed⟩ := every_authority_at_visit root visit authority
            exact ⟨some (seed, steps), formed⟩
      obtain ⟨input, inputExact⟩ := material
      refine ⟨(key, input) :: tail, fun query inside => ?_⟩
      rcases Finset.mem_insert.mp inside with same | prior
      · subst query
        exact (if_pos rfl).trans inputExact
      · have different : query ≠ key := fun same => fresh (same ▸ prior)
        exact (if_neg different).trans (tailExact query prior)

local instance : UniformSpace (Option (AuthorityTotal root visit)) := ⊥

theorem finite_dense : DenseRange (finite root visit Query) := by
  intro target
  rw [mem_closure_iff]
  intro neighborhood openNeighborhood contains
  obtain ⟨keys, fibers, localNeighborhood, contained⟩ :=
    isOpen_pi_iff.mp openNeighborhood target contains
  obtain ⟨programme, formed⟩ := finite_assignment root visit Query keys target
  refine ⟨finite root visit Query programme, contained ?_, ⟨programme, rfl⟩⟩
  intro key inside
  rw [formed key inside]
  exact (localNeighborhood key inside).2

abbrev Raw := Set.range (finite root visit Query)
abbrev Formed := Completion (Raw root visit Query)

def read : Formed root visit Query → (Query → Option (AuthorityTotal root visit)) :=
  Completion.extension Subtype.val

theorem read_coe (raw : Raw root visit Query) :
    read root visit Query (raw : Formed root visit Query) = raw.val :=
  Completion.extension_coe uniformContinuous_subtype_val raw

theorem read_uniformEmbedding : IsUniformEmbedding (read root visit Query) :=
  (Completion.isUniformInducing_extension
    isUniformEmbedding_subtype_val.isUniformInducing).isUniformEmbedding

theorem read_surjective : Function.Surjective (read root visit Query) := by
  have included : Set.range (finite root visit Query) ⊆ Set.range (read root visit Query) := by
    rintro _ ⟨programme, rfl⟩
    let raw : Raw root visit Query := ⟨finite root visit Query programme, ⟨programme, rfl⟩⟩
    exact ⟨(raw : Formed root visit Query), read_coe root visit Query raw⟩
  have closed := (read_uniformEmbedding root visit Query).isClosedEmbedding.isClosed_range
  intro target
  exact closure_minimal included closed (finite_dense root visit Query target)

def form (material : Formed root visit Query) : Option (Query → AuthorityTotal root visit) :=
  if total : ∀ query, ∃ authority, read root visit Query material query = some authority then
    some (fun query => (total query).choose)
  else none

theorem form_sound (material : Formed root visit Query)
    (section_ : Query → AuthorityTotal root visit)
    (formed : form root visit Query material = some section_) :
    ∀ query, read root visit Query material query = some (section_ query) := by
  unfold form at formed
  split at formed
  · rename_i total
    have same := Option.some.inj formed
    intro query
    exact (total query).choose_spec.trans (congrArg some (congrFun same query))
  · cases formed

theorem every_section (target : Query → AuthorityTotal root visit) :
    ∃ material : Formed root visit Query,
      (∀ query, read root visit Query material query = some (target query)) ∧
      form root visit Query material = some target := by
  obtain ⟨material, formed⟩ := read_surjective root visit Query (fun query => some (target query))
  have total : ∀ query, ∃ authority, read root visit Query material query = some authority :=
    fun query => ⟨target query, congrFun formed query⟩
  refine ⟨material, congrFun formed, ?_⟩
  unfold form
  rw [dif_pos total]
  apply congrArg some
  funext query
  exact Option.some.inj ((total query).choose_spec.symm.trans (congrFun formed query))

end Section
end
end MotherNativeAuthority
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
