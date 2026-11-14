import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Action
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory CategoryTheory.Limits

variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]

/-- For compatible observations of a fixed finite inventory, one stage reads the entire inverse fibre. -/
theorem finite_inventory_fibre {A : Type u} (inventory : Finset A) (read : Nat → A → Prop)
    (compatible : ∀ ⦃lower upper : Nat⦄, lower ≤ upper → ∀ source : A, read upper source → read lower source) :
    ∃ base : Nat, ∀ stage ≥ base, ∀ source ∈ inventory, read stage source ↔ ∀ address, read address source := by
  classical
  let remaining := fun stage => inventory.filter (read stage)
  have shrink {lower upper : Nat} (edge : lower ≤ upper) : remaining upper ⊆ remaining lower := by
    intro source selected
    have visible := Finset.mem_filter.mp selected
    exact Finset.mem_filter.mpr ⟨visible.1, compatible edge source visible.2⟩
  let sizeSeen := fun size : Nat => ∃ stage : Nat, (remaining stage).card = size
  have existsSize : ∃ size, sizeSeen size := ⟨(remaining 0).card, 0, rfl⟩
  obtain ⟨least, leastSize⟩ := Nat.find_spec existsSize
  have stationary (stage : Nat) (later : least ≤ stage) : remaining stage = remaining least := by
    have smallest := Nat.find_min' existsSize (show sizeSeen (remaining stage).card from ⟨stage, rfl⟩)
    exact Finset.eq_of_subset_of_card_le (shrink later) (leastSize.le.trans smallest)
  refine ⟨least, fun stage later source stocked => ⟨?_, fun all => all stage⟩⟩
  intro wrote address
  have kept : source ∈ remaining stage := Finset.mem_filter.mpr ⟨stocked, wrote⟩
  have atLeast : source ∈ remaining least := stationary stage later ▸ kept
  let common := max least address
  have atCommon : source ∈ remaining common := (stationary common (le_max_left _ _)).symm ▸ atLeast
  exact (Finset.mem_filter.mp (shrink (le_max_right least address) atCommon)).2

/-- The entire inverse fibre in the original finite inventory is read by the actual factorial restriction. -/
theorem factorial_integral_inventory_fibre (inventory : Finset L) (value : FactorialCompletion (L := L)) :
    ∃ base : Nat, ∀ stage ≥ base, ∀ source ∈ inventory,
      modulusProjection (factorialModulus stage) source = (factorialRestriction (L := L) stage).hom value ↔
        factorialCanonicalMap source = value := by
  let read := fun stage (source : L) => modulusProjection (factorialModulus stage) source =
    (factorialRestriction (L := L) stage).hom value
  have compatible {lower upper : Nat} (edge : lower ≤ upper) (source : L) (selected : read upper source) :
      read lower source := by
    let restrict := (factorialTower (L := L)).map (homOfLE edge).op
    have coherent := ConcreteCategory.congr_hom (limit.w (factorialTower (L := L)) (homOfLE edge).op) value
    exact (factorial_edge_projection edge source).symm.trans ((congrArg restrict.hom selected).trans coherent)
  obtain ⟨base, stable⟩ := finite_inventory_fibre inventory read
    (fun {lower upper} edge source selected => compatible (lower := lower) (upper := upper) edge source selected)
  refine ⟨base, fun stage later source stocked => ⟨?_, ?_⟩⟩
  · intro wrote
    have all := (stable stage later source stocked).1 wrote
    apply Concrete.limit_ext (factorialTower (L := L))
    rintro ⟨address⟩
    exact (factorial_canonical_restriction address source).trans (all address)
  · intro wrote
    exact (factorial_canonical_restriction stage source).symm.trans
      (congrArg (factorialRestriction (L := L) stage).hom wrote)

/-- Tail representatives in the same finite inventory give one original source for the whole class. -/
theorem factorial_integral_inventory_iff (inventory : Finset L) (value : FactorialCompletion (L := L)) :
    (∃ source ∈ inventory, factorialCanonicalMap source = value) ↔
      ∃ base : Nat, ∀ stage ≥ base, ∃ source ∈ inventory,
        modulusProjection (factorialModulus stage) source = (factorialRestriction (L := L) stage).hom value := by
  constructor
  · rintro ⟨source, stocked, writes⟩
    exact ⟨0, fun stage _ => ⟨source, stocked, (factorial_canonical_restriction stage source).symm.trans
      (congrArg (factorialRestriction (L := L) stage).hom writes)⟩⟩
  · rintro ⟨base, each⟩
    obtain ⟨least, fibre⟩ := factorial_integral_inventory_fibre inventory value
    let selected := max base least
    obtain ⟨source, stocked, wrote⟩ := each selected (le_max_left _ _)
    exact ⟨source, stocked, (fibre selected (le_max_right _ _) source stocked).1 wrote⟩

/-- The actual action preserves the original diagonal source, including every factorial coordinate. -/
theorem factorial_action_canonical (action : L →ₗ[ℤ] M) (source : L) :
    factorialCompletionAction action (factorialCanonicalMap source) = factorialCanonicalMap (action source) :=
  (congrArg (factorialCompletionAction action) (factorial_from_primes_canonical source).symm).trans
    ((factorial_from_primes_action action (allPrimeMap source)).trans
      ((congrArg factorialFromPrimes (allPrime_successor_source action source)).trans
        (factorial_from_primes_canonical (action source))))

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
