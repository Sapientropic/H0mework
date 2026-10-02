import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeAuthority.Generation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace MotherNativeAuthority

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}

/-- The original emitted event's complete source inventory, without a row or authority argument. -/
abbrev InventoryAt (root : SourceNativeLivingRootClosure N V) (current : V.Current) :=
  root.toAuthoritativeRoot.toLedgerRoot.source.source.law.AffectedInventoryAt
    (root.emitted current).2

def inventoryPresentation (root : SourceNativeLivingRootClosure N V) (current : V.Current) :
    ConstructivePresentation (InventoryAt root current) (EntryAt root current) :=
  root.toAuthoritativeRoot.toLedgerRoot.toInventoryRoot.affectedInventoryPresentation current

def entryFromInventory (root : SourceNativeLivingRootClosure N V) (current : V.Current)
    (material : InventoryAt root current) : EntryAt root current :=
  (inventoryPresentation root current).forward material

theorem every_entry_from_inventory (root : SourceNativeLivingRootClosure N V) (current : V.Current)
    (entry : EntryAt root current) :
    ∃ material : InventoryAt root current, entryFromInventory root current material = entry :=
  ⟨(inventoryPresentation root current).backward entry,
    (inventoryPresentation root current).forward_backward entry⟩

theorem inventory_material_preserved (root : SourceNativeLivingRootClosure N V) (current : V.Current)
    (material : InventoryAt root current) :
    (inventoryPresentation root current).backward (entryFromInventory root current material) =
      material :=
  (inventoryPresentation root current).backward_forward material

/-- The cofinal-target inventory is indexed by the source's own emitted event. -/
def CofinalInventory (root : SourceNativeLivingRootClosure N V) : Type u :=
  match V.cofinal.emit? with
  | none => PEmpty
  | some event => InventoryAt root (V.cofinal.target event)

def cofinalInventoryPresentation (root : SourceNativeLivingRootClosure N V) :
    ConstructivePresentation (CofinalInventory root) (CofinalEntry root) := by
  unfold CofinalInventory CofinalEntry
  split
  · rename_i absent
    rw [absent]
    exact .refl PEmpty
  · rename_i event emitted
    rw [emitted]
    exact inventoryPresentation root (V.cofinal.target event)

def entryFromCofinalInventory (root : SourceNativeLivingRootClosure N V)
    (material : CofinalInventory root) : CofinalEntry root :=
  (cofinalInventoryPresentation root).forward material

theorem every_cofinalEntry_from_inventory (root : SourceNativeLivingRootClosure N V)
    (entry : CofinalEntry root) :
    ∃ material : CofinalInventory root, entryFromCofinalInventory root material = entry :=
  ⟨(cofinalInventoryPresentation root).backward entry,
    (cofinalInventoryPresentation root).forward_backward entry⟩

inductive InventorySeed (root : SourceNativeLivingRootClosure N V) : Type u
  | initial (material : InventoryAt root root.toAuthoritativeRoot.toRoot.source.initial)
  | cofinal (material : CofinalInventory root)

def seedFromInventory (root : SourceNativeLivingRootClosure N V) : InventorySeed root → Seed root
  | .initial material =>
      .initial (entryFromInventory root root.toAuthoritativeRoot.toRoot.source.initial material)
  | .cofinal material => .cofinal (entryFromCofinalInventory root material)

theorem every_seed_from_inventory (root : SourceNativeLivingRootClosure N V) (seed : Seed root) :
    ∃ material : InventorySeed root, seedFromInventory root material = seed := by
  cases seed with
  | initial entry =>
      obtain ⟨material, formed⟩ := every_entry_from_inventory root
        root.toAuthoritativeRoot.toRoot.source.initial entry
      exact ⟨.initial material, congrArg Seed.initial formed⟩
  | cofinal entry =>
      obtain ⟨material, formed⟩ := every_cofinalEntry_from_inventory root entry
      exact ⟨.cofinal material, congrArg Seed.cofinal formed⟩

/-- The actual source inventory now feeds the original complete-authority formation chain. -/
noncomputable def formFromInventory (root : SourceNativeLivingRootClosure N V)
    (material : InventorySeed root) (steps : Nat) : Option (AuthorityState root) :=
  formAuthority root (seedFromInventory root material) steps

theorem every_authority_from_inventory (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (authority : AuthorityTotal root visit) :
    ∃ material : InventorySeed root, ∃ steps : Nat,
      formFromInventory root material steps = some ⟨visit, authority⟩ := by
  obtain ⟨seed, steps, generated⟩ := every_authority root visit authority
  obtain ⟨material, formed⟩ := every_seed_from_inventory root seed
  refine ⟨material, steps, ?_⟩
  exact (congrArg (fun input => formAuthority root input steps) formed).trans generated

end MotherNativeAuthority
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
