import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityFamilies.Factory

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityFamilies
open MotherInventoryAdmission MotherArenaNetwork
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}

theorem every_index (I : Type) (code : I ↪ MotherArenaHigher.Base rank) :
    ∃ domain : MotherArenaHigher.Material rank, Nonempty (I ≃ Member domain) := by
  obtain ⟨domain, readback⟩ := MotherArenaHigher.read_surjective rank
    (fun address _ => if ∃ index, code index = address then 0 else 1)
  have represented (address : MotherArenaHigher.Base rank) :
      bit domain 0 address ↔ ∃ index, code index = address := by
    simp only [bit, readback]
    by_cases present : ∃ index, code index = address <;> simp only [present, if_true, if_false, one_ne_zero, iff_self]
  exact ⟨domain, ⟨MotherArenaNetworkOrigin.imageEquiv code (bit domain 0) represented⟩⟩

structure Presentation (I : Type) (N : I → WorldRelationNetwork.{0})
    (V : I → ConstructiveRoot.Vocabulary.{0}) (roots : ∀ index, SourceNativeAuthoritativeRootClosure (N index) (V index))
    (value : FamilyValue rank) where
  index : I ≃ Member value.1
  root : ∀ point, MotherAuthorityRoot.Presentation (roots point)
    (value.2 (index point)).1.1 (value.2 (index point)).1.2 (value.2 (index point)).2

variable {I : Type} {N : I → WorldRelationNetwork.{0}} {V : I → ConstructiveRoot.Vocabulary.{0}}
    {roots : ∀ index, SourceNativeAuthoritativeRootClosure (N index) (V index)} {value : FamilyValue rank}

def Presentation.restrict (p : Presentation I N V roots value) :
    ∀ index, SourceNativeAuthoritativeRootClosure (N index) (V index) :=
  fun index => (p.root index).restrict

theorem Presentation.restrict_eq (p : Presentation I N V roots value) : p.restrict = roots :=
  funext (fun index => (p.root index).restrict_eq)

/-- The entire original root family is covered simultaneously. All child
operands are addressed at one rank before higher material formation. -/
theorem family_at_rank (I : Type) (N : I → WorldRelationNetwork.{0})
    (V : I → ConstructiveRoot.Vocabulary.{0}) (roots : ∀ index, SourceNativeAuthoritativeRootClosure (N index) (V index))
    (indexCode : I ↪ MotherArenaHigher.Base rank)
    (rootCode : (Σ index, MotherAuthorityRoot.AddressTotal (roots index)) ↪ MotherArenaHigher.Base rank) :
    ∃ material : MotherArenaHigher.Material rank, ∃ value : FamilyValue rank,
      formFamily material = some value ∧ Nonempty (Presentation I N V roots value) := by
  have allRoots : ∀ index, MotherAuthorityRoot.FormationAt rank (roots index) := fun index =>
    MotherAuthorityRoot.root_at_rank (N index) (V index) (roots index)
      ((Function.Embedding.sigmaMk index).trans rootCode)
  simp only [MotherAuthorityRoot.FormationAt] at allRoots
  choose materials values data surfaces presentations formed recovered original using allRoots
  obtain ⟨domain, ⟨indexMap⟩⟩ := every_index I indexCode
  let children : Member domain → Output := fun index =>
    ⟨⟨values (indexMap.symm index), data (indexMap.symm index)⟩, surfaces (indexMap.symm index)⟩
  obtain ⟨material, formedFamily⟩ := family_on_members domain children
    (fun index => materials (indexMap.symm index)) (fun index => formed (indexMap.symm index))
  refine ⟨material, ⟨domain, children⟩, formedFamily, ⟨{
    index := indexMap
    root := fun index => ?_ }⟩⟩
  change MotherAuthorityRoot.Presentation (roots index)
    (values (indexMap.symm (indexMap index))) (data (indexMap.symm (indexMap index)))
    (surfaces (indexMap.symm (indexMap index)))
  rw [indexMap.symm_apply_apply]
  exact presentations index

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityFamilies
