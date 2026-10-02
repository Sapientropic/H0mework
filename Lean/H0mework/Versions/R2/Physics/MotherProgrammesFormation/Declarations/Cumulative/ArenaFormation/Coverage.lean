import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaFormation.Higher
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.Declarations.ArenaAddressCoverage

/-! Common source-law addresses and exact retention of the original whole
higher material. This supplies arena operands; the fixed-B source factory
still needs its parametric instance before using these addresses. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaHigher
open MotherNetworkFactory
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

def carrierRank (A : Type) : Ordinal.{0} := Order.succ (MotherArenaAddressCoverage.bound A)

def carrierAddress (A : Type) : A ↪ Base (carrierRank A) where
  toFun := fun value => point (carrierRank A) (.inr (MotherArenaAddressCoverage.carrierAddress A value))
  inj' := fun _ _ same => (MotherArenaAddressCoverage.carrierAddress A).injective
    (Sum.inr.inj (point_injective (carrierRank A) same))

theorem every_carrier (A : Type) : ∃ rank : Ordinal.{0}, Nonempty (A ↪ Base rank) :=
  ⟨carrierRank A, ⟨carrierAddress A⟩⟩

def includeOriginal (rank : Ordinal.{0}) (address : B ↪ Base rank) (material : M) : Material rank :=
  (readEquiv rank).symm
    (Function.extend address (MotherHigherLawFormation.read material) (fun _ => 0))

theorem includeOriginal_read (rank : Ordinal.{0}) (address : B ↪ Base rank) (material : M) (base : B) :
    read rank (includeOriginal rank address material) (address base) = MotherHigherLawFormation.read material base := by
  change readEquiv rank ((readEquiv rank).symm _) (address base) = _
  rw [Equiv.apply_symm_apply]
  exact address.injective.extend_apply _ _ base

def restrictOriginal (rank : Ordinal.{0}) (address : B ↪ Base rank) (material : Material rank) : M :=
  (MotherHigherLawFormation.read_surjective (fun base => read rank material (address base))).choose

theorem restrictOriginal_read (rank : Ordinal.{0}) (address : B ↪ Base rank) (material : Material rank) :
    MotherHigherLawFormation.read (restrictOriginal rank address material) = fun base => read rank material (address base) :=
  (MotherHigherLawFormation.read_surjective _).choose_spec

theorem restrict_includeOriginal (rank : Ordinal.{0}) (address : B ↪ Base rank) (material : M) :
    restrictOriginal rank address (includeOriginal rank address material) = material := by
  apply MotherHigherLawFormation.read_uniformEmbedding.injective
  rw [restrictOriginal_read]
  funext base
  exact includeOriginal_read rank address material base

def originalMaterialEmbedding (rank : Ordinal.{0}) (address : B ↪ Base rank) : M ↪ Material rank where
  toFun := includeOriginal rank address
  inj' := fun first last same =>
    (restrict_includeOriginal rank address first).symm.trans
      ((congrArg (restrictOriginal rank address) same).trans (restrict_includeOriginal rank address last))

abbrev JointRootAddress {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (root : SourceNativeAuthoritativeRootClosure N V) := MotherArenaAddressCoverage.RootAddressTotal root ⊕ B

/-- One arena simultaneously covers the four actual factory operands and
retains every complete original material by an exact left inverse. -/
theorem root_addresses_and_original_material
    {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (root : SourceNativeAuthoritativeRootClosure N V) :
    ∃ rank : Ordinal.{0}, ∃ _rootAddress : MotherArenaAddressCoverage.RootAddressTotal root ↪ Base rank,
      ∃ originalAddress : B ↪ Base rank,
        Function.LeftInverse (restrictOriginal rank originalAddress) (includeOriginal rank originalAddress) := by
  let rank := carrierRank (JointRootAddress root)
  let shared := carrierAddress (JointRootAddress root)
  let rootAddress : MotherArenaAddressCoverage.RootAddressTotal root ↪ Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let originalAddress : B ↪ Base rank :=
    ⟨fun value => shared (.inr value), fun _ _ same => Sum.inr.inj (shared.injective same)⟩
  exact ⟨rank, rootAddress, originalAddress, restrict_includeOriginal rank originalAddress⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaHigher
