import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Higher
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Address
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.HigherLaw.Formation

/-! Common source-law addresses and exact retention of the original whole
higher material. This supplies arena operands; the fixed-B source factory
still needs its parametric instance before using these addresses. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptHigher
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section
universe u

local notation "B" => MotherHigherLawFormation.Base
local notation "M" => MotherHigherLawFormation.Formed

def carrierRank (A : Type u) : Ordinal.{u} := Order.succ (MotherReceiptAddress.bound A)

def carrierAddress (A : Type u) : A ↪ Base (carrierRank A) where
  toFun := fun value => point (carrierRank A) (.inr (MotherReceiptAddress.carrierAddress A value))
  inj' := fun _ _ same => (MotherReceiptAddress.carrierAddress A).injective
    (Sum.inr.inj (point_injective (carrierRank A) same))

theorem every_carrier (A : Type u) : ∃ rank : Ordinal.{u}, Nonempty (A ↪ Base rank) :=
  ⟨carrierRank A, ⟨carrierAddress A⟩⟩

def includeOriginal (rank : Ordinal.{u}) (address : B ↪ Base rank) (material : M) : Material rank :=
  (readEquiv rank).symm
    (Function.extend address (MotherHigherLawFormation.read material) (fun _ => 0))

theorem includeOriginal_read (rank : Ordinal.{u}) (address : B ↪ Base rank) (material : M) (base : B) :
    read rank (includeOriginal rank address material) (address base) = MotherHigherLawFormation.read material base := by
  change readEquiv rank ((readEquiv rank).symm _) (address base) = _
  rw [Equiv.apply_symm_apply]
  exact address.injective.extend_apply _ _ base

def restrictOriginal (rank : Ordinal.{u}) (address : B ↪ Base rank) (material : Material rank) : M :=
  (MotherHigherLawFormation.read_surjective (fun base => read rank material (address base))).choose

theorem restrictOriginal_read (rank : Ordinal.{u}) (address : B ↪ Base rank) (material : Material rank) :
    MotherHigherLawFormation.read (restrictOriginal rank address material) = fun base => read rank material (address base) :=
  (MotherHigherLawFormation.read_surjective _).choose_spec

theorem restrict_includeOriginal (rank : Ordinal.{u}) (address : B ↪ Base rank) (material : M) :
    restrictOriginal rank address (includeOriginal rank address material) = material := by
  apply MotherHigherLawFormation.read_uniformEmbedding.injective
  rw [restrictOriginal_read]
  funext base
  exact includeOriginal_read rank address material base

def originalMaterialEmbedding (rank : Ordinal.{u}) (address : B ↪ Base rank) : M ↪ Material rank where
  toFun := includeOriginal rank address
  inj' := fun first last same =>
    (restrict_includeOriginal rank address first).symm.trans
      ((congrArg (restrictOriginal rank address) same).trans (restrict_includeOriginal rank address last))

/-- Every receipt address and the entire original material space share one
sufficient stage; the latter is retained by an actual reader left inverse. -/
theorem carrier_and_original_material (A : Type u) :
    ∃ rank : Ordinal.{u}, ∃ _address : A ↪ Base rank,
      ∃ originalAddress : B ↪ Base rank,
        Function.LeftInverse (restrictOriginal rank originalAddress)
          (includeOriginal rank originalAddress) := by
  let Total := A ⊕ ULift.{u, 0} B
  let rank := carrierRank Total
  let shared := carrierAddress Total
  let address : A ↪ Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let originalAddress : B ↪ Base rank :=
    ⟨fun value => shared (.inr (ULift.up value)), fun _ _ same =>
      congrArg ULift.down (Sum.inr.inj (shared.injective same))⟩
  exact ⟨rank, address, originalAddress, restrict_includeOriginal rank originalAddress⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptHigher
