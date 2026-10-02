import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Coverage

/-! Common source material for a small family of complete rank materials.
The ranks are construction indices. Every original reader is retained on
its entire carrier, so every complete downstream output is unchanged. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMaterialJoin
open scoped Classical
noncomputable section
universe u v

variable {I : Type}

abbrev Total (ranks : I → Ordinal.{u}) : Type u := Σ index, MotherReceiptHigher.Base (ranks index)

def sharedRank (ranks : I → Ordinal.{u}) : Ordinal.{u} := MotherReceiptHigher.carrierRank (Total ranks)

def address (ranks : I → Ordinal.{u}) (index : I) :
    MotherReceiptHigher.Base (ranks index) ↪ MotherReceiptHigher.Base (sharedRank ranks) :=
  (Function.Embedding.sigmaMk index).trans (MotherReceiptHigher.carrierAddress (Total ranks))

def combine (ranks : I → Ordinal.{u}) (materials : (index : I) → MotherReceiptHigher.Material (ranks index)) :
    MotherReceiptHigher.Material (sharedRank ranks) :=
  (MotherReceiptHigher.readEquiv (sharedRank ranks)).symm
    (Function.extend (MotherReceiptHigher.carrierAddress (Total ranks))
      (fun point : Total ranks => MotherReceiptHigher.read (ranks point.1) (materials point.1) point.2) (fun _ => 0))

def restrict (ranks : I → Ordinal.{u}) (index : I)
    (material : MotherReceiptHigher.Material (sharedRank ranks)) : MotherReceiptHigher.Material (ranks index) :=
  (MotherReceiptHigher.readEquiv (ranks index)).symm
    (fun base => MotherReceiptHigher.read (sharedRank ranks) material (address ranks index base))

theorem combine_read (ranks : I → Ordinal.{u}) (materials : (index : I) → MotherReceiptHigher.Material (ranks index))
    (index : I) (base : MotherReceiptHigher.Base (ranks index)) :
    MotherReceiptHigher.read (sharedRank ranks) (combine ranks materials) (address ranks index base) =
      MotherReceiptHigher.read (ranks index) (materials index) base := by
  change MotherReceiptHigher.readEquiv (sharedRank ranks) ((MotherReceiptHigher.readEquiv (sharedRank ranks)).symm _) _ = _
  rw [Equiv.apply_symm_apply]
  exact (MotherReceiptHigher.carrierAddress (Total ranks)).injective.extend_apply _ _ ⟨index, base⟩

theorem restrict_combine (ranks : I → Ordinal.{u}) (materials : (index : I) → MotherReceiptHigher.Material (ranks index))
    (index : I) : restrict ranks index (combine ranks materials) = materials index := by
  apply (MotherReceiptHigher.read_uniformEmbedding (ranks index)).injective
  change MotherReceiptHigher.readEquiv (ranks index) ((MotherReceiptHigher.readEquiv (ranks index)).symm _) = _
  rw [Equiv.apply_symm_apply]
  funext base
  exact combine_read ranks materials index base

theorem whole_family_leftInverse (ranks : I → Ordinal.{u}) :
    Function.LeftInverse (fun material index => restrict ranks index material) (combine ranks) :=
  fun materials => funext (restrict_combine ranks materials)

/-- Arbitrary output universes are allowed: complete dependent source or
compiler records are recovered, not just finite observations of them. -/
theorem consumer_readback (ranks : I → Ordinal.{u})
    {Output : I → Sort v} (consumers : (index : I) → MotherReceiptHigher.Material (ranks index) → Output index)
    (materials : (index : I) → MotherReceiptHigher.Material (ranks index)) (index : I) :
    consumers index (restrict ranks index (combine ranks materials)) = consumers index (materials index) :=
  congrArg (consumers index) (restrict_combine ranks materials index)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMaterialJoin
