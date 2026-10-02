import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.MaterialJoin.Higher
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaFormation.Higher

/-! One source for complete high Receipt materials and low original arena
materials. All participating carriers choose the shared stage at once. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMaterialJoin.Mixed
open scoped Classical
noncomputable section
universe v w
variable {High Low : Type}

abbrev HighTotal (ranks : High → Ordinal.{3}) : Type 3 := Σ index, MotherReceiptHigher.Base (ranks index)
abbrev LowTotal (ranks : Low → Ordinal.{0}) := Σ index, MotherArenaHigher.Base (ranks index)
abbrev Total (high : High → Ordinal.{3}) (low : Low → Ordinal.{0}) : Type 3 :=
  HighTotal high ⊕ ULift.{3, 0} (LowTotal low)

def sharedRank (high : High → Ordinal.{3}) (low : Low → Ordinal.{0}) : Ordinal.{3} :=
  MotherReceiptHigher.carrierRank (Total high low)

def highAddress (high : High → Ordinal.{3}) (low : Low → Ordinal.{0}) (index : High) :
    MotherReceiptHigher.Base (high index) ↪ MotherReceiptHigher.Base (sharedRank high low) where
  toFun := fun base => MotherReceiptHigher.carrierAddress (Total high low) (.inl ⟨index, base⟩)
  inj' := by
    intro first last same
    have pointSame := Sum.inl.inj ((MotherReceiptHigher.carrierAddress (Total high low)).injective same)
    exact (Function.Embedding.sigmaMk index).injective pointSame

def lowAddress (high : High → Ordinal.{3}) (low : Low → Ordinal.{0}) (index : Low) :
    MotherArenaHigher.Base (low index) ↪ MotherReceiptHigher.Base (sharedRank high low) where
  toFun := fun base => MotherReceiptHigher.carrierAddress (Total high low) (.inr (ULift.up ⟨index, base⟩))
  inj' := by
    intro first last same
    have pointSame := congrArg ULift.down (Sum.inr.inj ((MotherReceiptHigher.carrierAddress (Total high low)).injective same))
    exact (Function.Embedding.sigmaMk index).injective pointSame

def combine (high : High → Ordinal.{3}) (low : Low → Ordinal.{0})
    (highMaterials : (index : High) → MotherReceiptHigher.Material (high index))
    (lowMaterials : (index : Low) → MotherArenaHigher.Material (low index)) :
    MotherReceiptHigher.Material (sharedRank high low) :=
  (MotherReceiptHigher.readEquiv (sharedRank high low)).symm
    (Function.extend (MotherReceiptHigher.carrierAddress (Total high low))
      (Sum.elim
        (fun point => MotherReceiptHigher.read (high point.1) (highMaterials point.1) point.2)
        (fun point => MotherArenaHigher.read (low point.down.1) (lowMaterials point.down.1) point.down.2)) (fun _ => 0))

def restrictHigh (high : High → Ordinal.{3}) (low : Low → Ordinal.{0}) (index : High)
    (material : MotherReceiptHigher.Material (sharedRank high low)) : MotherReceiptHigher.Material (high index) :=
  (MotherReceiptHigher.readEquiv (high index)).symm
    (fun base => MotherReceiptHigher.read (sharedRank high low) material (highAddress high low index base))

def restrictLow (high : High → Ordinal.{3}) (low : Low → Ordinal.{0}) (index : Low)
    (material : MotherReceiptHigher.Material (sharedRank high low)) : MotherArenaHigher.Material (low index) :=
  (MotherArenaHigher.readEquiv (low index)).symm
    (fun base => MotherReceiptHigher.read (sharedRank high low) material (lowAddress high low index base))

theorem high_read (high : High → Ordinal.{3}) (low : Low → Ordinal.{0})
    (highMaterials : (index : High) → MotherReceiptHigher.Material (high index))
    (lowMaterials : (index : Low) → MotherArenaHigher.Material (low index))
    (index : High) (base : MotherReceiptHigher.Base (high index)) :
    MotherReceiptHigher.read (sharedRank high low) (combine high low highMaterials lowMaterials)
      (highAddress high low index base) = MotherReceiptHigher.read (high index) (highMaterials index) base := by
  change MotherReceiptHigher.readEquiv (sharedRank high low) ((MotherReceiptHigher.readEquiv (sharedRank high low)).symm _) _ = _
  rw [Equiv.apply_symm_apply]
  exact (MotherReceiptHigher.carrierAddress (Total high low)).injective.extend_apply _ _ (.inl ⟨index, base⟩)

theorem low_read (high : High → Ordinal.{3}) (low : Low → Ordinal.{0})
    (highMaterials : (index : High) → MotherReceiptHigher.Material (high index))
    (lowMaterials : (index : Low) → MotherArenaHigher.Material (low index))
    (index : Low) (base : MotherArenaHigher.Base (low index)) :
    MotherReceiptHigher.read (sharedRank high low) (combine high low highMaterials lowMaterials)
      (lowAddress high low index base) = MotherArenaHigher.read (low index) (lowMaterials index) base := by
  change MotherReceiptHigher.readEquiv (sharedRank high low) ((MotherReceiptHigher.readEquiv (sharedRank high low)).symm _) _ = _
  rw [Equiv.apply_symm_apply]
  exact (MotherReceiptHigher.carrierAddress (Total high low)).injective.extend_apply _ _ (.inr (ULift.up ⟨index, base⟩))

theorem restrictHigh_combine (high : High → Ordinal.{3}) (low : Low → Ordinal.{0})
    (highMaterials : (index : High) → MotherReceiptHigher.Material (high index))
    (lowMaterials : (index : Low) → MotherArenaHigher.Material (low index)) (index : High) :
    restrictHigh high low index (combine high low highMaterials lowMaterials) = highMaterials index := by
  apply (MotherReceiptHigher.read_uniformEmbedding (high index)).injective
  change MotherReceiptHigher.readEquiv (high index) ((MotherReceiptHigher.readEquiv (high index)).symm _) = _
  rw [Equiv.apply_symm_apply]
  funext base
  exact high_read high low highMaterials lowMaterials index base

theorem restrictLow_combine (high : High → Ordinal.{3}) (low : Low → Ordinal.{0})
    (highMaterials : (index : High) → MotherReceiptHigher.Material (high index))
    (lowMaterials : (index : Low) → MotherArenaHigher.Material (low index)) (index : Low) :
    restrictLow high low index (combine high low highMaterials lowMaterials) = lowMaterials index := by
  apply (MotherArenaHigher.read_uniformEmbedding (low index)).injective
  change MotherArenaHigher.readEquiv (low index) ((MotherArenaHigher.readEquiv (low index)).symm _) = _
  rw [Equiv.apply_symm_apply]
  funext base
  exact low_read high low highMaterials lowMaterials index base

/-- Simultaneous preservation of the complete material spaces, for every
high and low input family and every reader coordinate. -/
theorem whole_family_leftInverse (high : High → Ordinal.{3}) (low : Low → Ordinal.{0}) :
    Function.LeftInverse
      (fun material => ((fun index => restrictHigh high low index material), (fun index => restrictLow high low index material)))
      (fun materials => combine high low materials.1 materials.2) := by
  intro materials
  exact Prod.ext (funext (restrictHigh_combine high low materials.1 materials.2))
    (funext (restrictLow_combine high low materials.1 materials.2))

theorem consumer_readback (high : High → Ordinal.{3}) (low : Low → Ordinal.{0})
    {HighOutput : High → Sort v} {LowOutput : Low → Sort w}
    (highConsumers : (index : High) → MotherReceiptHigher.Material (high index) → HighOutput index)
    (lowConsumers : (index : Low) → MotherArenaHigher.Material (low index) → LowOutput index)
    (highMaterials : (index : High) → MotherReceiptHigher.Material (high index))
    (lowMaterials : (index : Low) → MotherArenaHigher.Material (low index)) :
    (∀ index, highConsumers index (restrictHigh high low index (combine high low highMaterials lowMaterials)) =
      highConsumers index (highMaterials index)) ∧
    ∀ index, lowConsumers index (restrictLow high low index (combine high low highMaterials lowMaterials)) =
      lowConsumers index (lowMaterials index) :=
  ⟨fun index => congrArg (highConsumers index) (restrictHigh_combine high low highMaterials lowMaterials index),
    fun index => congrArg (lowConsumers index) (restrictLow_combine high low highMaterials lowMaterials index)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMaterialJoin.Mixed
