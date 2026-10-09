import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SpecNet
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Evaluate.Restrictions

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Contraction
open scoped Matrix BigOperators
noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

def blockNetQ (k : Sym2 Basis) : MatrixQ (BodyFiber k) (BodyFiber k) :=
  Spec.loadedNet.submatrix Subtype.val Subtype.val

def blockBodyQ (k : Sym2 Basis) : MatrixQ (BodyFiber k) (BodyFiber k) :=
  Spec.body.submatrix Subtype.val Subtype.val

def blockGainQ (k : Sym2 Basis) : ℚ := Spec.energyQ (blockNetQ k) (blockBodyQ k)

def supplyBlockQ (k : Sym2 Basis) : MatrixQ (FullFiber k) (FullFiber k) :=
  Spec.supply.submatrix Subtype.val Subtype.val

def pointerBlockQ (k : Sym2 Basis) : MatrixQ (PointerFiber k) (PointerFiber k) :=
  Spec.pointer.submatrix Subtype.val Subtype.val

def nineBlockQ (k : Sym2 Basis) : MatrixQ (PointerFiber k) (PointerFiber k) :=
  Spec.nine.submatrix Subtype.val Subtype.val

def elevenBlockQ (k : Sym2 Basis) : MatrixQ (PointerFiber k) (PointerFiber k) :=
  Spec.eleven.submatrix Subtype.val Subtype.val

def pcBlockQ (k : Sym2 Basis) : MatrixQ (PointerFiber k) (PointerFiber k) :=
  Spec.pcObservable.submatrix Subtype.val Subtype.val

def netBlockQ (k : Sym2 Basis) : MatrixQ (PointerFiber k) (PointerFiber k) :=
  qmultiply (qmultiply (qadjoint (elevenBlockQ k)) (pcBlockQ k)) (elevenBlockQ k) -
    qmultiply (qmultiply (qadjoint (nineBlockQ k)) (pcBlockQ k)) (nineBlockQ k)

def rootNetBlockQ (k : Sym2 Basis) : MatrixQ (PointerFiber k) (PointerFiber k) :=
  qmultiply (qmultiply (qadjoint (pointerBlockQ k)) (netBlockQ k)) (pointerBlockQ k)

def readoutBlockQ (k : Sym2 Basis) : MatrixQ (BodyFiber k) (BodyFiber k) :=
  (qmultiply (qmultiply (qadjoint (supplyBlockQ k))
    ((rootNetBlockQ k).submatrix (insertPointer k) (insertPointer k))) (supplyBlockQ k)).submatrix
      (insertDonor k) (insertDonor k)

def receivedBlockQ (k : Sym2 Basis) : MatrixQ (BodyFiber k) (BodyFiber k) :=
  Spec.receivedWord.submatrix Subtype.val Subtype.val

def inputBlockQ (k : Sym2 Basis) : MatrixQ (BodyFiber k) (BodyFiber k) :=
  Spec.bodyInput.submatrix Subtype.val Subtype.val

theorem supplyBlockQ_value (k : Sym2 Basis) : qvalue (supplyBlockQ k)=localSupply k := by
  rw [supplyBlockQ,qvalue_submatrix,Spec.supply_value]
  rfl

theorem pointerBlockQ_value (k : Sym2 Basis) : qvalue (pointerBlockQ k)=localPointer k := by
  rw [pointerBlockQ,qvalue_submatrix,Spec.pointer_value]
  rfl

theorem nineBlockQ_value (k : Sym2 Basis) : qvalue (nineBlockQ k)=localNine k := by
  rw [nineBlockQ,qvalue_submatrix,Spec.nine_value]
  rfl

theorem elevenBlockQ_value (k : Sym2 Basis) : qvalue (elevenBlockQ k)=localEleven k := by
  rw [elevenBlockQ,qvalue_submatrix,Spec.eleven_value]
  rfl

theorem pcBlockQ_value (k : Sym2 Basis) : qvalue (pcBlockQ k)=localPC k := by
  rw [pcBlockQ,qvalue_submatrix,Spec.pcObservable_value]
  rfl

theorem netBlockQ_value (k : Sym2 Basis) : qvalue (netBlockQ k)=localNet k := by
  rw [netBlockQ,qvalue_sub,qvalue_multiply,qvalue_multiply,qvalue_multiply,qvalue_multiply,
    qvalue_adjoint,qvalue_adjoint,elevenBlockQ_value,nineBlockQ_value,pcBlockQ_value]
  rw [localNet,Matrix.star_eq_conjTranspose,Matrix.star_eq_conjTranspose]

theorem rootNetBlockQ_value (k : Sym2 Basis) : qvalue (rootNetBlockQ k)=localRootNet k := by
  rw [rootNetBlockQ,qvalue_multiply,qvalue_multiply,qvalue_adjoint,
    pointerBlockQ_value,netBlockQ_value]
  rw [localRootNet,Matrix.star_eq_conjTranspose]

theorem readoutBlockQ_value (k : Sym2 Basis) : qvalue (readoutBlockQ k)=localReadout k := by
  rw [readoutBlockQ,qvalue_submatrix,qvalue_multiply,qvalue_multiply,qvalue_adjoint,
    qvalue_submatrix,supplyBlockQ_value,rootNetBlockQ_value]
  rw [localReadout,Matrix.star_eq_conjTranspose]

theorem receivedBlockQ_value (k : Sym2 Basis) : qvalue (receivedBlockQ k)=localReceivedWord k := by
  rw [receivedBlockQ,qvalue_submatrix,Spec.receivedWord_value]
  rfl

theorem inputBlockQ_value (k : Sym2 Basis) : qvalue (inputBlockQ k)=localBodyInput k := by
  rw [inputBlockQ,qvalue_submatrix,Spec.bodyInput_value]
  rfl

theorem blockNetQ_value (k : Sym2 Basis) : qvalue (blockNetQ k)=localReadout k := by
  rw [blockNetQ,qvalue_submatrix,Spec.loadedNet_value]
  exact local_readout_exact k

theorem blockBodyQ_value (k : Sym2 Basis) : qvalue (blockBodyQ k)=localBody k := by
  rw [blockBodyQ,qvalue_submatrix,Spec.body_value]
  exact local_body_exact k

theorem block_net_small (k : Sym2 Basis) : blockNetQ k=readoutBlockQ k := by
  apply Evaluate.qvalue_injective
  rw [blockNetQ_value,readoutBlockQ_value]

theorem block_body_small (k : Sym2 Basis) :
    blockBodyQ k=qmultiply (qmultiply (receivedBlockQ k) (inputBlockQ k))
      (qadjoint (receivedBlockQ k)) := by
  apply Evaluate.qvalue_injective
  rw [blockBodyQ_value,qvalue_multiply,qvalue_multiply,qvalue_adjoint,
    receivedBlockQ_value,inputBlockQ_value]
  rw [localBody,Matrix.star_eq_conjTranspose]

def smallGainQ (k : Sym2 Basis) : ℚ :=
  Spec.energyQ (readoutBlockQ k)
    (qmultiply (qmultiply (receivedBlockQ k) (inputBlockQ k)) (qadjoint (receivedBlockQ k)))

theorem block_gain_small (k : Sym2 Basis) : blockGainQ k=smallGainQ k := by
  rw [blockGainQ,smallGainQ,block_net_small,block_body_small]

theorem block_gain_value (k : Sym2 Basis) : (blockGainQ k : ℝ)=programEnergy k := by
  calc
    (blockGainQ k : ℝ) = Collision.energy (qvalue (blockNetQ k)) (qvalue (blockBodyQ k)) :=
      Spec.energyQ_value (blockNetQ k) (blockBodyQ k)
    _ = programEnergy k := by rw [blockNetQ_value,blockBodyQ_value]; rfl

theorem net_gain_block_sum : Spec.netGain=∑ k : Sym2 Basis, blockGainQ k := by
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_sum,Spec.netGain_value,program_energy_exact]
  apply Finset.sum_congr
  · ext k; simp
  · intro k _; exact (block_gain_value k).symm

theorem net_gain_small_sum : Spec.netGain=∑ k : Sym2 Basis, smallGainQ k := by
  rw [net_gain_block_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact block_gain_small k

theorem original_net_small_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-
        Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
        ((∑ k : Sym2 Basis, smallGainQ k : ℚ) : ℝ)| ≤ (109/10^7 : ℝ) := by
  rw [← net_gain_small_sum]
  exact Spec.original_rational_net_error

theorem source_net_off_sector (i j : PairController × Fin 2) (different : pceOrbit i ≠ pceOrbit j) :
    Spec.loadedNet i j=(0,0) := by
  apply LoadPrimitive.scalar_value_injective
  have h := net_preserves i j different
  rw [← Spec.loadedNet_value] at h
  simpa [qvalue,Scalar.value] using h

theorem assembleQ_same_block {ι κ : Type*} [DecidableEq κ]
    (label : ι → κ) (family : ∀ k, MatrixQ {i // label i=k} {i // label i=k}) (k : κ) :
    (assembleQ label family).submatrix Subtype.val Subtype.val=family k := by
  funext i j
  change Matrix.blockDiagonal' family ⟨label i.val,⟨i.val,rfl⟩⟩
    ⟨label j.val,⟨j.val,rfl⟩⟩=family k i j
  have left : (⟨label i.val,⟨i.val,rfl⟩⟩ : Σ k, {x // label x=k})=⟨k,i⟩ := by
    rcases i with ⟨x,hx⟩
    cases hx
    rfl
  have right : (⟨label j.val,⟨j.val,rfl⟩⟩ : Σ k, {x // label x=k})=⟨k,j⟩ := by
    rcases j with ⟨x,hx⟩
    cases hx
    rfl
  rw [left,right,Matrix.blockDiagonal'_apply_eq]

theorem pc_source_blockQ (k : Sym2 Basis) :
    computedPCQ.submatrix Subtype.val Subtype.val=(pcFamilyQ k).one := by
  rw [computedPCQ,assembleQ_same_block]

theorem parent_pc_source_blockQ (k : Sym2 Basis) :
    computedParentPCQ.submatrix Subtype.val Subtype.val=(pcFamilyQ k).two := by
  rw [computedParentPCQ,assembleQ_same_block]

theorem recovery_pc_source_blockQ (k : Sym2 Basis) :
    computedRecoveryPCQ.submatrix Subtype.val Subtype.val=(pcFamilyQ k).three := by
  rw [computedRecoveryPCQ,assembleQ_same_block]

theorem load_source_blockQ (k : Sym2 Basis) :
    computedLoadQ.submatrix Subtype.val Subtype.val=(loadedFamilyQ k).load := by
  rw [computedLoadQ,assembleQ_same_block]

theorem root_source_blockQ (k : Sym2 Basis) :
    computedRootQ.submatrix Subtype.val Subtype.val=(loadedFamilyQ k).root := by
  rw [computedRootQ,assembleQ_same_block]

theorem complement_source_blockQ (k : Sym2 Basis) :
    computedComplementQ.submatrix Subtype.val Subtype.val=(loadedFamilyQ k).complement := by
  rw [computedComplementQ,assembleQ_same_block]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
