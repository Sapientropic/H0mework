import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SpecBase

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Spec
open Propagation.Interface Load.Source Collision
open scoped Matrix
noncomputable section

def rotatedRoot (R : MatrixQ (PairController × Fin 2) (PairController × Fin 2)) : MatrixQ (PairController × Fin 2) (PairController × Fin 2) :=
  qmultiply (qmultiply free R) (qadjoint free)

def bodyObservable (R : MatrixQ (PairController × Fin 2) (PairController × Fin 2)) : MatrixQ Current.FullIndex Current.FullIndex :=
  localMatrixQ R (qidentity PairController)

def pointer : MatrixQ PointerIndex PointerIndex :=
  let r := bodyObservable (rotatedRoot computedRootQ)
  let s := bodyObservable (rotatedRoot computedComplementQ)
  Matrix.fromBlocks r (-s) s r

def pcLift : MatrixQ Current.FullIndex Current.FullIndex :=
  qkron (qkron hamiltonianQ (qidentity PairController)) (qidentity (Fin 2))

def pcObservable : MatrixQ PointerIndex PointerIndex := Matrix.fromBlocks pcLift 0 0 pcLift

def pointerLoad : MatrixQ PointerIndex PointerIndex := Matrix.fromBlocks load 0 0 (qscale phaseQ load)
def pointerSupply : MatrixQ PointerIndex PointerIndex := Matrix.fromBlocks load 0 0 (qscale phaseQ supply)
def pointerWeak : MatrixQ PointerIndex PointerIndex := Matrix.fromBlocks load 0 0 (qscale phaseQ weak)
def nine : MatrixQ PointerIndex PointerIndex := qmultiply (qmultiply pointerLoad pointerSupply) pointerSupply
def eleven : MatrixQ PointerIndex PointerIndex := qmultiply (qmultiply pointerLoad pointerWeak) nine

theorem rotatedRoot_value (R : MatrixQ (PairController × Fin 2) (PairController × Fin 2)) :
    qvalue (rotatedRoot R)=PCExecution.rotatedRoot (qvalue R) := by
  simp only [rotatedRoot,qvalue_multiply,qvalue_adjoint,free_value,PCExecution.rotatedRoot,Matrix.star_eq_conjTranspose]

theorem bodyObservable_value (R : MatrixQ (PairController × Fin 2) (PairController × Fin 2)) :
    qvalue (bodyObservable R)=Incidence.bodyObservable (qvalue R) := by
  rw [bodyObservable,localMatrixQ_value,qvalue_identity]
  rfl

theorem pointer_value : qvalue pointer=PCExecution.pointer := by
  simp only [pointer,qvalue_fourBlocks,qvalue_neg,bodyObservable_value,rotatedRoot_value,
    computedRootQ_value,computedComplementQ_value]
  rw [PCExecution.pointer,SquareRoot.raw_dilation_read]

theorem pcLift_value : qvalue pcLift=Post.pcLift (sourcePCH E) := by
  simp only [pcLift,qvalue_kron,hamiltonianQ_value,qvalue_identity,Post.pcLift]

theorem pcObservable_value : qvalue pcObservable=Post.finitePCObservable := by
  simp only [pcObservable,qvalue_fourBlocks,pcLift_value,qvalue_zero,Post.finitePCObservable]
  rfl

theorem pointerLoad_value : qvalue pointerLoad=LoadExecution.pointerLoad := by
  simp only [pointerLoad,qvalue_fourBlocks,load_value,qvalue_zero,qvalue_scale,phaseQ_value,LoadExecution.pointerLoad]

theorem pointerSupply_value : qvalue pointerSupply=LoadExecution.pointerSupply := by
  simp only [pointerSupply,qvalue_fourBlocks,load_value,supply_value,qvalue_zero,qvalue_scale,phaseQ_value,LoadExecution.pointerSupply]

theorem pointerWeak_value : qvalue pointerWeak=LoadExecution.pointerWeak := by
  simp only [pointerWeak,qvalue_fourBlocks,load_value,weak_value,qvalue_zero,qvalue_scale,phaseQ_value,LoadExecution.pointerWeak]

theorem nine_value : qvalue nine=LoadExecution.nine := by
  simp only [nine,qvalue_multiply,pointerLoad_value,pointerSupply_value,LoadExecution.nine]

theorem eleven_value : qvalue eleven=LoadExecution.eleven := by
  simp only [eleven,qvalue_multiply,pointerLoad_value,pointerWeak_value,nine_value,LoadExecution.eleven]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Spec
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
