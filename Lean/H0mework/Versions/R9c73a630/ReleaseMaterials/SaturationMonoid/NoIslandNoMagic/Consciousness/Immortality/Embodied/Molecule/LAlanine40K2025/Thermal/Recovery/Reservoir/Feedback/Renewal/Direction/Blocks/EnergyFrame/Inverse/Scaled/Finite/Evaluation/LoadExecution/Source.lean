import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Whole
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.Consumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def receivedWord : LoadedJoint := PCExecution.recovery*LoadPrimitive.computedLoad*PCExecution.parent

def load : Current.FullJoint := Post.localMatrix LoadPrimitive.computedLoad Primitive.computedPC

def pointerLoad : PointerJoint := Matrix.fromBlocks load 0 0 (Phase.pointerPhase • load)
def pointerSupply : PointerJoint := Matrix.fromBlocks load 0 0 (Phase.pointerPhase • PCExecution.supply)
def pointerWeak : PointerJoint := Matrix.fromBlocks load 0 0 (Phase.pointerPhase • PCExecution.weak)
def nine : PointerJoint := pointerLoad*pointerSupply*pointerSupply
def eleven : PointerJoint := pointerLoad*pointerWeak*nine

def netObservable : PointerJoint := star eleven*Post.finitePCObservable*eleven-star nine*Post.finitePCObservable*nine

def rootNet : PointerJoint := star PCExecution.pointer*netObservable*PCExecution.pointer

def loadedNet : LoadedJoint := Supply.donorSlice
  (star PCExecution.supply*(Prepared.pointerReadout rootNet)*PCExecution.supply)

def receivedBody : LoadedJoint := receivedWord*Field.computedBodyInput*star receivedWord

def netGain : ℝ := Collision.energy loadedNet receivedBody

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
