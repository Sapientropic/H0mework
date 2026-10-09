import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Whole
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Net

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def free : LoadedJoint := Matrix.kronecker Primitive.computedPC Phase.environmentPolynomial
def parent : LoadedJoint := Matrix.kronecker Primitive.computedParentPC (1 : Matrix (Fin 2) (Fin 2) ℂ)
def recovery : LoadedJoint := Matrix.kronecker Primitive.computedRecoveryPC Actions.recoveryEnvironmentPolynomial
def receivedWord : LoadedJoint := recovery*Actions.loadPolynomial*parent

def sharedPC : JointMatrix PairController := Matrix.kronecker Primitive.computedPC Primitive.computedPC
def supply : Current.FullJoint := Matrix.kronecker (sharedPC*Supply.nativeExchangePolynomial) Phase.environmentPolynomial
def weak : Current.FullJoint := Matrix.kronecker (sharedPC*Supply.weakExchangePolynomial) Phase.environmentPolynomial
def load : Current.FullJoint := Post.localMatrix Actions.loadPolynomial Primitive.computedPC

def rotatedRoot (R : LoadedJoint) : LoadedJoint := free*R*star free

def pointer : PointerJoint := SquareRoot.rawDilation
  (Incidence.bodyObservable (rotatedRoot SquareRoot.Full.sourceRoot))
  (Incidence.bodyObservable (rotatedRoot SquareRoot.Full.sourceComplement))

def pointerLoad : PointerJoint := Matrix.fromBlocks load 0 0 (Phase.pointerPhase • load)
def pointerSupply : PointerJoint := Matrix.fromBlocks load 0 0 (Phase.pointerPhase • supply)
def pointerWeak : PointerJoint := Matrix.fromBlocks load 0 0 (Phase.pointerPhase • weak)
def nine : PointerJoint := pointerLoad*pointerSupply*pointerSupply
def eleven : PointerJoint := pointerLoad*pointerWeak*nine

def netObservable : PointerJoint := star eleven*Post.finitePCObservable*eleven-star nine*Post.finitePCObservable*nine

def rootNet : PointerJoint := star pointer*netObservable*pointer

def loadedNet : LoadedJoint := Supply.donorSlice (star supply*(Prepared.pointerReadout rootNet)*supply)

def receivedBody : LoadedJoint := receivedWord*Field.computedBodyInput*star receivedWord

def netGain : ℝ := Collision.energy loadedNet receivedBody

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
