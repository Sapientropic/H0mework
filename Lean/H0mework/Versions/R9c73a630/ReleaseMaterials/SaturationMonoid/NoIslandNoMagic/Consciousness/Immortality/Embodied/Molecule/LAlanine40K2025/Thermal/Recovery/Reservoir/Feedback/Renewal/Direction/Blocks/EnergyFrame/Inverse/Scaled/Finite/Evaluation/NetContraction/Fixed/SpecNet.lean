import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SpecPulse

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Spec
open Propagation.Interface Load.Source Collision Powered.Dynamics
open scoped Matrix BigOperators
noncomputable section

def netObservable : MatrixQ PointerIndex PointerIndex :=
  qmultiply (qmultiply (qadjoint eleven) pcObservable) eleven-qmultiply (qmultiply (qadjoint nine) pcObservable) nine

def rootNet : MatrixQ PointerIndex PointerIndex := qmultiply (qmultiply (qadjoint pointer) netObservable) pointer

def wireQ {α β : Type*} [Fintype α] (A : MatrixQ α α) (B : MatrixQ (α ⊕ α) (α ⊕ α)) (f : β → α) : MatrixQ β β :=
  (qmultiply (qmultiply (qadjoint A) (B.submatrix Sum.inl Sum.inl)) A).submatrix f f

theorem wireQ_value {α β : Type*} [Fintype α] (A : MatrixQ α α) (B : MatrixQ (α ⊕ α) (α ⊕ α)) (f : β → α) :
    qvalue (wireQ A B f)=((qvalue A).conjTranspose*(qvalue B).submatrix Sum.inl Sum.inl*qvalue A).submatrix f f := by
  simp only [wireQ,qvalue_submatrix,qvalue_multiply,qvalue_adjoint]

def loadedNet : MatrixQ (PairController × Fin 2) (PairController × Fin 2) :=
  wireQ supply rootNet (fun i => ((i.1,Supply.donorIndex),i.2))

def excitedQ : MatrixQ (Fin 2) (Fin 2) := diagonalQ ![(0,0),(1,0)]
def bodyInput : MatrixQ (PairController × Fin 2) (PairController × Fin 2) := qkron (qkron pairQ excitedQ) environmentQ
def body : MatrixQ (PairController × Fin 2) (PairController × Fin 2) := qmultiply (qmultiply receivedWord bodyInput) (qadjoint receivedWord)

theorem netObservable_value : qvalue netObservable=LoadExecution.netObservable := by
  simp only [netObservable,qvalue_sub,qvalue_multiply,qvalue_adjoint,eleven_value,nine_value,pcObservable_value,
    LoadExecution.netObservable,Matrix.star_eq_conjTranspose]

theorem rootNet_value : qvalue rootNet=LoadExecution.rootNet := by
  simp only [rootNet,qvalue_multiply,qvalue_adjoint,pointer_value,netObservable_value,LoadExecution.rootNet,Matrix.star_eq_conjTranspose]

theorem loadedNet_value : qvalue loadedNet=LoadExecution.loadedNet := by
  have wire := wireQ_value supply rootNet (fun i : PairController × Fin 2 => ((i.1,Supply.donorIndex),i.2))
  rw [supply_value,rootNet_value] at wire
  exact wire

theorem excitedQ_value : qvalue excitedQ=excitedController := by
  rw [excitedQ,diagonalQ_value]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [excitedController,Scalar.value]

theorem bodyInput_value : qvalue bodyInput=InputProducts.bodyInput := by
  simp only [bodyInput,qvalue_kron,pairQ_value,excitedQ_value,environmentQ_value,InputProducts.bodyInput,chargedInput]

theorem body_value : qvalue body=InputProducts.body := by
  simp only [body,qvalue_multiply,qvalue_adjoint,receivedWord_value,bodyInput_value,InputProducts.body,Matrix.star_eq_conjTranspose]

def energyQ {α : Type*} [Fintype α] (O ρ : MatrixQ α α) : ℚ := ∑ i, (qmultiply O ρ i i).1

theorem energyQ_value {α : Type*} [Fintype α] (O ρ : MatrixQ α α) :
    (energyQ O ρ : ℝ)=Collision.energy (qvalue O) (qvalue ρ) := by
  rw [Collision.energy,← qvalue_multiply]
  simp [energyQ,Matrix.trace,Matrix.diag,qvalue,Scalar.value]

def netGain : ℚ := energyQ loadedNet body

theorem netGain_value : (netGain : ℝ)=InputProducts.netGain := by
  rw [netGain,energyQ_value,loadedNet_value,body_value]
  rfl

theorem original_rational_net_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-(netGain : ℝ)| ≤ (109/10^7 : ℝ) := by
  rw [netGain_value]
  exact InputProducts.original_computed_input_net_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Spec
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
