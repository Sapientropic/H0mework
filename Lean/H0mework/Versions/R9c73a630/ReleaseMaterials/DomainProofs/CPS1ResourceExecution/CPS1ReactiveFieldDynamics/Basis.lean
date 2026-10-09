import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveField.Continuation
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Mechanics
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Variation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

namespace CPS1ReactiveFieldDynamics
noncomputable section
open CPS1ElectronicSource InnerProductSpace
open scoped BigOperators InnerProductSpace Matrix
abbrev Snapshot := CPS1ReactiveField.Carried.Snapshot

-- This is the complete stored source family, including unoccupied directions.
def raw (state : Snapshot) (index : state.PrimitiveIndex) : SpinSpace :=
  (state.primitive index).jet 0
abbrev BasisIndex (state : Snapshot) := CPS1MolecularFrame.FiniteNormed.Index (𝕜 := ℂ) (raw state)
def basis (state : Snapshot) : BasisIndex state → SpinSpace :=
  CPS1MolecularFrame.FiniteNormed.field (𝕜 := ℂ) (raw state)
def sourceCoefficient (state : Snapshot) : Matrix state.PrimitiveIndex (BasisIndex state) ℂ :=
  CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ) (raw state)
def coordinates (state : Snapshot) : Matrix (BasisIndex state) state.ElectronIndex ℂ :=
  CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (raw state) * state.occupied

def basisJet (state : Snapshot) (index : BasisIndex state) (jet : Fin 3 → Nat) : SpinSpace :=
  ∑ primitive, sourceCoefficient state primitive index • (state.primitive primitive).jet jet

theorem basis_orthonormal (state : Snapshot) : Orthonormal ℂ (basis state) :=
  CPS1MolecularFrame.FiniteNormed.field_orthonormal _

theorem complete_source_span (state : Snapshot) :
    Submodule.span ℂ (Set.range (basis state)) = Submodule.span ℂ (Set.range (raw state)) :=
  CPS1MolecularFrame.FiniteNormed.span_exact _

theorem basis_jet_zero (state : Snapshot) (index : BasisIndex state) :
    basisJet state index 0 = basis state index :=
  (CPS1MolecularFrame.FiniteNormed.field_synthesis (raw state) index).symm

theorem raw_synthesis (state : Snapshot) (primitive : state.PrimitiveIndex) :
    CPS1ElectronicEvolution.fields (basis state)
      (CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (raw state)) primitive = raw state primitive :=
  (CPS1MolecularFrame.FiniteNormed.raw_synthesis (raw state) primitive).symm

theorem current_coordinates (state : Snapshot) (slot : state.ElectronIndex) :
    CPS1ElectronicEvolution.fields (basis state) (coordinates state) slot = state.fields slot := by
  rw [coordinates,CPS1Deformation.fields_mul]
  have complete : CPS1ElectronicEvolution.fields (basis state)
      (CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (raw state)) = raw state :=
    funext (raw_synthesis state)
  rw [complete]
  rfl

theorem coordinates_gram (state : Snapshot) (good : state.Good) :
    (coordinates state).conjTranspose * coordinates state = 1 := by
  ext first second
  rw [← CPS1ElectronicEvolution.field_gram (basis state) (basis_orthonormal state),
    current_coordinates,current_coordinates]
  exact orthonormal_iff_ite.mp good first second

-- Preserve the actual stored coefficients, including raw null relations. A later
-- update adds a generated source-span increment rather than resetting old C.
def increment (state : Snapshot) (next : Matrix (BasisIndex state) state.ElectronIndex ℂ) :
    Matrix state.PrimitiveIndex state.ElectronIndex ℂ :=
  state.occupied + sourceCoefficient state * (next - coordinates state)

def withOccupation (state : Snapshot) (occupied : Matrix state.PrimitiveIndex state.ElectronIndex ℂ) : Snapshot :=
  {state with occupied := occupied}

theorem increment_current (state : Snapshot) : increment state (coordinates state) = state.occupied := by
  simp only [increment,sub_self,Matrix.mul_zero,add_zero]

theorem increment_fields (state : Snapshot) (next : Matrix (BasisIndex state) state.ElectronIndex ℂ)
    (slot : state.ElectronIndex) :
    (withOccupation state (increment state next)).fields slot =
      CPS1ElectronicEvolution.fields (basis state) next slot := by
  change (∑ primitive, (state.occupied + sourceCoefficient state * (next - coordinates state)) primitive slot •
    (state.primitive primitive).jet 0) = _
  simp only [Matrix.add_apply,add_smul,Finset.sum_add_distrib]
  change state.fields slot + CPS1ElectronicEvolution.fields (raw state)
    (sourceCoefficient state * (next - coordinates state)) slot = _
  rw [CPS1Deformation.fields_mul]
  have synthesis : CPS1ElectronicEvolution.fields (raw state) (sourceCoefficient state) = basis state :=
    funext (basis_jet_zero state)
  rw [synthesis]
  rw [← current_coordinates state slot]
  simp only [CPS1ElectronicEvolution.fields,Matrix.sub_apply,sub_smul,Finset.sum_sub_distrib]
  abel

end
end CPS1ReactiveFieldDynamics
