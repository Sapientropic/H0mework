import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Shared

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open Propagation.Interface Load.Source Propagation.Producer
open scoped Matrix BigOperators
noncomputable section

def valueMatrix (x y time : ℝ) : Matrix NativeIndex NativeIndex ℂ :=
  (basis*sharedValue x y time*inverse).submatrix flatten flatten

theorem packed_flow_values (x y time : ℝ) : Phase.flowPolynomial (packed x y) time=basis*sharedValue x y time*inverse := by
  rw [original_load_shared,basis_flow,shared_flow_values]

theorem original_native_flow_values (x y time : ℝ) :
    Phase.flowPolynomial (Scaled.Order.smallLoaded x y) time=valueMatrix x y time := by
  have same : (packed x y).submatrix flatten flatten=Scaled.Order.smallLoaded x y := by
    unfold packed
    rw [Matrix.submatrix_submatrix]
    simp only [Function.comp_def,Equiv.symm_apply_apply]
    rfl
  rw [← same,← Primitive.flow_reindex,packed_flow_values]
  rfl

theorem original_load_values (a b : Basis) (distinct : a ≠ b) :
    Actions.loadPolynomial.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)=
      valueMatrix (Donor.calculatedEnergy a) (Donor.calculatedEnergy b) (nativeClockStep : ℝ) := by
  unfold Actions.loadPolynomial
  rw [Primitive.ordinary_load_original a b distinct]
  exact original_native_flow_values _ _ _

end

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
