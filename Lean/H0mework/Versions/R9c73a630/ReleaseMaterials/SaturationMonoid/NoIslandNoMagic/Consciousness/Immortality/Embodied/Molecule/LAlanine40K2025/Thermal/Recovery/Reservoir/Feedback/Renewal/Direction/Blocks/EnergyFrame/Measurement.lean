import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.LoadConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.BoundedBodyMeasurement
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.BinaryPointerDilation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem measurement_scale_error (A B : Matrix ι ι ℂ) :
    |measurementScale A-measurementScale B| ≤ ‖A-B‖ := by
  simpa only [measurementScale,add_sub_add_left_eq_sub] using abs_norm_sub_norm_le A B

theorem measurement_scale_conjugation (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    measurementScale (Quantum.conjugation U A) = measurementScale A := by
  unfold measurementScale
  exact congrArg (fun x : ℝ => 1+x) (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U) A)

theorem bounded_effect_conjugation (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    Quantum.conjugation U (boundedEffect A) = boundedEffect (Quantum.conjugation U A) := by
  have one : Quantum.conjugation U (1 : Matrix ι ι ℂ) = 1 :=
    map_one (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U)
  simp only [boundedEffect,measurement_scale_conjugation,map_add,map_smul,one]

theorem sqrt_conjugation (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) (positive : A.PosSemidef) :
    Quantum.conjugation U (CFC.sqrt A) = CFC.sqrt (Quantum.conjugation U A) := by
  apply ((CFC.sqrt_eq_iff _ _ (Quantum.conjugation_posSemidef U A positive).nonneg
    (Quantum.conjugation_posSemidef U _ (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))).nonneg).mpr ?_).symm
  have product : Quantum.conjugation U (CFC.sqrt A*CFC.sqrt A) =
      Quantum.conjugation U (CFC.sqrt A)*Quantum.conjugation U (CFC.sqrt A) :=
    map_mul (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U) _ _
  rw [← product,CFC.sqrt_mul_sqrt_self A positive.nonneg]

theorem effect_root_conjugation (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) (hermitian : A.IsHermitian) :
    Quantum.conjugation U (effectRoot (boundedEffect A)) = effectRoot (boundedEffect (Quantum.conjugation U A)) := by
  rw [effectRoot,sqrt_conjugation U _ (boundedEffect_positive A hermitian),bounded_effect_conjugation]
  rfl

theorem complement_root_conjugation (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) (hermitian : A.IsHermitian) :
    Quantum.conjugation U (complementRoot (boundedEffect A)) = complementRoot (boundedEffect (Quantum.conjugation U A)) := by
  rw [complementRoot,sqrt_conjugation U _ (boundedEffect_complement_positive A hermitian)]
  have one : Quantum.conjugation U (1 : Matrix ι ι ℂ) = 1 :=
    map_one (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U)
  simp only [map_sub,one,bounded_effect_conjugation,complementRoot]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
