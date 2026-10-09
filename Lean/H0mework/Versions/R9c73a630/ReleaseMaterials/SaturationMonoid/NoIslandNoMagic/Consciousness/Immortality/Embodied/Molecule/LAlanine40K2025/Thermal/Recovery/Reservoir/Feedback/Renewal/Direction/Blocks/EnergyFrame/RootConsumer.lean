import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.RootError
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.RelativeEffect
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.EffectGap

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def commonRootFloor (A B : Matrix ι ι ℂ) : ℝ := Real.sqrt (min (effectGap A) (effectGap B))

theorem common_root_floor_positive (A B : Matrix ι ι ℂ) : 0 < commonRootFloor A B :=
  Real.sqrt_pos.mpr (lt_min (effect_gap_positive A) (effect_gap_positive B))

def rootErrorBudget (A B : Matrix ι ι ℂ) : ℝ := (‖A-B‖/measurementScale A)/(2*commonRootFloor A B)

theorem effect_root_error (A B : Matrix ι ι ℂ) (ha : A.IsHermitian) (hb : B.IsHermitian) :
    ‖effectRoot (boundedEffect A)-effectRoot (boundedEffect B)‖ ≤ rootErrorBudget A B := by
  have rpos := common_root_floor_positive A B
  have dpos : 0 ≤ rootErrorBudget A B :=
    div_nonneg (div_nonneg (norm_nonneg _) (measurementScale_pos A).le) (mul_nonneg (by norm_num) rpos.le)
  have sq : commonRootFloor A B*commonRootFloor A B = min (effectGap A) (effectGap B) := by
    rw [← pow_two,commonRootFloor,Real.sq_sqrt (le_min (effect_gap_positive A).le (effect_gap_positive B).le)]
  have floorA : (commonRootFloor A B*commonRootFloor A B) • (1 : Matrix ι ι ℂ) ≤ boundedEffect A := by
    rw [sq]
    exact (smul_le_smul_of_nonneg_right (min_le_left _ _) zero_le_one).trans (bounded_effect_gap A ha)
  have floorB : (commonRootFloor A B*commonRootFloor A B) • (1 : Matrix ι ι ℂ) ≤ boundedEffect B := by
    rw [sq]
    exact (smul_le_smul_of_nonneg_right (min_le_right _ _) zero_le_one).trans (bounded_effect_gap B hb)
  have paid : ‖boundedEffect A-boundedEffect B‖ ≤ 2*commonRootFloor A B*rootErrorBudget A B := by
    unfold rootErrorBudget
    rw [mul_div_cancel₀ _ (mul_pos (by norm_num) rpos).ne']
    exact bounded_effect_relative_error A B
  exact sqrt_perturbation _ _ (boundedEffect_positive A ha).nonneg (boundedEffect_positive B hb).nonneg
    (commonRootFloor A B) (rootErrorBudget A B) rpos.le dpos floorA floorB paid

theorem complement_root_error (A B : Matrix ι ι ℂ) (ha : A.IsHermitian) (hb : B.IsHermitian) :
    ‖complementRoot (boundedEffect A)-complementRoot (boundedEffect B)‖ ≤ rootErrorBudget A B := by
  have h := effect_root_error (-A) (-B) ha.neg hb.neg
  simpa only [effectRoot,complementRoot,← boundedEffect_complement,rootErrorBudget,commonRootFloor,
    effectGap,measurementScale,norm_neg,neg_sub_neg,norm_sub_rev] using h

theorem original_source_root_error (B : Load.Source.LoadedJoint) (hermitian : B.IsHermitian) :
    ‖Quantum.conjugation installedLoadFrame (effectRoot (sourceMeasurementEffect Load.Source.loadTotalHamiltonian))-
      effectRoot (boundedEffect B)‖ ≤ rootErrorBudget originalCalculatedOutput B ∧
    ‖Quantum.conjugation installedLoadFrame (complementRoot (sourceMeasurementEffect Load.Source.loadTotalHamiltonian))-
      complementRoot (boundedEffect B)‖ ≤ rootErrorBudget originalCalculatedOutput B := by
  rw [original_effect_root_calculated,original_complement_root_calculated]
  exact ⟨effect_root_error _ _ original_calculated_hermitian hermitian,
    complement_root_error _ _ original_calculated_hermitian hermitian⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
