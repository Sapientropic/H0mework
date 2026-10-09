import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Whole
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Normalization

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
open Propagation.Interface Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def finiteEffect : LoadedJoint := normalizedAt rationalRegularizer (480362644764/10^10) rationalCore

theorem finite_effect_error : ‖scaledEffect rationalRegularizer rationalCore-finiteEffect‖ ≤ (4/10^12 : ℝ) := by
  have paid := normalization_error rationalRegularizer (480362644764/10^10) (3/10^10) rationalCore
    rational_regularizer_positive original_rational_norm_interval.2 (by linarith [original_rational_norm_interval.1])
  apply paid.trans
  apply (div_le_iff₀ (by linarith [rational_regularizer_positive] : (0 : ℝ) < 2*(rationalRegularizer+480362644764/10^10))).mpr
  nlinarith [rational_regularizer_positive]

theorem source_finite_effect_error :
    ‖Quantum.conjugation installedLoadFrame (sourceMeasurementEffect loadTotalHamiltonian)-
      Quantum.conjugation numericFree finiteEffect‖ ≤ (266/10^12 : ℝ) := by
  have delta : ‖Quantum.conjugation numericFree (scaledEffect rationalRegularizer rationalCore)-
      Quantum.conjugation numericFree finiteEffect‖ ≤ (4/10^12 : ℝ) := by
    rw [← map_sub]
    have same := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint numericFree)
      (scaledEffect rationalRegularizer rationalCore-finiteEffect)
    change ‖Quantum.conjugation numericFree (scaledEffect rationalRegularizer rationalCore-finiteEffect)‖ = _ at same
    rw [same]
    exact finite_effect_error
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (Quantum.conjugation installedLoadFrame (sourceMeasurementEffect loadTotalHamiltonian))
    (Quantum.conjugation numericFree (scaledEffect rationalRegularizer rationalCore))
    (Quantum.conjugation numericFree finiteEffect)
  linarith [source_rational_effect_error]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
