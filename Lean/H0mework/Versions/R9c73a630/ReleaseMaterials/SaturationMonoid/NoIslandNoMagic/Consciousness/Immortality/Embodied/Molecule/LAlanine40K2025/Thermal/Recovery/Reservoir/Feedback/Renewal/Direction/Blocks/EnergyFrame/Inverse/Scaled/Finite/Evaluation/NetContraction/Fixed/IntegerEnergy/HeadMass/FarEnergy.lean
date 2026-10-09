import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.FarMass
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.LoadedNorm
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Powered.Dynamics
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
noncomputable section

/-! A single original loaded-observable bound settles all high-partner addresses. -/

theorem source_ordinary_qnet_lower_loaded (a b : Basis) (ordered : a < b) :
    (-(2005/1000) : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet a b ordered := by
  have h := hermitian_lower_from_center (sourceOrdinaryQNet a b ordered)
    (ordinary_qnet_hermitian a b ordered) 0 (2005/1000)
    (by simpa only [zero_smul,sub_zero] using source_ordinary_qnet_norm_loaded a b ordered)
  simpa only [zero_sub] using h

theorem head_far_original_gain_lower :
    (-(302/10^8) : ℝ) < headRestFarOriginalGain := by
  have point (p : HeadRestFar) := original_ordinary_gain_lower_of_order
    p.val.val.val.1 p.val.val.val.2 p.val.val.property.2 (-(2005/1000))
    (source_ordinary_qnet_lower_loaded _ _ p.val.val.property.2)
  have summed := Finset.sum_le_sum (s := (Finset.univ : Finset HeadRestFar))
    (fun p _ => point p)
  change (∑ p : HeadRestFar,
      ((-(2005/1000)-3/10^12 : ℝ)*(computedOrdinaryBody p.val.val.val.1 p.val.val.val.2).trace.re-
        2/10^14)) ≤ headRestFarOriginalGain at summed
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,head_rest_far_card,nsmul_eq_mul] at summed
  change (-(2005/1000)-3/10^12 : ℝ)*headFarReferenceMass-444*(2/10^14) ≤
    headRestFarOriginalGain at summed
  have mass := head_far_reference_mass_upper
  linarith only [summed,mass]

theorem source_net_low_remainder_lower :
    midOriginalGain+headRestLowOriginalGain+(803/10^9 : ℝ) < (Spec.netGain : ℝ) := by
  have source := source_net_remaining_lower
  have far := head_far_original_gain_lower
  linarith only [source,far]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
