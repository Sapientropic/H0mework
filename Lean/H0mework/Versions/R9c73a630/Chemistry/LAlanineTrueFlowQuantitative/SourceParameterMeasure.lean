import H0mework.Versions.AB.Chemistry.LAlanineWholeCell.PartitionGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowQuantitative

open SourceGaussianModel IntervalParameterMap WholeCellPartition Set MeasureTheory
noncomputable section

theorem source_full_parameter_volume_exact :
    rationalBoxVolume fullLowerQ fullUpperQ =
      (1441151880758559 / 576460752303423488 : ℚ) := by decide +kernel

theorem fullDomain_volume_exact :
    volume.real fullDomain = (1441151880758559 / 576460752303423488 : ℝ) := by
  change (volume (Icc (fun i => (fullLowerQ i : ℝ))
    (fun i => (fullUpperQ i : ℝ)))).toReal = _
  rw [Real.volume_Icc_pi_toReal (fun i => Rat.cast_le.mpr (full_ordered i).le)]
  have exactVolume := congrArg (fun q : ℚ => (q : ℝ)) source_full_parameter_volume_exact
  simpa only [rationalBoxVolume, Rat.cast_prod, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
    using exactVolume

theorem fullDomain_volume_bounds :
    (1 / 400 : ℝ) < volume.real fullDomain ∧ volume.real fullDomain < 251 / 100000 := by
  rw [fullDomain_volume_exact]
  constructor <;> norm_num

end
end LAlanine40K2025.BasinRefinement.TrueFlowQuantitative
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
