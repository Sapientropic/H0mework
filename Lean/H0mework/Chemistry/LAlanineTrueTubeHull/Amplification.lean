import H0mework.Chemistry.LAlanineTrueTubeHull.Lipschitz

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeHull

open SourceSignedEvaluator
noncomputable section

private theorem source_exp_upper : (exponential (point (33 / 40)) 1 1).2 < 23 / 10 := by decide +kernel

theorem half_window_amplification : Real.exp ((lipschitzConstant : ℝ) / 2) < 23 / 10 := by
  have bounded := exponential_holds (point (33 / 40)) 1 1 (by decide +kernel) (by decide +kernel)
    (33 / 40) (by convert! point_holds (33 / 40) using 1; norm_num)
  have capped : Real.exp (33 / 40) < (23 / 10 : ℝ) :=
    bounded.2.trans_lt (by simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt.mpr source_exp_upper : ((exponential (point (33 / 40)) 1 1).2 : ℝ) < ((23 / 10 : ℚ) : ℝ)))
  exact (Real.exp_le_exp.mpr (by linarith [constant_strict.2])).trans_lt capped

end
end LAlanine40K2025.BasinRefinement.TrueTubeHull
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
