import H0mework.Chemistry.LAlanineBandCellDifferential.Linearization

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandGeometry WholeBandActual TrueFlowDifferential
open WholeBandCell0Continuation Set
noncomputable section

theorem cell0_rawPath_integral_equation (p : Cell0Point) :
    rawPath (cellSeed 0 p.val) = pathConst (cellSeed 0 p.val) +
      volterra (pathGradient (rawPath (cellSeed 0 p.val))) := by
  apply ContinuousMap.ext
  intro t
  have htime : uIcc (0 : ℝ) (t : ℝ) ⊆ Icc (-(1/2) : ℝ) (1/2) :=
    uIcc_subset_Icc (by constructor <;> norm_num) t.property
  have hpicard := ODE.picard_eq_of_hasDerivAt
    (f := fun _ => sourceGradient) (t₀ := 0) (t := (t : ℝ))
    (α := rawFlow (cellSeed 0 p.val)) (u := univ)
    ((sourceGradient_contDiff 1).continuous.comp continuous_snd).continuousOn
    (fun s hs => (cell0_full_original p s (htime hs)).mono htime)
    (fun _ _ => mem_univ _)
  change rawFlow (cellSeed 0 p.val) t = cellSeed 0 p.val +
    ∫ s in 0..(t : ℝ), extendPath (pathGradient (rawPath (cellSeed 0 p.val))) s
  calc
    rawFlow (cellSeed 0 p.val) t = cellSeed 0 p.val +
        ∫ s in 0..(t : ℝ), sourceGradient (rawFlow (cellSeed 0 p.val) s) := by
      simpa only [ODE.picard_apply, rawFlow_starts] using hpicard.symm
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      exact (extendPath_coe (pathGradient (rawPath (cellSeed 0 p.val))) ⟨s, htime hs⟩).symm

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
