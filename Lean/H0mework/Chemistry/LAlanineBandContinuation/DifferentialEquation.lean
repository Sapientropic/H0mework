import H0mework.Chemistry.LAlanineBandContinuation.DifferentialLinearization

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandContinuation TrueFlowDifferential Set
noncomputable section

theorem rawPath_integral_equation (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) :
    rawPath (cellSeed c p) = pathConst (cellSeed c p) + volterra (pathGradient (rawPath (cellSeed c p))) := by
  apply ContinuousMap.ext
  intro t
  have htime : uIcc (0 : ℝ) (t : ℝ) ⊆ Icc (-(1/2) : ℝ) (1/2) :=
    uIcc_subset_Icc (by constructor <;> norm_num) t.property
  have hpicard := ODE.picard_eq_of_hasDerivAt
    (f := fun _ => sourceGradient) (t₀ := 0) (t := (t : ℝ))
    (α := rawFlow (cellSeed c p)) (u := univ)
    ((sourceGradient_contDiff 1).continuous.comp continuous_snd).continuousOn
    (fun s hs => (full_original c fields p inside s (htime hs)).mono htime)
    (fun _ _ => mem_univ _)
  change rawFlow (cellSeed c p) t = cellSeed c p +
    ∫ s in 0..(t : ℝ), extendPath (pathGradient (rawPath (cellSeed c p))) s
  calc
    rawFlow (cellSeed c p) t = cellSeed c p +
        ∫ s in 0..(t : ℝ), sourceGradient (rawFlow (cellSeed c p) s) := by
      simpa only [ODE.picard_apply, rawFlow_starts] using hpicard.symm
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      exact (extendPath_coe (pathGradient (rawPath (cellSeed c p))) ⟨s, htime hs⟩).symm

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
