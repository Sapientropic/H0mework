import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ActualWholeFlow
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ActualFullConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeActual

open SourceGaussianModel SourceSignedEvaluator TrueTubeSource TrueTubeTrace TrueTubeActual
open WholeCellPartition ContinuousGradient Set
noncomputable section

theorem fullFlow_original (p : BandPoint) :
    IsIntegralCurveOn (fullFlow p) (fun _ => sourceGradient) (Icc (-(1 / 2) : ℝ) (1 / 2)) :=
  original_full_from_local actual_step p

theorem fullFlow_stays (p : BandPoint) (t : ℝ) (time : t ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    fullFlow p t ∈ sourceCube := full_stays_from_local actual_step p t time

theorem fullFlow_zero_derivative (p : BandPoint) :
    HasDerivAt (fullFlow p) (sourceGradient (ContinuousParameterMap.initialMap 0 4 p.val)) 0 := by
  have derivative := (fullFlow_original p 0 (by constructor <;> norm_num)).hasDerivAt
    (Icc_mem_nhds (by norm_num) (by norm_num))
  rwa [fullFlow_starts] at derivative

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
