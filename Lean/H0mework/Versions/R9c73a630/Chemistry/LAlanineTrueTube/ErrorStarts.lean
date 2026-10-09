import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.ErrorTrajectory

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeError

open SourceGaussianModel ContinuousGradient ContinuousParameterMap
open LAlanineContinuousPatch.Parametric
noncomputable section

attribute [local irreducible] sourceGradient

def zeroTimeParameters (p : Point) : Point := ![p 0, p 1, 0]

theorem initialMap_same_zero_time (p : Point) :
    initialMap 0 4 (zeroTimeParameters p) = initialMap 0 4 p := rfl

theorem parameterMap_at_zero_time (p : Point) (zero : p 2 = 0) :
    parameterMap 0 4 p = initialMap 0 4 p := by
  have time : parameterTimeLinear 0 p = 0 := by rw [parameterTime_readout, zero, zero_div]
  have step : rk4Step sourceGradient 0 = id := by
    funext x
    simp only [rk4Step, zero_div, zero_smul, add_zero, id_eq]
  rw [parameterMap, time, step]
  simp only [Function.iterate_id, id_eq]

theorem finiteTrajectory_same_initial (p : Point) :
    finiteTrajectory (zeroTimeParameters p) 0 = initialMap 0 4 p := by
  change parameterMap 0 4 (zeroTimeParameters p + (0 : ℝ) • Pi.single 2 1) = _
  rw [zero_smul, add_zero, parameterMap_at_zero_time _ (by rfl), initialMap_same_zero_time]

end
end LAlanine40K2025.BasinRefinement.TrueTubeError
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
