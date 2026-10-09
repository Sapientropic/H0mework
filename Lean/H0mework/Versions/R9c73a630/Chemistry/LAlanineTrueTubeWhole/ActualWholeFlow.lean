import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ActualAllSteps
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ActualModel
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ContinuationSteps
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ContinuationPreservesFirst

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeActual

open SourceGaussianModel SourceSignedEvaluator TrueTubeSource TrueTubeTrace TrueTubeActual
open TrueTubeWholeChecks TrueTubeContinuation ContinuousGradient Set
noncomputable section

theorem wholeDirectionalFlow_original (d : Direction) (initial : InitialAt d) :
    IsIntegralCurveOn (wholeDirectionalFlow d initial) (fun _ => signedGradient (sign d))
      (Icc (0 : ℝ) (1 / 2)) :=
  window_is_original_flow d initial.val initial.property (actual_step d)

theorem wholeDirectionalFlow_stays (d : Direction) (initial : InitialAt d) (t : ℝ)
    (time : t ∈ Icc (0 : ℝ) (1 / 2)) : wholeDirectionalFlow d initial t ∈ sourceCube :=
  window_stays_source d initial.val initial.property (actual_step d) t time

theorem wholeDirectionalFlow_initials (d : Direction) (initial : InitialAt d) (i : Step) :
    InRectangle (initialBox d i) (wholeDirectionalFlow d initial (stepOffset i)) :=
  window_all_initials d initial.val initial.property (actual_step d) i

theorem wholeDirectionalFlow_tubes (d : Direction) (initial : InitialAt d) (i : Step) (t : ℝ)
    (time : t ∈ Icc 0 (stepSize : ℝ)) :
    InRectangle (tubeBox d i) (wholeDirectionalFlow d initial (t + stepOffset i)) :=
  window_all_tubes d initial.val initial.property (actual_step d) i t time

theorem wholeDirectionalFlow_endpoints (d : Direction) (initial : InitialAt d) (i : Step) :
    InRectangle (endpointBox d i) (wholeDirectionalFlow d initial (stepOffset i + stepSize)) :=
  window_all_endpoints d initial.val initial.property (actual_step d) i

theorem wholeDirectionalFlow_last (d : Direction) (initial : InitialAt d) :
    InRectangle (endpointBox d 15) (wholeDirectionalFlow d initial (1 / 2)) :=
  window_final_endpoint d initial.val initial.property (actual_step d)

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
