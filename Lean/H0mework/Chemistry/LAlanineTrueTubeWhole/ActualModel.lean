import H0mework.Chemistry.LAlanineTrueTubeWhole.ContinuationPreservesFirst

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeActual

open SourceGaussianModel SourceSignedEvaluator TrueTubeSource TrueTubeActual
open TrueTubeContinuation Set
noncomputable section

def wholeDirectionalFlow (d : Direction) (initial : InitialAt d) : ℝ → Point := windowCurve d initial.val

theorem wholeDirectionalFlow_starts (d : Direction) (initial : InitialAt d) :
    wholeDirectionalFlow d initial 0 = initial.val := windowCurve_starts d initial.val

theorem wholeDirectionalFlow_preserves_first (d : Direction) (initial : InitialAt d) :
    EqOn (firstCurve d initial) (wholeDirectionalFlow d initial) (Icc 0 (stepSize : ℝ)) ∧
    wholeDirectionalFlow d initial stepSize = (firstTarget d initial).val :=
  ⟨window_preserves_first_curve d initial, window_preserves_first_target d initial⟩

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
