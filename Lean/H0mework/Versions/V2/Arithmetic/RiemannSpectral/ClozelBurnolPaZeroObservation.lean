import H0mework.Versions.V2.Arithmetic.RiemannSpectral.PaDiagonalBoundary

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

noncomputable section

def burnolPaZeroObservation
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    GeneratedRiemannZeroObservation :=
  GeneratedRiemannZeroObservation.ofMathlibZero coordinate.value zero

theorem burnolPaZeroObservation_nontrivial
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    ¬ ∃ n : Nat, (burnolPaZeroObservation coordinate zero).coordinate =
      -2 * (n + 1) := by
  rintro ⟨n, equality⟩
  have realEquality := congrArg Complex.re equality
  change coordinate.value.re = (-2 * ((n : ℂ) + 1)).re at realEquality
  norm_num at realEquality
  linarith [coordinate.rightHalf]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
