import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Pure paired Mellin character

The half-density dilation character and its reciprocal are ordinary scalar
coordinates.  This file deliberately imports no Burnol operator occurrence,
physical landing, kernel event, or analytic-zero source.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex

noncomputable section

/-- Full logarithmic character in half-density normalization. -/
def fullMellinTranslationCharacter (coordinate : ℂ) (shift : ℝ) : ℂ :=
  Complex.exp (((1 / 2 : ℂ) - coordinate) * (shift : ℂ))

/-- Character of the inverse dilation. -/
def reciprocalMellinTranslationCharacter
    (coordinate : ℂ) (shift : ℝ) : ℂ :=
  Complex.exp ((coordinate - (1 / 2 : ℂ)) * (shift : ℂ))

/-- Fourier-fixed pairing of forward and inverse dilation characters. -/
def pairedMellinTranslationCharacter (coordinate : ℂ) (shift : ℝ) : ℂ :=
  (fullMellinTranslationCharacter coordinate shift +
    reciprocalMellinTranslationCharacter coordinate shift) / 2

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
