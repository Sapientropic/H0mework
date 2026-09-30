import H0mework.Arithmetic.RiemannInverseFibre.ReversalResidual

/-!
# Exact presentation disposition of a generated zero fibre

The generated analytic observer never determines one reversal-presentation
class by itself.  Two explicit lawful preimages survive the chart quotient,
so the partner coordinate is a registered obstruction for the next
source-generated separator.  No representative is chosen.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

noncomputable section

namespace InverseZeroFibre

/-- Concrete evidence that the observer fibre contains more than one
reversal-presentation class. -/
structure NontrivialPresentationResidual
    (observation : GeneratedRiemannZeroObservation) : Type 5 where
  first : InverseZeroFibre observation
  second : InverseZeroFibre observation
  separated :
    ¬ReversalPresentationEquivalent observation first second

/-- The residual is generated explicitly by partner values `0` and `1`; it
does not use a selected centre or a hidden branch bit. -/
def generatedPresentationResidual
    (observation : GeneratedRiemannZeroObservation) :
    NontrivialPresentationResidual observation where
  first := leftPreimage observation 0
  second := leftPreimage observation 1
  separated :=
    leftPreimage_zero_not_reversalPresentationEquivalent_one observation

theorem no_single_reversal_presentation_class
    (observation : GeneratedRiemannZeroObservation) :
    ¬∃ center : InverseZeroFibre observation,
      ∀ candidate,
        ReversalPresentationEquivalent observation candidate center := by
  rintro ⟨center, universal⟩
  have first := universal (leftPreimage observation 0)
  have second := universal (leftPreimage observation 1)
  have equivalent : ReversalPresentationEquivalent observation
      (leftPreimage observation 0) (leftPreimage observation 1) :=
    (reversalPresentationEquivalent_equivalence observation).trans first
      ((reversalPresentationEquivalent_equivalence observation).symm second)
  exact leftPreimage_zero_not_reversalPresentationEquivalent_one
    observation equivalent

/-- The analytic observer's presentation quotient is exactly the partner
residual: equality of residuals is neither weaker nor stronger than the
installed chart-reversal relation. -/
theorem presentation_classes_classified_by_partnerResidual
    (observation : GeneratedRiemannZeroObservation)
    (left right : InverseZeroFibre observation) :
    ReversalPresentationEquivalent observation left right ↔
      partnerResidual left = partnerResidual right :=
  reversalPresentationEquivalent_iff_partnerResidual_eq
    observation left right

end InverseZeroFibre

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
