import H0mework.Chemistry.LAlanineBandInputs.Calculations

/-! Source-fixed input family for the original Root64 calculation face.
The original M3 Gaussian functions and registered rectangles generate these bounds;
no density report, flow, endpoint or new physical clock is an input. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGeneratedInputs

open SourceGaussianModel SourceSignedEvaluator SourceExponential SourceRectangle
open WholeBandSource WholeBandSaturation

theorem all_reductions_valid (f : FullBandCall) (g : Group) :
    TermReductionValid (groupTerm g) (callBox f)
      (callReductions f g).1 (callReductions f g).2 :=
  (all_calculations f).reductions_valid g

theorem all_saturated_inputs (f : FullBandCall) (s : SaturatedGroup) :
    InputBounds (callBox f) (callReductions f) (groupAt s) :=
  (all_calculations f).saturated_inputs s

theorem all_exponential_saturated (f : FullBandCall) (s : SaturatedGroup) :
    exponential (radialPair (groupTerm (groupAt s)) (callBox f))
      (callReductions f (groupAt s)).1 (callReductions f (groupAt s)).2 = (0, 1/scale) :=
  exponential_eq _ _ _ (all_saturated_inputs f s)

theorem all_actual_exponentials (f : FullBandCall) (g : Group) (x : Point)
    (inside : InRectangle (callBox f) x) :
    Holds (exponential (radialPair (groupTerm g) (callBox f))
      (callReductions f g).1 (callReductions f g).2) (Real.exp (radialArgument (groupTerm g) x)) :=
  exponential_holds _ _ _ (all_reductions_valid f g).1 (all_reductions_valid f g).2 _
    (radialPair_contains _ _ x inside)

theorem all_saturated_actual_exponential (f : FullBandCall) (s : SaturatedGroup) (x : Point)
    (inside : InRectangle (callBox f) x) :
    Holds (0, 1/scale) (Real.exp (radialArgument (groupTerm (groupAt s)) x)) := by
  rw [← all_exponential_saturated f s]
  exact all_actual_exponentials f (groupAt s) x inside

end LAlanine40K2025.BasinRefinement.WholeBandGeneratedInputs
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
