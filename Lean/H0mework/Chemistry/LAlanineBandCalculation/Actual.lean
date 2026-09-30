import H0mework.Chemistry.LAlanineBandCalculation.Family
import H0mework.Chemistry.LAlanineBandInputs.Producer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation
open SourceRectangle SourceGaussianModel SourceSignedEvaluator SourceFiniteData SourceFields SourceIntegerGrid WholeBandSource
noncomputable section

/-- Every original evaluator is sound from its own registered source inputs. -/
theorem all_original_orbitals (f : FullBandCall) (j : LowJet) (b : Basis) (x : Point)
    (inside : InRectangle (callBox f) x) :
    Holds (grid (originalAO f j b)) (orbital (source_terms b) (multiindex (fullJet j)) x) :=
  original_orbitals_contain f (WholeBandGeneratedInputs.all_reductions_valid f) j b x inside

theorem all_original_fields (f : FullBandCall) (x : Point) (inside : InRectangle (callBox f) x) :
    IntervalParameterMap.FieldHolds (originalField f) x :=
  original_fields_contain f (WholeBandGeneratedInputs.all_reductions_valid f) x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
