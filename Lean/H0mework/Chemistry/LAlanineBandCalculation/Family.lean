import H0mework.Chemistry.LAlanineBandCalculation.Orbitals
import H0mework.Chemistry.LAlanineBandCalculation.Matrix
import H0mework.Chemistry.LAlanineBandSource.Data

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation

open SourceSignedEvaluator SourceIntegerGrid SourceGaussianModel SourceRectangle SourceFiniteData SourceFields
open WholeBandSource WholeBandMatrix
noncomputable section

/-- Same original source family; report recognition occurs only after these computations. -/
def originalExp (f : FullBandCall) (g : Group) : Pair :=
  exponential (radialPair (groupTerm g) (callBox f)) (callReductions f g).1 (callReductions f g).2

def originalPoly (f : FullBandCall) (g : Group) (axis p : Fin 3) (d : Fin 4) : Pair :=
  jetHorner (groupTerm g).exponent p.val d.val (relative (groupTerm g) (callBox f) axis)

def originalAO (f : FullBandCall) (j : LowJet) (b : Basis) : Interval :=
  orbitalIntegers (originalExp f) (originalPoly f) b j

def originalRows (f : FullBandCall) : Rows := matrixRows (originalAO f)
def originalField (f : FullBandCall) : IntervalParameterMap.FieldBox := calculatedField (originalRows f)

 theorem original_matrix_certificate (f : FullBandCall) :
    RowsCertificate (originalRows f) (fun j b => grid (originalAO f j b)) :=
  matrix_certificate (originalAO f)

 theorem original_orbitals_contain (f : FullBandCall)
    (valid : ∀ g, TermReductionValid (groupTerm g) (callBox f) (callReductions f g).1 (callReductions f g).2)
    (j : LowJet) (b : Basis) (x : Point) (inside : InRectangle (callBox f) x) :
    Holds (grid (originalAO f j b)) (orbital (source_terms b) (multiindex (fullJet j)) x) := by
  rw [originalAO,orbital_integers_commute]
  exact WholeCellSource.source_group_orbital_contains (callBox f) (callReductions f)
    (originalExp f) (originalPoly f) (fun _ => rfl) (fun _ _ _ _ => rfl) valid b (fullJet j) x inside

 theorem original_fields_contain (f : FullBandCall)
    (valid : ∀ g, TermReductionValid (groupTerm g) (callBox f) (callReductions f g).1 (callReductions f g).2)
    (x : Point) (inside : InRectangle (callBox f) x) : IntervalParameterMap.FieldHolds (originalField f) x :=
  fieldHolds_of_rows (callBox f) (fun j b => grid (originalAO f j b)) (originalRows f)
    (original_matrix_certificate f) (fun j b y hy => original_orbitals_contain f valid j b y hy) x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
