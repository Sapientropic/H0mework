import H0mework.Chemistry.LAlanineSourceMatrix.AllData
import H0mework.Chemistry.LAlanineContinuousChecks.AOComplete
import H0mework.Chemistry.LAlanineSourceField01.CacheComplete
import H0mework.Chemistry.LAlanineSourceField02.CacheComplete
import H0mework.Chemistry.LAlanineSourceField03.CacheComplete
import H0mework.Chemistry.LAlanineSourceField04.CacheComplete
import H0mework.Chemistry.LAlanineSourceField05.CacheComplete
import H0mework.Chemistry.LAlanineSourceField06.CacheComplete
import H0mework.Chemistry.LAlanineSourceField07.CacheComplete
import H0mework.Chemistry.LAlanineSourceField08.CacheComplete
import H0mework.Chemistry.LAlanineSourceField09.CacheComplete
import H0mework.Chemistry.LAlanineSourceField10.CacheComplete
import H0mework.Chemistry.LAlanineSourceField11.CacheComplete
import H0mework.Chemistry.LAlanineSourceField12.CacheComplete
import H0mework.Chemistry.LAlanineSourceField13.CacheComplete
import H0mework.Chemistry.LAlanineSourceField14.CacheComplete
import H0mework.Chemistry.LAlanineSourceField15.CacheComplete
import H0mework.Chemistry.LAlanineSourceField16.CacheComplete

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields.AllFields

open SourceRectangle SourceSignedEvaluator SourceGaussianModel SourceFiniteData

theorem calculatedAO_eq_orbitalPair (f : Field) (j : LowJet) (basis : Basis) :
    calculatedAO f j basis =
      orbitalPair (source_terms basis) (multiindex (fullJet j)) (actualBox f) (steps f) := by
  fin_cases f
  · exact SourceRectangleChecks.calculatedAO_eq_orbitalPair (fullJet j) basis
  · exact Field1.calculatedAO_eq_orbitalPair j basis
  · exact Field2.calculatedAO_eq_orbitalPair j basis
  · exact Field3.calculatedAO_eq_orbitalPair j basis
  · exact Field4.calculatedAO_eq_orbitalPair j basis
  · exact Field5.calculatedAO_eq_orbitalPair j basis
  · exact Field6.calculatedAO_eq_orbitalPair j basis
  · exact Field7.calculatedAO_eq_orbitalPair j basis
  · exact Field8.calculatedAO_eq_orbitalPair j basis
  · exact Field9.calculatedAO_eq_orbitalPair j basis
  · exact Field10.calculatedAO_eq_orbitalPair j basis
  · exact Field11.calculatedAO_eq_orbitalPair j basis
  · exact Field12.calculatedAO_eq_orbitalPair j basis
  · exact Field13.calculatedAO_eq_orbitalPair j basis
  · exact Field14.calculatedAO_eq_orbitalPair j basis
  · exact Field15.calculatedAO_eq_orbitalPair j basis
  · exact Field16.calculatedAO_eq_orbitalPair j basis

theorem calculatedAO_contains (f : Field) (j : LowJet) (basis : Basis) (x : Point)
    (inside : InRectangle (actualBox f) x) :
    Holds (calculatedAO f j basis) (orbital (source_terms basis) (multiindex (fullJet j)) x) := by
  fin_cases f
  · exact SourceRectangleChecks.calculatedAO_contains (fullJet j) basis x inside
  · exact Field1.calculatedAO_contains j basis x inside
  · exact Field2.calculatedAO_contains j basis x inside
  · exact Field3.calculatedAO_contains j basis x inside
  · exact Field4.calculatedAO_contains j basis x inside
  · exact Field5.calculatedAO_contains j basis x inside
  · exact Field6.calculatedAO_contains j basis x inside
  · exact Field7.calculatedAO_contains j basis x inside
  · exact Field8.calculatedAO_contains j basis x inside
  · exact Field9.calculatedAO_contains j basis x inside
  · exact Field10.calculatedAO_contains j basis x inside
  · exact Field11.calculatedAO_contains j basis x inside
  · exact Field12.calculatedAO_contains j basis x inside
  · exact Field13.calculatedAO_contains j basis x inside
  · exact Field14.calculatedAO_contains j basis x inside
  · exact Field15.calculatedAO_contains j basis x inside
  · exact Field16.calculatedAO_contains j basis x inside

theorem actual_D3_bilinear_contains (f : Field) (j k : LowJet) (x : Point)
    (inside : InRectangle (actualBox f) x) :
    Holds (bilinearPair (calculatedAO f j) (calculatedAO f k) source_matrix)
      (bilinear source_terms source_matrix (multiindex (fullJet j)) (multiindex (fullJet k)) x) :=
  bilinearPair_contains (calculatedAO f j) (calculatedAO f k) source_matrix source_terms
    (multiindex (fullJet j)) (multiindex (fullJet k)) x
    (fun basis => calculatedAO_contains f j basis x inside)
    (fun basis => calculatedAO_contains f k basis x inside)

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields.AllFields
