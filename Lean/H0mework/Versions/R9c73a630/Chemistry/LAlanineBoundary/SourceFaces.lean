import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.SourceModel
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! Six source boundary addresses and their independent oriented flux readout. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary

open SourceGaussianModel WholeCellPartition Set MeasureTheory
open scoped BigOperators
noncomputable section

abbrev Face := Fin 3 × Bool
abbrev FacePoint := Fin 2 → ℝ

def faceDomain (axis : Fin 3) : Set FacePoint :=
  Icc (fullLower ∘ axis.succAbove) (fullUpper ∘ axis.succAbove)
def faceCoordinate (face : Face) : ℝ := if face.2 then fullUpper face.1 else fullLower face.1
def faceParameter (face : Face) (p : FacePoint) : Point := face.1.insertNth (faceCoordinate face) p
def parameterFace (face : Face) : Set Point := faceParameter face '' faceDomain face.1
def spatialFace (face : Face) : Set Point := chart '' parameterFace face

def faceFlux (face : Face) (p : FacePoint) : ℝ :=
  if face.2 then pulledFlux (faceParameter face p) face.1 else -pulledFlux (faceParameter face p) face.1
def faceIntegral (face : Face) : ℝ := ∫ p in faceDomain face.1, faceFlux face p
def netFlux : ℝ := ∑ i : Fin 3, (faceIntegral (i,true) + faceIntegral (i,false))

theorem faceDomain_nonempty (axis : Fin 3) : (faceDomain axis).Nonempty :=
  ⟨fullLower ∘ axis.succAbove, le_rfl,
    fun j => Rat.cast_le.mpr (full_ordered (axis.succAbove j)).le⟩

theorem parameterFace_nonempty (face : Face) : (parameterFace face).Nonempty :=
  (faceDomain_nonempty face.1).image _

theorem spatialFace_nonempty (face : Face) : (spatialFace face).Nonempty :=
  (parameterFace_nonempty face).image _

theorem netFlux_eq_front_minus_back : netFlux = ∑ i : Fin 3,
    ((∫ p in faceDomain i, pulledFlux (i.insertNth (fullUpper i) p) i) -
      ∫ p in faceDomain i, pulledFlux (i.insertNth (fullLower i) p) i) := by
  unfold netFlux faceIntegral faceFlux faceParameter faceCoordinate
  simp only [Bool.false_eq_true, ↓reduceIte, integral_neg, sub_eq_add_neg]

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
