import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.SourceDivergenceConsumer

/-! Each quarter restricts the same flux; opposite internal faces cancel as actual integrals. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary

open SourceGaussianModel WholeCellPartition Set MeasureTheory
open scoped BigOperators
noncomputable section

def quarterFaceDomain (q : Quarter) (axis : Fin 3) : Set FacePoint :=
  Icc (quarterLower q ∘ axis.succAbove) (quarterUpper q ∘ axis.succAbove)
def quarterFaceParameter (q : Quarter) (face : Face) (p : FacePoint) : Point :=
  face.1.insertNth (if face.2 then quarterUpper q face.1 else quarterLower q face.1) p
def quarterFaceFlux (q : Quarter) (face : Face) (p : FacePoint) : ℝ :=
  if face.2 then pulledFlux (quarterFaceParameter q face p) face.1
  else -pulledFlux (quarterFaceParameter q face p) face.1
def quarterFaceIntegral (q : Quarter) (face : Face) : ℝ :=
  ∫ p in quarterFaceDomain q face.1, quarterFaceFlux q face p
def quarterNetFlux (q : Quarter) : ℝ :=
  ∑ i : Fin 3, (quarterFaceIntegral q (i,true) + quarterFaceIntegral q (i,false))

def seamBefore (i : Fin 3) : Quarter := i.castSucc
def seamAfter (i : Fin 3) : Quarter := i.succ

theorem quarterNetFlux_eq_divergence (smooth : ContDiff ℝ 1 pulledFlux) (q : Quarter) :
    quarterNetFlux q = ∫ p in quarterDomain q, ∑ i : Fin 3, fderiv ℝ pulledFlux p (Pi.single i 1) i := by
  have gauss := (integral_divergence_of_hasFDerivAt_off_countable (quarterLower q) (quarterUpper q)
    (fun i => Rat.cast_le.mpr (quarter_ordered q i).le) pulledFlux (fderiv ℝ pulledFlux)
    ∅ countable_empty smooth.continuous.continuousOn
    (fun p _ => (smooth.differentiable (by norm_num) p).hasFDerivAt)
    ((flux_divergence_continuous smooth).continuousOn.integrableOn_compact (quarter_compact q))).symm
  simpa only [quarterNetFlux, quarterFaceIntegral, quarterFaceFlux, quarterFaceParameter,
    quarterFaceDomain, quarterDomain, Bool.false_eq_true, ↓reduceIte, integral_neg, sub_eq_add_neg] using gauss

theorem seam_coordinate : ∀ i : Fin 3, quarterUpperQ (seamBefore i) 2 = quarterLowerQ (seamAfter i) 2 := by
  decide +kernel

theorem seam_domain (i : Fin 3) :
    quarterFaceDomain (seamBefore i) 2 = quarterFaceDomain (seamAfter i) 2 := by
  unfold quarterFaceDomain
  congr 1
  all_goals
    funext j
    fin_cases j <;> rfl

theorem seam_parameter (i : Fin 3) (p : FacePoint) :
    quarterFaceParameter (seamBefore i) (2,true) p = quarterFaceParameter (seamAfter i) (2,false) p := by
  unfold quarterFaceParameter
  simp only [↓reduceIte]
  congr 1

theorem seam_flux_opposite (i : Fin 3) (p : FacePoint) :
    quarterFaceFlux (seamBefore i) (2,true) p = -quarterFaceFlux (seamAfter i) (2,false) p := by
  simp only [quarterFaceFlux, Bool.false_eq_true, ↓reduceIte, neg_neg, seam_parameter]

theorem seam_integral_cancels (i : Fin 3) :
    quarterFaceIntegral (seamBefore i) (2,true) + quarterFaceIntegral (seamAfter i) (2,false) = 0 := by
  unfold quarterFaceIntegral
  rw [seam_domain]
  have equal : quarterFaceFlux (seamBefore i) (2,true) = -quarterFaceFlux (seamAfter i) (2,false) :=
    funext (seam_flux_opposite i)
  rw [equal]
  simp only [Pi.neg_apply, integral_neg, neg_add_cancel]

theorem all_three_seams_cancel :
    ∑ i : Fin 3, (quarterFaceIntegral (seamBefore i) (2,true) +
      quarterFaceIntegral (seamAfter i) (2,false)) = 0 := by
  simp only [seam_integral_cancels, Finset.sum_const_zero]

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
