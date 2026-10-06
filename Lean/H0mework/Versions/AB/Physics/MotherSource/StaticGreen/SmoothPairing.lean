import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Source
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory
open scoped ContDiff SchwartzMap LineDeriv
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel
noncomputable section

def spatialFirst (f : Point → ℝ) (index : Fin 3) (point : Point) : ℝ :=
  fderiv ℝ f point (axis index)

def spatialLap (f : Point → ℝ) (point : Point) : ℝ :=
  ∑ index : Fin 3, spatialFirst (spatialFirst f index) index point

theorem spatialFirst_smooth {f : Point → ℝ} (smooth : ContDiff ℝ ∞ f) (index : Fin 3) :
    ContDiff ℝ ∞ (spatialFirst f index) :=
  (contDiff_infty_iff_fderiv.mp smooth).2.clm_apply contDiff_const

theorem spatialLap_smooth {f : Point → ℝ} (smooth : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (spatialLap f) :=
  ContDiff.sum (fun index _ => spatialFirst_smooth (spatialFirst_smooth smooth index) index)

theorem compact_mul_integrable {f g : Point → ℝ} (hf : Continuous f) (hg : Continuous g)
    (support : HasCompactSupport g) : Integrable (fun point => f point*g point) :=
  (hf.mul hg).integrable_of_hasCompactSupport support.mul_left

theorem compact_first_support {g : Point → ℝ} (support : HasCompactSupport g) (index : Fin 3) :
    HasCompactSupport (spatialFirst g index) := support.fderiv_apply ℝ (axis index)

theorem compact_pairing_first {f g : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (support : HasCompactSupport g) (index : Fin 3) :
    (∫ point, f point*spatialFirst g index point) = -(∫ point, spatialFirst f index point*g point) := by
  exact integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (compact_mul_integrable (spatialFirst_smooth hf index).continuous hg.continuous support)
    (compact_mul_integrable hf.continuous (spatialFirst_smooth hg index).continuous
      (compact_first_support support index))
    (compact_mul_integrable hf.continuous hg.continuous support)
    (fun point _ => ((hf.differentiable (by simp)) point).hasFDerivAt.hasLineDerivAt (axis index))
    (fun point _ => ((hg.differentiable (by simp)) point).hasFDerivAt.hasLineDerivAt (axis index))

theorem compact_pairing_second {f g : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (support : HasCompactSupport g) (index : Fin 3) :
    (∫ point, f point*spatialFirst (spatialFirst g index) index point) =
      ∫ point, spatialFirst (spatialFirst f index) index point*g point := by
  rw [compact_pairing_first hf (spatialFirst_smooth hg index) (compact_first_support support index),
    compact_pairing_first (spatialFirst_smooth hf index) hg support, neg_neg]

theorem compact_pairing_laplacian {f g : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (support : HasCompactSupport g) :
    (∫ point, f point*spatialLap g point) = ∫ point, spatialLap f point*g point := by
  simp only [spatialLap, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun index _ =>
    compact_mul_integrable hf.continuous (spatialFirst_smooth (spatialFirst_smooth hg index) index).continuous
      (compact_first_support (compact_first_support support index) index))]
  simp_rw [compact_pairing_second hf hg support]
  rw [integral_finsetSum Finset.univ (fun index _ =>
    compact_mul_integrable (spatialFirst_smooth (spatialFirst_smooth hf index) index).continuous hg.continuous support)]

theorem spatialLap_test (test : 𝓢(Point, ℝ)) : spatialLap test = testLaplacian test := by
  funext point
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
