import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.Operator.ClozelBurnolRechartedOperatorDerivative
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.BoundaryCosineSource
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology

def phase (radius x y : ℝ) : ℂ :=
  Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (radius : ℂ)^2 * (x : ℂ) * (y : ℂ))
def squareKernel (radius x y : ℝ) : ℂ :=
  ∫ t : ℝ in -(radius^2)..radius^2,
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * ((x+y : ℝ) : ℂ))
def cosineRaw (radius x : ℝ) : ℂ := burnolRadiusBoundaryCosineRaw radius x
def sineRaw (radius x : ℝ) : ℂ := ((2 * Real.sin (2 * Real.pi * radius^2 * x) : ℝ) : ℂ)

theorem endpoint_phase (radius x y : ℝ) :
    phase radius 1 (x+y) + phase radius (-1) (x+y) =
      (1/2 : ℂ) * (cosineRaw radius x * cosineRaw radius y - sineRaw radius x * sineRaw radius y) := by
  unfold phase cosineRaw sineRaw burnolRadiusBoundaryCosineRaw
  have plus : -2 * (Real.pi : ℂ) * Complex.I * (radius : ℂ)^2 * (1 : ℂ) * ((x+y : ℝ) : ℂ) =
      ((-(2 * Real.pi * radius^2 * (x+y)) : ℝ) : ℂ) * Complex.I := by push_cast;ring
  have minus : -2 * (Real.pi : ℂ) * Complex.I * (radius : ℂ)^2 * ((-1 : ℝ) : ℂ) * ((x+y : ℝ) : ℂ) =
      ((2 * Real.pi * radius^2 * (x+y) : ℝ) : ℂ) * Complex.I := by push_cast;ring
  norm_num only [Complex.ofReal_one] at *
  rw [plus,minus,Complex.exp_mul_I,Complex.exp_mul_I]
  rw [← Complex.ofReal_cos,← Complex.ofReal_sin,← Complex.ofReal_cos,← Complex.ofReal_sin]
  simp only [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]
  have angle : 2 * Real.pi * radius^2 * (x+y) = 2 * Real.pi * radius^2*x + 2 * Real.pi * radius^2*y := by ring
  rw [angle,Real.cos_add]
  push_cast
  ring

theorem square_kernel_derivative (radius x y : ℝ) :
    HasDerivAt (fun r : ℝ => squareKernel r x y)
      ((radius : ℂ) * (cosineRaw radius x * cosineRaw radius y - sineRaw radius x * sineRaw radius y)) radius := by
  let f : ℝ → ℂ := fun t => Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * ((x+y : ℝ) : ℂ))
  have continuous : Continuous f := by fun_prop
  have right := intervalIntegral.integral_hasDerivAt_right
    (continuous.intervalIntegrable 0 (radius^2))
    (continuous.stronglyMeasurableAtFilter volume _) continuous.continuousAt
  have square : HasDerivAt (fun r : ℝ => r^2) (2*radius) radius := by simpa using hasDerivAt_pow 2 radius
  have rightComp := HasFDerivAt.comp_hasDerivAt_of_eq radius right.hasFDerivAt square rfl
  have left := intervalIntegral.integral_hasDerivAt_right
    (continuous.intervalIntegrable 0 (-(radius^2)))
    (continuous.stronglyMeasurableAtFilter volume _) continuous.continuousAt
  have leftComp := HasFDerivAt.comp_hasDerivAt_of_eq radius left.hasFDerivAt square.neg rfl
  have actual := rightComp.sub leftComp
  have fixed : (fun r : ℝ => (∫ t : ℝ in 0..r^2,f t) - (∫ t : ℝ in 0..(-(r^2)),f t)) =
      fun r : ℝ => squareKernel r x y := by
    funext r
    rw [intervalIntegral.integral_interval_sub_left
      (continuous.intervalIntegrable _ _) (continuous.intervalIntegrable _ _)]
    rfl
  change HasDerivAt (fun r : ℝ => (∫ t : ℝ in 0..r^2,f t) - (∫ t : ℝ in 0..(-(r^2)),f t)) _ radius at actual
  rw [fixed] at actual
  convert! actual using 1
  dsimp only [f]
  have source := endpoint_phase radius x y
  change _ = (2*radius : ℝ) • Complex.exp (-2*(Real.pi:ℂ)*Complex.I*((radius^2:ℝ):ℂ)*((x+y:ℝ):ℂ)) -
      (-(2*radius) : ℝ) • Complex.exp (-2*(Real.pi:ℂ)*Complex.I*((-(radius^2):ℝ):ℂ)*((x+y:ℝ):ℂ))
  have first : Complex.exp (-2*(Real.pi:ℂ)*Complex.I*((radius^2:ℝ):ℂ)*((x+y:ℝ):ℂ)) = phase radius 1 (x+y) := by
    unfold phase
    congr 1
    push_cast
    ring
  have second : Complex.exp (-2*(Real.pi:ℂ)*Complex.I*((-(radius^2):ℝ):ℂ)*((x+y:ℝ):ℂ)) = phase radius (-1) (x+y) := by
    unfold phase
    congr 1
    push_cast
    ring
  rw [first,second]
  simp only [real_smul]
  rw [show ((2*radius : ℝ) : ℂ) * phase radius 1 (x+y) -
      ((-(2*radius) : ℝ) : ℂ) * phase radius (-1) (x+y) =
      ((2*radius : ℝ) : ℂ) * (phase radius 1 (x+y)+phase radius (-1) (x+y)) by push_cast;ring,source]
  push_cast
  ring

theorem square_kernel_finite (q r x y : ℝ) :
    squareKernel r x y - squareKernel q x y =
      ∫ t : ℝ in q..r, (t : ℂ) * (cosineRaw t x * cosineRaw t y - sineRaw t x * sineRaw t y) := by
  have regular : Continuous (fun t : ℝ => (t : ℂ) *
      (cosineRaw t x * cosineRaw t y - sineRaw t x * sineRaw t y)) := by
    unfold cosineRaw sineRaw burnolRadiusBoundaryCosineRaw
    fun_prop
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => square_kernel_derivative t x y) (regular.intervalIntegrable q r)).symm

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
