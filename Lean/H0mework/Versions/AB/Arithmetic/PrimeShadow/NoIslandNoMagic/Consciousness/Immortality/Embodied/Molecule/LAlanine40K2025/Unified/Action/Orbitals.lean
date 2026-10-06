import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.Weighted
import H0mework.Versions.AB.Chemistry.LAlanineGradient.Model

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open BasinRefinement SourceGaussianModel SourceFiniteData
open scoped ContDiff
noncomputable section

/-- The conversion from U's spatial coordinates to the original Bohr coordinates remains explicit. -/
def spatialPoint (scale : ℝ) (p : BasePoint) : Point := fun a => scale * p a.succ

def orbitalWeight (b : Basis) (scale : ℝ) (p : BasePoint) : ℂ :=
  (orbital (sourceTerms b) ContinuousGradient.zeroJet (spatialPoint scale p) : ℂ)

theorem orbitalWeight_smooth (b : Basis) (scale : ℝ) : ContDiff ℝ ∞ (orbitalWeight b scale) := by
  have spatial : ContDiff ℝ ∞ (spatialPoint scale) := by unfold spatialPoint; fun_prop
  exact Complex.ofRealCLM.contDiff.comp ((orbital_contDiff (sourceTerms b) ContinuousGradient.zeroJet ∞).comp spatial)

def orbitalTest (b : Basis) (scale : ℝ) : StageNineHolonomicConfiguration := weighted (orbitalWeight b scale)

theorem original_orbital_covariant (b : Basis) (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative (orbitalTest b scale) p direction =
      orbitalWeight b scale p • holonomicMatterCovariantDerivative Stage10.Runtime.configuration p direction +
        fieldDirectionalDerivative (orbitalWeight b scale) p direction • Stage10.Runtime.configuration.matter p :=
  weighted_covariant_derivative _ p ((orbitalWeight_smooth b scale).differentiable (by simp) p) direction

private theorem line_derivative (p : BasePoint) (direction : LorentzianIndex) :
    HasDerivAt (fun t : ℝ => p + t • coordinateDirection direction) (coordinateDirection direction) 0 := by
  simpa only [one_smul,zero_add] using!
    (hasDerivAt_const (0 : ℝ) p).add ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateDirection direction))

private theorem weight_line_derivative (b : Basis) (scale : ℝ) (p : BasePoint) (direction : LorentzianIndex) :
    HasDerivAt (fun t : ℝ => orbitalWeight b scale (p + t • coordinateDirection direction))
      (fieldDirectionalDerivative (orbitalWeight b scale) p direction) 0 := by
  have outer : HasFDerivAt (orbitalWeight b scale) (fderiv ℝ (orbitalWeight b scale) p)
      (p + (0 : ℝ) • coordinateDirection direction) := by
    simpa only [zero_smul,add_zero] using! ((orbitalWeight_smooth b scale).differentiable (by simp) p).hasFDerivAt
  have h := outer.comp_hasDerivAt 0 (line_derivative p direction)
  simpa only [zero_smul,add_zero] using! h

theorem original_orbital_time_derivative (b : Basis) (scale : ℝ) (p : BasePoint) :
    fieldDirectionalDerivative (orbitalWeight b scale) p 0 = 0 := by
  have same : (fun t : ℝ => orbitalWeight b scale (p+t • coordinateDirection 0)) =
      fun _ => orbitalWeight b scale p := by
    funext t
    apply congrArg (fun x : Point => (orbital (sourceTerms b) ContinuousGradient.zeroJet x : ℂ))
    funext a
    simp [spatialPoint,coordinateDirection]
  have original := weight_line_derivative b scale p 0
  rw [same] at original
  exact original.unique (hasDerivAt_const (0 : ℝ) (orbitalWeight b scale p))

private theorem spatial_line (scale : ℝ) (p : BasePoint) (axis : Fin 3) (t : ℝ) :
    spatialPoint scale (p+t • coordinateDirection axis.succ) =
      Function.update (spatialPoint scale p) axis (spatialPoint scale p axis+scale*t) := by
  funext a
  by_cases same : a = axis
  · subst a
    simp [spatialPoint,coordinateDirection]
    ring
  · simp [spatialPoint,coordinateDirection,same]

theorem original_orbital_spatial_derivative (b : Basis) (scale : ℝ) (p : BasePoint) (axis : Fin 3) :
    fieldDirectionalDerivative (orbitalWeight b scale) p axis.succ =
      (scale * orbital (sourceTerms b) (raise ContinuousGradient.zeroJet axis) (spatialPoint scale p) : ℝ) := by
  let x := spatialPoint scale p
  have inner : HasDerivAt (fun t : ℝ => x axis+scale*t) scale 0 := by
    simpa using! (hasDerivAt_id (0 : ℝ)).const_mul scale |>.const_add (x axis)
  have outer : HasDerivAt (fun t => orbital (sourceTerms b) ContinuousGradient.zeroJet (Function.update x axis t))
      (orbital (sourceTerms b) (raise ContinuousGradient.zeroJet axis) x) (x axis+scale*0) := by
    simpa using! orbital_coordinate_derivative (sourceTerms b) ContinuousGradient.zeroJet x axis
  have raw := outer.comp 0 inner
  have complex := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 raw
  have actual : HasDerivAt (fun t : ℝ => orbitalWeight b scale (p+t • coordinateDirection axis.succ))
      ((scale * orbital (sourceTerms b) (raise ContinuousGradient.zeroJet axis) x : ℝ) : ℂ) 0 := by
    convert! complex using 1
    · funext t
      change (orbital (sourceTerms b) ContinuousGradient.zeroJet (spatialPoint scale (p+t • coordinateDirection axis.succ)) : ℂ) = _
      rw [spatial_line]
      rfl
    · simp only [Complex.ofRealCLM_apply,Complex.ofReal_mul,mul_comm]
  exact (weight_line_derivative b scale p axis.succ).unique actual

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
