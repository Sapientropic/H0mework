import H0mework.Physics.Homogeneous.Cartan
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Dynamics.Homogeneous
open ProofFreeRicherAnholonomicSource
noncomputable section

open scoped Matrix.Norms.Operator in
theorem coframeInverse_line_hasDerivAt (coframe direction : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    HasDerivAt (fun t : ℝ => (coframe + t • direction)⁻¹)
      (-(coframe⁻¹ * direction * coframe⁻¹)) 0 := by
  have unit : IsUnit coframe :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr nondegenerate)
  obtain ⟨u, rfl⟩ := unit
  have line : HasDerivAt (fun t : ℝ => (u : LorentzianCoframe) + t • direction) direction 0 := by
    convert! ((hasDerivAt_id (x := (0 : ℝ))).smul_const direction).const_add
      (u : LorentzianCoframe) using 1; first | rfl | simp
  have ringInverse : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ LorentzianCoframe (u⁻¹ : LorentzianCoframeˣ) (u⁻¹ : LorentzianCoframeˣ))
      ((u : LorentzianCoframe) + (0 : ℝ) • direction) := by
    simpa only [zero_smul, add_zero] using hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have inverse := ringInverse.comp_hasDerivAt 0 line
  convert! inverse using 1 <;> first
    | rfl
    | simp only [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit,
        neg_apply, ContinuousLinearMap.mulLeftRight_apply] <;> rfl

open scoped Matrix.Norms.Elementwise in
theorem coframe_line_hasDerivAt (coframe direction : LorentzianCoframe) :
    HasDerivAt (fun t : ℝ => coframe + t • direction) direction 0 := by
  convert! ((hasDerivAt_id (x := (0 : ℝ))).smul_const direction).const_add coframe using 1;
    first | rfl | simp

open StageNineCartanTangentSimplicityResponse in
theorem coframeWedge_hasDerivAt
    (curve : ℝ → LorentzianCoframe) (velocity : LorentzianCoframe) (parameter : ℝ)
    (derivative : HasDerivAt curve velocity parameter) (internalPair spacetimePair : Fin 6) :
    HasDerivAt (fun t => coframeWedge (curve t) internalPair spacetimePair)
      (coframeWedgeTangent (curve parameter) velocity internalPair spacetimePair) parameter := by
  have entry (row column : LorentzianIndex) :
      HasDerivAt (fun t => curve t row column) (velocity row column) parameter :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp derivative row) column
  have first := (entry (pairFirst internalPair) (pairFirst spacetimePair)).mul
    (entry (pairSecond internalPair) (pairSecond spacetimePair))
  have second := (entry (pairFirst internalPair) (pairSecond spacetimePair)).mul
    (entry (pairSecond internalPair) (pairFirst spacetimePair))
  convert! first.sub second using 1; first
    | rfl
    | (simp only [coframeWedgeTangent]; ring)

open StageNineCartanTangentSimplicityResponse StageNineGlobalIntegratedAction
  EmpiricalReferenceScaleCouplingBoundary StageNineBlockwiseConstitutive

def coframeTwoFormTangent (coframe velocity : LorentzianCoframe)
    (form : GaugeTwoForm) : GaugeTwoForm := fun output =>
  ∑ input : Fin 6, coframeWedgeTangent coframe velocity output input * form input

theorem coframeTwoFormLinear_hasDerivAt
    (curve : ℝ → LorentzianCoframe) (velocity : LorentzianCoframe) (parameter : ℝ)
    (derivative : HasDerivAt curve velocity parameter) (form : GaugeTwoForm) (output : Fin 6) :
    HasDerivAt (fun t => coframeTwoFormLinear (curve t) form output)
      (coframeTwoFormTangent (curve parameter) velocity form output) parameter := by
  have summed := HasDerivAt.fun_sum (u := Finset.univ)
    (fun input _ => (coframeWedge_hasDerivAt curve velocity parameter derivative output input).mul_const
      (form input))
  convert! summed using 1

private theorem lorentzianHodge_hasDerivAt
    (curve : ℝ → GaugeTwoForm) (velocity : GaugeTwoForm) (parameter : ℝ)
    (derivative : ∀ output, HasDerivAt (fun t => curve t output) (velocity output) parameter)
    (output : Fin 6) :
    HasDerivAt (fun t => lorentzianCoframeHodge (curve t) output)
      (lorentzianCoframeHodge velocity output) parameter := by
  fin_cases output
  · exact derivative 3
  · exact derivative 4
  · exact derivative 5
  · exact (derivative 0).neg
  · exact (derivative 1).neg
  · exact (derivative 2).neg

def coframeHodgeTangent (coframe velocity : LorentzianCoframe) (form : GaugeTwoForm) : GaugeTwoForm :=
  coframeTwoFormTangent coframe⁻¹ (-(coframe⁻¹ * velocity * coframe⁻¹))
      (lorentzianCoframeHodge (coframeTwoFormLinear coframe form)) +
    coframeTwoFormLinear coframe⁻¹
      (lorentzianCoframeHodge (coframeTwoFormTangent coframe velocity form))

theorem coframeHodge_line_hasDerivAt (coframe velocity : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) (form : GaugeTwoForm) (output : Fin 6) :
    HasDerivAt (fun t : ℝ => coframeGaugeSpacetimeHodgeLinear (coframe + t • velocity) form output)
      (coframeHodgeTangent coframe velocity form output) 0 := by
  have primal := coframe_line_hasDerivAt coframe velocity
  have inverse := coframeInverse_line_hasDerivAt coframe velocity nondegenerate
  have first (index : Fin 6) :=
    coframeWedge_hasDerivAt _ _ 0 inverse output index
  have second (index : Fin 6) :=
    lorentzianHodge_hasDerivAt _ _ 0
      (fun component => coframeTwoFormLinear_hasDerivAt _ _ 0 primal form component) index
  have product (index : Fin 6) := (first index).mul (second index)
  have summed := HasDerivAt.fun_sum (u := Finset.univ) (fun index _ => product index)
  convert! summed using 1; first
    | rfl
    | (simp only [coframeHodgeTangent, coframeTwoFormTangent, coframeTwoFormLinear,
        Pi.add_apply, zero_smul, add_zero, Finset.sum_add_distrib]; rfl)

end
end SaturationMonoid.PhysicsCore.Stage9C.Dynamics.Homogeneous
