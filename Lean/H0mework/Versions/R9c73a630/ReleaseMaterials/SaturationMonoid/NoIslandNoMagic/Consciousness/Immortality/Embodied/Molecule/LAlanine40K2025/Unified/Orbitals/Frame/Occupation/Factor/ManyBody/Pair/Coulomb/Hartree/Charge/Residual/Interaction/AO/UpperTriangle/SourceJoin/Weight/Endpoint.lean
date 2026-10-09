import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.TargetFull.Outer.Compactify
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
open MeasureTheory Set
noncomputable section

def outerMajorant (c s t : ℝ) : ℝ := 1/((c + s*t^2)*Real.sqrt (c + s*t^2))

def endpointQ (c s u : ℝ) : ℝ := c*(1-u)^2 + s*u^2

def endpointAntiderivative (c s u : ℝ) : ℝ := u/(c*Real.sqrt (endpointQ c s u))

def endpointIntegrand (c s u : ℝ) : ℝ :=
  (1-u)/(endpointQ c s u*Real.sqrt (endpointQ c s u))

theorem endpointQ_pos (c s u : ℝ) (hc : 0 < c) (hs : 0 < s) :
    0 < endpointQ c s u := by
  unfold endpointQ
  by_cases h : u = 1
  · subst h
    simpa using hs
  · have h1 : (1 : ℝ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    exact add_pos_of_pos_of_nonneg
      (mul_pos hc (sq_pos_of_ne_zero h1))
      (mul_nonneg hs.le (sq_nonneg u))

theorem endpointQ_deriv (c s u : ℝ) :
    HasDerivAt (endpointQ c s) (-2*c*(1-u) + 2*s*u) u := by
  have hsub : HasDerivAt (fun u : ℝ => u - 1) 1 u := by
    simpa using (hasDerivAt_id u).sub_const (1 : ℝ)
  have h1 : HasDerivAt (fun u : ℝ => c*(u-1)^2) (c*(2*(u-1)*1)) u := by
    simpa using (hsub.pow 2).const_mul c
  have h2 : HasDerivAt (fun u : ℝ => s*u^2) (s*(2*u)) u := by
    simpa using (hasDerivAt_pow 2 u).const_mul s
  have h := h1.add h2
  exact (h.congr_deriv (by ring)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun x => by unfold endpointQ; simp only [Pi.add_apply]; ring))

theorem endpointDenominator_pos (c s u : ℝ) (hc : 0 < c) (hs : 0 < s) :
    0 < c*Real.sqrt (endpointQ c s u) :=
  mul_pos hc (Real.sqrt_pos.mpr (endpointQ_pos c s u hc hs))

theorem endpointAntiderivative_hasDerivAt (c s u : ℝ) (hc : 0 < c) (hs : 0 < s) :
    HasDerivAt (endpointAntiderivative c s) (endpointIntegrand c s u) u := by
  have hQ : 0 < endpointQ c s u := endpointQ_pos c s u hc hs
  have hQd := endpointQ_deriv c s u
  have hsqrt : HasDerivAt (fun u => Real.sqrt (endpointQ c s u))
      ((-2*c*(1-u) + 2*s*u)/(2*Real.sqrt (endpointQ c s u))) u :=
    hQd.sqrt (ne_of_gt hQ)
  have hden : HasDerivAt (fun u => c*Real.sqrt (endpointQ c s u))
      (c*((-2*c*(1-u) + 2*s*u)/(2*Real.sqrt (endpointQ c s u)))) u :=
    hsqrt.const_mul c
  have hden0 : c*Real.sqrt (endpointQ c s u) ≠ 0 :=
    ne_of_gt (endpointDenominator_pos c s u hc hs)
  have h := (hasDerivAt_id u).div hden hden0
  simp only [id_eq] at h
  have e2 : (1 * (c * Real.sqrt (endpointQ c s u)) -
        u * (c * ((-2*c*(1-u) + 2*s*u)/(2*Real.sqrt (endpointQ c s u))))) /
      (c*Real.sqrt (endpointQ c s u))^2 = endpointIntegrand c s u := by
    unfold endpointIntegrand
    have hs0 : Real.sqrt (endpointQ c s u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
    have sq : Real.sqrt (endpointQ c s u)^2 = endpointQ c s u :=
      Real.sq_sqrt hQ.le
    field_simp
    rw [sq]
    unfold endpointQ
    ring
  rw [e2] at h
  exact h

theorem endpointAntiderivative_zero (c s : ℝ) :
    endpointAntiderivative c s 0 = 0 := by
  unfold endpointAntiderivative endpointQ
  simp

theorem endpointAntiderivative_one (c s : ℝ) :
    endpointAntiderivative c s 1 = 1/(c*Real.sqrt s) := by
  unfold endpointAntiderivative endpointQ
  simp

theorem endpointIntegrand_continuous (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    Continuous (endpointIntegrand c s) := by
  unfold endpointIntegrand
  apply Continuous.div
  · continuity
  · apply Continuous.mul
    · unfold endpointQ
      continuity
    · exact Real.continuous_sqrt.comp (by unfold endpointQ; continuity)
  · intro x
    exact ne_of_gt (mul_pos (endpointQ_pos c s x hc hs)
      (Real.sqrt_pos.mpr (endpointQ_pos c s x hc hs)))

theorem endpointIntegrand_integral (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    ∫ u in (0 : ℝ)..1, endpointIntegrand c s u =
      1/(c*Real.sqrt s) := by
  have hint : IntervalIntegrable (endpointIntegrand c s) volume 0 1 :=
    (endpointIntegrand_continuous c s hc hs).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    (fun u _ => (endpointAntiderivative_hasDerivAt c s u hc hs).continuousAt.continuousWithinAt)
    (fun u _ => endpointAntiderivative_hasDerivAt c s u hc hs) hint]
  rw [endpointAntiderivative_zero c s, endpointAntiderivative_one c s, sub_zero]

theorem outerMajorant_nonneg (c s t : ℝ) (hc : 0 < c) (hs : 0 < s) :
    0 ≤ outerMajorant c s t := by
  unfold outerMajorant
  positivity

theorem outerMajorant_pos (c s t : ℝ) (hc : 0 < c) (hs : 0 < s) :
    0 < outerMajorant c s t := by
  unfold outerMajorant
  positivity

theorem outerMajorant_continuous (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    Continuous (outerMajorant c s) := by
  unfold outerMajorant
  apply Continuous.div continuous_const
  apply Continuous.mul
  · continuity
  · exact Real.continuous_sqrt.comp (by continuity)
  · intro x
    have : 0 < c + s*x^2 := add_pos_of_pos_of_nonneg hc
      (mul_nonneg hs.le (sq_nonneg x))
    exact ne_of_gt (mul_pos this (Real.sqrt_pos.mpr this))

theorem outerMajorant_transformed (c s u : ℝ) (hc : 0 < c) (hs : 0 < s)
    (hu : u < 1) :
    outerMajorant c s (u/(1-u)) / (1-u)^2 = endpointIntegrand c s u := by
  have h1 : (0 : ℝ) < 1 - u := sub_pos.mpr hu
  have hQ : 0 < endpointQ c s u := endpointQ_pos c s u hc hs
  have hkey : c + s*(u/(1-u))^2 = endpointQ c s u/(1-u)^2 := by
    unfold endpointQ
    field_simp
  have hsqrt : Real.sqrt (endpointQ c s u/(1-u)^2) =
      Real.sqrt (endpointQ c s u)/(1-u) := by
    rw [Real.sqrt_div hQ.le, Real.sqrt_sq h1.le]
  unfold outerMajorant endpointIntegrand
  rw [hkey, hsqrt]
  field_simp

theorem outerMajorant_integral (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), outerMajorant c s t = 1/(c*Real.sqrt s) := by
  have htrans : EqOn
      (fun u => outerMajorant c s (u/(1-u))/(1-u)^2)
      (endpointIntegrand c s) (Ioo (0 : ℝ) 1) :=
    fun u hu => outerMajorant_transformed c s u hc hs hu.2
  rw [Laplace.Axis.Moment.Shift.High.TargetFull.Outer.compactify_integral]
  rw [setIntegral_congr_fun measurableSet_Ioo htrans]
  have ae : Ioo (0 : ℝ) 1 =ᵐ[volume] Ioc (0 : ℝ) 1 := Ioo_ae_eq_Ioc
  rw [setIntegral_congr_set ae,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact endpointIntegrand_integral c s hc hs

theorem outerMajorant_integrable (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    IntegrableOn (outerMajorant c s) (Ioi (0 : ℝ)) volume := by
  refine ⟨(outerMajorant_continuous c s hc hs).aestronglyMeasurable, ?_⟩
  have ae_nonneg : ∀ᵐ x ∂volume.restrict (Ioi (0:ℝ)),
      0 ≤ outerMajorant c s x :=
    ae_of_all _ (fun x => outerMajorant_nonneg c s x hc hs)
  have hmeas : AEStronglyMeasurable (outerMajorant c s) (volume.restrict (Ioi (0:ℝ))) :=
    (outerMajorant_continuous c s hc hs).aestronglyMeasurable
  have h := MeasureTheory.integral_eq_lintegral_of_nonneg_ae ae_nonneg hmeas
  rw [outerMajorant_integral c s hc hs] at h
  have hpos : (0 : ℝ) < 1/(c*Real.sqrt s) := by positivity
  have eq_lint : (∫⁻ x, ((‖outerMajorant c s x‖₊ : NNReal) : ENNReal)
      ∂volume.restrict (Ioi (0:ℝ))) =
      ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (outerMajorant c s x) := by
    apply lintegral_congr
    intro x
    have hx := outerMajorant_nonneg c s x hc hs
    rw [ENNReal.ofReal_eq_coe_nnreal hx]
    congr 1
    ext : 1
    simp [Real.norm_eq_abs, abs_of_nonneg hx]
  show (∫⁻ x, ((‖outerMajorant c s x‖₊ : NNReal) : ENNReal)
      ∂volume.restrict (Ioi (0:ℝ))) < ⊤
  rw [eq_lint, lt_top_iff_ne_top]
  intro heq
  rw [heq, ENNReal.toReal_top] at h
  linarith

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
