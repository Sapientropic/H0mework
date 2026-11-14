import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SingleSlotPriceInverse
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Rat.Denumerable

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.PhysicalPriceGrid

open BurnolPhysicalState Set Filter MeasureTheory
open scoped InnerProductSpace
open private probe positive_weight_integrable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.MellinSeparation
open private original_K_separates from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SingleSlotPriceInverse

private theorem probe_real (y : ℝ) : (probe y).value.re = 3/4 := by
  norm_num [probe, Complex.add_re, Complex.mul_re]

private theorem probe_of_coordinate (d : BurnolCompletedMellinCoordinate) (line : d.value.re = 3/4) :
    probe (d.value.im / (2 * Real.pi)) = d := by
  have value : (probe (d.value.im / (2 * Real.pi))).value = d.value := by
    apply Complex.ext
    · rw [probe_real, line]
    · have realConstant : ((3/4 : ℂ)).im = 0 := by norm_num [Complex.div_im]
      have imaginary (y : ℝ) : (probe y).value.im = 2 * Real.pi * y := by
        simp only [probe, Complex.add_im, realConstant, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
      rw [imaginary]
      field_simp [Real.pi_ne_zero]
  generalize same : probe (d.value.im / (2 * Real.pi)) = c at value ⊢
  cases c
  cases d
  cases value
  rfl

private theorem continuous_probe_price (v : BurnolPaAmbientCarrier) :
    Continuous (fun y : ℝ => burnolCompletedMellinEvaluator (probe y) v) := by
  let weight (y x : ℝ) := (x : ℂ)^(-(probe y).value) * (v : BurnolL2) x
  have int (y : ℝ) : IntegrableOn (weight y) (Ioi 0) :=
    positive_weight_integrable (probe y) (v : BurnolL2) v.property.1.1
  have actual (y : ℝ) :
      burnolCompletedMellinEvaluator (probe y) v = ∫ x in Ioi 0, weight y x := by
    have restricted := congrArg (fun f : BurnolPaAmbientCarrier →L[ℂ] ℂ => f v)
      (burnolAmbientCompletedMellinEvaluator_restrict (probe y))
    exact restricted.symm.trans
      (burnolAmbientCompletedMellinEvaluator_eq_positive_integral_of_positionGap (probe y)
        (v : BurnolL2) v.property.1.1)
  rw [funext actual]
  refine continuous_of_dominated (μ := volume.restrict (Ioi (0 : ℝ))) (F := weight)
    (bound := fun x => ‖weight 0 x‖) (fun y => (int y).aestronglyMeasurable) ?_ (int 0).norm ?_
  · intro y
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have pos : 0 < x := hx
    simp only [weight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos pos, Complex.neg_re, probe_real]
    exact le_rfl
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have pos : 0 < x := hx
    have exponent : Continuous (fun y : ℝ => -(probe y).value) := by
      change Continuous (fun y : ℝ => -((3/4 : ℂ) + ((2*Real.pi*y : ℝ) : ℂ) * Complex.I))
      fun_prop
    exact (exponent.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr pos.ne'))).mul continuous_const

/-- Every rational height is read again after every cutoff. -/
def height (i : Nat) : ℝ :=
  ((Denumerable.eqv ℚ).symm (Nat.unpair i).1 : ℚ)

def coordinate (i : Nat) : BurnolCompletedMellinCoordinate :=
  probe (height i)

def price (i : Nat) : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
  burnolCompletedMellinEvaluator (coordinate i)

theorem price_is_original_K (i : Nat) (v : BurnolPaAmbientCarrier) :
    price i v = inner ℂ (burnolCompletedMellinRieszVector (coordinate i) : BurnolL2) (v : BurnolL2) :=
  (burnolCompletedMellinRieszVector_readback (coordinate i) v).symm

theorem real_part (i : Nat) : (coordinate i).value.re = 3/4 := probe_real _

theorem tail_separates (v : BurnolPaAmbientCarrier) (cutoff : Nat)
    (quiet : ∀ t : Nat, price (cutoff+t) v = 0) : v = 0 := by
  have rational (q : ℚ) : burnolCompletedMellinEvaluator (probe (q : ℝ)) v = 0 := by
    let address := Nat.pair ((Denumerable.eqv ℚ) q) cutoff
    have after : cutoff ≤ address := Nat.right_le_pair _ _
    have clock : cutoff + (address-cutoff) = address := by omega
    have readHeight : height address = (q : ℝ) := by
      simp only [height, address, Nat.unpair_pair, Equiv.symm_apply_apply]
    have value := quiet (address-cutoff)
    rw [clock] at value
    change burnolCompletedMellinEvaluator (probe (height address)) v = 0 at value
    rw [readHeight] at value
    exact value
  have everywhere : (fun y : ℝ => burnolCompletedMellinEvaluator (probe y) v) = fun _ => 0 := by
    apply Continuous.ext_on Rat.denseRange_cast (continuous_probe_price v) continuous_const
    rintro _ ⟨q,rfl⟩
    exact rational q
  apply Subtype.ext
  apply original_K_separates v
  intro test
  have observed := congrFun everywhere (test.1.value.im / (2*Real.pi))
  rw [probe_of_coordinate test.1 test.2] at observed
  exact (burnolCompletedMellinRieszVector_readback test.1 v).trans observed

/-- Original K prices on any rational tail separate every independent original Pa family. -/
theorem independent_tail (columns : Nat → BurnolPaAmbientCarrier)
    (independent : LinearIndependent ℂ columns) (cutoff : Nat) :
    LinearIndependent ℂ (fun j : Nat => fun t : Nat => price (cutoff+t) (columns j)) := by
  classical
  rw [linearIndependent_iff']
  intro indices coefficients silent j member
  let field := ∑ i ∈ indices, coefficients i • columns i
  have zero : field = 0 := by
    apply tail_separates field cutoff
    intro t
    have read := congrFun silent t
    simpa only [field, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using read
  exact (linearIndependent_iff'.mp independent) indices coefficients zero j member

end OriginalKFiniteOrderRelease.PositionGapCayley.PhysicalPriceGrid
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
