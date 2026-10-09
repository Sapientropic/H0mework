import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationAbelZeroRead
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceHamiltonianSpectralMeasure

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalAbelZeroRead
open GaussCoreHilbert GaussUnitaryHistory SourceJointResidualEnergy
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalHalfAxis
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumGaugeSourceInjection
open PreparationVacuumMixedFieldReturn
open MeasureTheory Filter Set
open scoped Topology BigOperators InnerProductSpace

/-- Positive mass belongs to the original unit source state, with its actual escape channel. -/
theorem sourcePrepared_channel_mass (q : PhysicalResponsePoint) (state : RestStateIndex) :
    ∑ i : Channel q.F,‖channel q.F i (sourcePolePrepared q.epsilon q.precision 0 state)‖^2=1 := by
  rw [SourceHamiltonianSpectralMeasure.actual_channel_mass,sourcePolePrepared_unit,pow_two,one_mul]

private theorem abel_factor_bound (eta d : ℝ) (positive : 0<eta) (different : d≠0) :
    ‖(eta : ℂ)*((eta : ℂ)-Complex.I*(d : ℂ))⁻¹‖≤eta/|d| := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive,←div_eq_mul_inv]
  have denominator : |d|≤‖(eta : ℂ)-Complex.I*(d : ℂ)‖ := by
    simpa only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,zero_mul,one_mul,zero_add,zero_sub,abs_neg] using
      Complex.abs_im_le_norm ((eta : ℂ)-Complex.I*(d : ℂ))
  exact div_le_div_of_nonneg_left positive.le (abs_pos.mpr different) denominator

def sourceStaticErrorPrice (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) : ℝ :=
  ∑ i : Channel q.F,∑ j : Channel q.F,
    if channelValue q.F i=channelValue q.F j then 0 else
      ‖sourceStaticCoefficient q left right mu a i j‖/|sourceStaticGap q.F i j|

theorem sourceStaticErrorPrice_nonnegative (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) : 0 ≤ sourceStaticErrorPrice q left right mu a := by
  unfold sourceStaticErrorPrice
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

theorem sourceStaticAbel_controlled (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) (eta : ℝ) (positive : 0<eta) :
    ‖(eta : ℂ)*sourceStaticAbel q left right mu a (eta : ℂ)-sourceStaticResidue q left right mu a‖≤
      eta*sourceStaticErrorPrice q left right mu a := by
  classical
  unfold sourceStaticAbel sourceStaticResidue sourceStaticErrorPrice
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases same : channelValue q.F i=channelValue q.F j
  · simp only [if_pos same]
    have gapZero : sourceStaticGap q.F i j=0:=sub_eq_zero.mpr same
    simp only [sourceStaticDenominator,gapZero,Complex.ofReal_zero,
      mul_zero,sub_zero,←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne'),one_mul,sub_self,norm_zero,le_refl]
  · simp only [if_neg same,sub_zero]
    rw [sourceStaticDenominator,←mul_assoc,norm_mul]
    have gap : sourceStaticGap q.F i j≠0:=sub_ne_zero.mpr same
    exact (mul_le_mul_of_nonneg_right (abel_factor_bound eta (sourceStaticGap q.F i j) positive gap)
      (norm_nonneg _)).trans_eq (by ring)

theorem sourceActualStaticHalf_controlled (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) (eta : ℝ) (positive : 0<eta)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖(eta : ℂ)*sourcePoleCurrentHalf q 0 0 left right (eta : ℂ) (gaugeSlot mu a)-sourceStaticResidue q left right mu a‖≤
      eta*sourceStaticErrorPrice q left right mu a := by
  rw [sourceStaticHalf_generated q left right mu a (eta : ℂ)
    (by simpa only [Complex.ofReal_re] using positive) nonrealL nonrealR]
  exact sourceStaticAbel_controlled q left right mu a eta positive

end LowEnergy.PreparationVacuumPhysicalAbelZeroRead
