import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.FiniteB
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.PowerSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.Sawtooth
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalUnitMellinSource.Fourier
open scoped InnerProductSpace Topology
open private actual_TF_R from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.PowerSource
open private power_dilation from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.FixedShell
local notation "q" => (1/4 : ℝ)
local notation "D" => burnolMultiplicativeDilation
local notation "R" => burnolDirectRightResolventCLM
local notation "T" => burnolTateReciprocalL2
local notation "F" => fourierL2
local notation "H" => ConstantDual.value

/-- Both source scales stay explicit until the whole-field identity has been generated. -/
def bridgeFactor (c : BurnolCompletedMellinCoordinate) : ℂ :=
  (fullMellinTranslationCharacter c.value (-Real.log 16))⁻¹*(q : ℂ)^(-c.value)

/-- This word acts on the entire sawtooth, including the same-N continuous normalization. -/
def sawtoothUnitWord (c : BurnolCompletedMellinCoordinate) (j : ℕ) (value : BurnolL2) : BurnolL2 :=
  bridgeFactor c • D (-Real.log 16)
    ((((R c)^j) value)+(c.value/2) • (((R c)^(j+1)) value))

private theorem tf_dilation (h : ℝ) (value : BurnolL2) :
    T (F (D h value)) = D h (T (F value)) := by
  rw [fourierL2_burnolMultiplicativeDilation,←burnolTateReciprocalL2_dilation_inverse]

private theorem tf_power (c : BurnolCompletedMellinCoordinate) (j : ℕ) (value : BurnolL2) :
    T (F (((R c)^j) value)) = ((R c)^j) (T (F value)) := by
  induction j with
  | zero => rfl
  | succ j previous =>
    rw [pow_succ',mul_apply_eq_comp,actual_TF_R,previous]
    rfl

/-- The radius-four Unit is identified as the actual full resolvent source of the original sawtooth. -/
theorem actual_unit_four_sawtooth_field (c : BurnolCompletedMellinCoordinate) :
    T (F (burnolUnitTailResponse c 4)) =
      bridgeFactor c • D (-Real.log 16) (H+(c.value/2) • R c H) := by
  have quarter := congrArg T (actual_unit_quarter_fourier c)
  rw [map_smul,burnolTateReciprocalL2_involutive] at quarter
  have radius : q*Real.exp (-(-Real.log 16)) = 4 := by
    rw [neg_neg,Real.exp_log (by norm_num : (0 : ℝ)<16)]
    norm_num
  have moved := congrArg (fun value : BurnolL2 => T (F value))
    (burnolUnitTailResponse_radius_dilation c q (by norm_num) (by norm_num)
      (-Real.log 16) (by rw [radius]; norm_num))
  rw [radius,tf_dilation,quarter,map_smul,map_smul,map_smul] at moved
  change (q : ℂ)^(-c.value) • D (-Real.log 16) (H+(c.value/2) • R c H) =
    fullMellinTranslationCharacter c.value (-Real.log 16) • T (F (burnolUnitTailResponse c 4)) at moved
  have nonzero : fullMellinTranslationCharacter c.value (-Real.log 16) ≠ 0 := Complex.exp_ne_zero _
  calc
    _ = (fullMellinTranslationCharacter c.value (-Real.log 16))⁻¹ •
        (fullMellinTranslationCharacter c.value (-Real.log 16) • T (F (burnolUnitTailResponse c 4))) :=
      (inv_smul_smul₀ nonzero _).symm
    _ = _ := by rw [←moved,smul_smul]; rfl

/-- The higher sawtooth column j+1 is retained by the actual original j-th R action. -/
theorem actual_unit_power_sawtooth_field (c : BurnolCompletedMellinCoordinate) (j : ℕ) :
    T (F (((R c)^j) (burnolUnitTailResponse c 4))) = sawtoothUnitWord c j H := by
  rw [tf_power,actual_unit_four_sawtooth_field,map_smul,power_dilation,map_add,map_smul]
  unfold sawtoothUnitWord
  rw [pow_succ,mul_apply_eq_comp]

/-- Both radius factors combine without any branch choice at nonpositive bases. -/
theorem actual_bridge_factor (c : BurnolCompletedMellinCoordinate) :
    bridgeFactor c = (4 : ℂ)^(1-c.value) := by
  have logq : Complex.log (q : ℂ) = -(Real.log 4 : ℂ) := by
    rw [←Complex.ofReal_log (by norm_num : (0 : ℝ)≤q),
      show q=(4 : ℝ)⁻¹ by norm_num,Real.log_inv,Complex.ofReal_neg]
  have log4 : Complex.log (4 : ℂ) = (Real.log 4 : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ)≤4)).symm
  have log16 : Real.log 16 = 2*Real.log 4 := by
    rw [show (16 : ℝ)=4*4 by norm_num,Real.log_mul (by norm_num : (4 : ℝ)≠0) (by norm_num : (4 : ℝ)≠0)]
    ring
  unfold bridgeFactor fullMellinTranslationCharacter
  rw [←Complex.exp_neg,Complex.cpow_def_of_ne_zero (by norm_num : (q : ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (4 : ℂ)≠0),logq,log4,←Complex.exp_add,log16]
  congr 1
  push_cast
  ring

/-- The same original integer-minus-full-continuous sequence generates this entire Unit word strongly. -/
theorem actual_same_N_sawtooth_unit_tendsto (c : BurnolCompletedMellinCoordinate) (j : ℕ) :
    Tendsto (fun N : ℕ => sawtoothUnitWord c j (DualSource.source N ConstantDual.seed)) atTop
      (𝓝 (T (F (((R c)^j) (burnolUnitTailResponse c 4))))) := by
  have continuous : Continuous (sawtoothUnitWord c j) := by
    unfold sawtoothUnitWord
    fun_prop
  have source := (continuous.tendsto H).comp ConstantDual.original_tendsto
  rw [←actual_unit_power_sawtooth_field] at source
  exact source

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.Sawtooth
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
