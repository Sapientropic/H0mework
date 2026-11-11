import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaNativePortMoments
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.VolterraMoments
open Complex Filter MeasureTheory Set OriginalPaPhysicalGreen
open CenteredGram.IntegralGraphJointAction
open scoped InnerProductSpace Topology BigOperators
local notation "q" => (1/4:ℝ)
namespace Port
export OriginalKCrossParameterRAdjointSource.PaNativePortSource (Pa sourceMap correction loop port)
export OriginalKCrossParameterRAdjointSource.PaNativePortMoments (actual_port_log_moment)
end Port
namespace Unit
export OriginalKFiniteOrderRelease.UnitPowerSource
  (actual_Pa_power_split unitPower_fourier_top unitPower)
end Unit
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
open private allPa_fourier_power_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
open private step_source_recovery from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.Source

/-- The original Pa source, with its paid qualification, is not an approximate finite value. -/
def originalPa : ↥Port.Pa := ⟨burnolPaCombApproximation 0,burnolPaCombApproximation_mem 0⟩

/-- The full all-order producer is reused; this is its second actual coefficient. -/
theorem second_coefficient (c : BurnolCompletedMellinCoordinate) (p : ↥Port.Pa) :
    Port.port c 2 p=4*(∫x:ℝ in Icc q 4,
      (x:ℂ)^(-c.value)*(Real.log (x/q):ℂ)^2*Port.sourceMap p x) := by
  have actual := Port.actual_port_log_moment c 2 p
  norm_num at actual
  exact actual

/-- Fourier/Tate extraction reads the original comb's unchanged reciprocal source. -/
theorem original_source : Port.sourceMap originalPa=
    (2:ℂ) • burnolReciprocalStepSourceL2 1 (3/2) (by norm_num) (by norm_num) := by
  let step := burnolReciprocalStepPhysicalState 1 (3/2) (by norm_num) (by norm_num) (by norm_num)
  have member : step∈burnolCompactCoPoissonClosedRange :=
    burnolReciprocalStepWave_memPa 1 (3/2) (by norm_num) (by norm_num) (by norm_num)
  have original : (originalPa:BurnolPaAmbientCarrier)=
      (2:ℂ) • evenFaceFourierEquiv burnolUnscaledCommonGapRadius step := by
    norm_num [originalPa,burnolPaCombApproximation,burnolPaCombSourceWidth,step]
  change burnolTateReciprocalL2 (burnolMobiusSourceL2 (originalPa:BurnolPaAmbientCarrier))=_
  rw [original,map_smul,map_smul,burnolMobiusSource_fourier step member,
    burnolTateReciprocalL2_involutive]
  exact congrArg (fun v:BurnolL2 => (2:ℂ) • v)
    (step_source_recovery 1 (3/2) (by norm_num) (by norm_num) (by norm_num))

theorem original_source_read : (Port.sourceMap originalPa:ℝ→ℂ)=ᵐ[volume]
    fun x => 2*burnolReciprocalStepSourceRaw 1 (3/2) x := by
  rw [original_source]
  filter_upwards [Lp.coeFn_smul (2:ℂ)
      (burnolReciprocalStepSourceL2 1 (3/2) (by norm_num) (by norm_num)),
    (burnolReciprocalStepSource_memLp 1 (3/2) (by norm_num) (by norm_num)).coeFn_toLp]
      with x scaled raw
  rw [scaled,Pi.smul_apply,smul_eq_mul]
  exact congrArg (fun v:ℂ => 2*v) raw

theorem original_second_coefficient (c : BurnolCompletedMellinCoordinate) :
    Port.port c 2 originalPa=8*(∫x:ℝ in (2/3:ℝ)..1,
      (x:ℂ)^(-c.value-1)*(Real.log (4*x):ℂ)^2) := by
  rw [second_coefficient]
  have profile : (fun x:ℝ => (x:ℂ)^(-c.value)*(Real.log (x/q):ℂ)^2*Port.sourceMap originalPa x)
      =ᵐ[volume.restrict (Icc q 4)]
        (Ioc (2/3:ℝ) 1).indicator (fun x:ℝ => 2*((x:ℂ)^(-c.value-1)*(Real.log (4*x):ℂ)^2)) := by
    filter_upwards [ae_restrict_of_ae original_source_read,ae_restrict_mem measurableSet_Icc] with x raw inside
    have positive : 0<x := lt_of_lt_of_le (by norm_num) inside.1
    have incidence : (1≤x⁻¹ ∧ x⁻¹<(3/2:ℝ)) ↔ (2/3:ℝ)<x ∧ x≤1 := by
      have product : x⁻¹*x=1 := inv_mul_cancel₀ positive.ne'
      constructor
      · intro h
        have low := mul_le_mul_of_nonneg_right h.1 positive.le
        have high := mul_lt_mul_of_pos_right h.2 positive
        exact ⟨by nlinarith,by nlinarith⟩
      · intro h
        have a : 1*x≤x⁻¹*x := by nlinarith
        have b : x⁻¹*x<(3/2:ℝ)*x := by nlinarith
        exact ⟨le_of_mul_le_mul_right a positive,lt_of_mul_lt_mul_right b positive.le⟩
    rw [raw]
    unfold burnolReciprocalStepSourceRaw
    rw [abs_of_pos positive]
    by_cases member:x∈Ioc (2/3:ℝ) 1
    · rw [if_pos (incidence.mpr member),indicator_of_mem member]
      have power : (x:ℂ)^(-c.value)*(x:ℂ)⁻¹=(x:ℂ)^(-c.value-1) := by
        rw [←Complex.cpow_neg_one,←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
        simp only [sub_eq_add_neg]
      have logarithm : x/q=4*x := by ring
      rw [logarithm]
      calc
        _ = 2*((x:ℂ)^(-c.value)*(x:ℂ)⁻¹)*(Real.log (4*x):ℂ)^2 := by ring
        _ = _ := by rw [power];ring
    · rw [if_neg (fun h => member (incidence.mp h)),indicator_of_notMem member,mul_zero,mul_zero]
  rw [integral_congr_ae profile,setIntegral_indicator measurableSet_Ioc]
  have region : Icc q 4 ∩ Ioc (2/3:ℝ) 1=Ioc (2/3:ℝ) 1 := by
    apply inter_eq_right.mpr
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  rw [region,←intervalIntegral.integral_of_le (by norm_num : (2/3:ℝ)≤1),intervalIntegral.integral_const_mul]
  ring

section Original
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "Rpow" => CombSource.Division.rawIterate observation half.down
local notation "FK" => fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2)
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation

/-- Three paid source splits expose the second coefficient in the same original raw0 price. -/
theorem actual_raw_fourier_second_moment (depth : ℕ) :
    inner ℂ FK (OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth 0)=
      Port.port c 0 originalPa*inner ℂ FK (Unit.unitPower observation half (m+1))+
      Port.port c 1 originalPa*inner ℂ FK (Unit.unitPower observation half m)+
      (8*(∫x:ℝ in (2/3:ℝ)..1,
        (x:ℂ)^(-(c).value-1)*(Real.log (4*x):ℂ)^2))*e := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  have first := Unit.actual_Pa_power_split observation half
    (originalPa:BurnolPaAmbientCarrier) originalPa.property (m+1)
  have second := Unit.actual_Pa_power_split observation half
    (Port.loop c 1 originalPa:BurnolPaAmbientCarrier) (Port.loop c 1 originalPa).property m
  have third := Unit.actual_Pa_power_split observation half
    (Port.loop c 2 originalPa:BurnolPaAmbientCarrier) (Port.loop c 2 originalPa).property (m-1)
  have index : m-1+1=m := by omega
  rw [index] at third
  have raw : OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth 0=
      Rpow (m+2) (originalPa:BurnolL2) := by
    rw [OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial.actual_raw_field,
      OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial.actual_iterate_power]
    rfl
  have low := allPa_fourier_power_zero observation nontrivial half
    (Port.loop c 3 originalPa:BurnolPaAmbientCarrier) (Port.loop c 3 originalPa).property (m-1) (by omega)
  have top := Unit.unitPower_fourier_top observation nontrivial half
  change Rpow (m+2) (originalPa:BurnolL2)=
    Rpow (m+1) (Port.loop c 1 originalPa:BurnolL2)+_ at first
  change Rpow (m+1) (Port.loop c 1 originalPa:BurnolL2)=
    Rpow m (Port.loop c 2 originalPa:BurnolL2)+_ at second
  change Rpow m (Port.loop c 2 originalPa:BurnolL2)=
    Rpow (m-1) (Port.loop c 3 originalPa:BurnolL2)+_ at third
  rw [raw,first,second,third]
  simp only [inner_add_right,inner_smul_right,low,zero_add,top]
  change _=Port.port c 0 originalPa*_+Port.port c 1 originalPa*_+_
  rw [←original_second_coefficient]
  unfold Port.port
  rw [show Port.loop c 0 originalPa=originalPa from rfl]
  ring
end Original
end CountedPaInitial.VolterraMoments
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
