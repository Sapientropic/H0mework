import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.NativePriceFlow
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierPhysicalTransfer
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalKPairedBEulerJunctionSource OriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice
open scoped InnerProductSpace Topology
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "P" => positionSource
local notation "b" => burnolRieszSingleFourierSourceRaw

open private position_hasDerivAt from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice

def physicalClock (time:ℝ) : ℝ := q*Real.exp time
def sourceProgramme (rate:ℂ) (side:Fin 2) (time:ℝ) : ℂ :=
  ∫ t:ℝ in 0..time,Complex.exp (rate*(t:ℂ))*sourceColumn side (physicalClock t)

/-- Every entry is generated from the original fixed response columns, including the unit. -/
def sourceTransfer (c:BurnolCompletedMellinCoordinate) (time:ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![Complex.exp (-(star c.value*(time:ℂ)))*(-1+sourceProgramme (star c.value) 0 time),
      Complex.exp (-(star c.value*(time:ℂ)))*sourceProgramme (star c.value) 1 time],
    ![-Complex.exp (-((1-star c.value)*(time:ℂ)))*sourceProgramme (1-star c.value) 1 time,
      Complex.exp (-((1-star c.value)*(time:ℂ)))*(1-sourceProgramme (1-star c.value) 0 time)]]

private theorem clock_positive (time:ℝ) : 0<physicalClock time := by
  unfold physicalClock
  positivity

private theorem clock_velocity (time:ℝ) : HasDerivAt physicalClock (physicalClock time) time := by
  convert! ((hasDerivAt_id time).exp.const_mul q) using 1
  first | rfl | norm_num [physicalClock]

private theorem programme_integrable (rate:ℂ) (side:Fin 2) (time:ℝ) :
    IntervalIntegrable (fun t:ℝ=>Complex.exp (rate*(t:ℂ))*sourceColumn side (physicalClock t)) volume 0 time := by
  have actual : Continuous (fun t:ℝ=>sourceColumn side (physicalClock t)) :=
    (source_column_continuous side).comp (by unfold physicalClock;fun_prop)
  exact (by fun_prop : Continuous (fun t:ℝ=>Complex.exp (rate*(t:ℂ))*sourceColumn side (physicalClock t))).intervalIntegrable 0 time

private theorem weighted_position_velocity (c:BurnolCompletedMellinCoordinate) (time:ℝ) :
    HasDerivAt (fun t:ℝ=>Complex.exp (star c.value*(t:ℂ))*P c (physicalClock t))
      (Complex.exp (star c.value*(time:ℂ))*
        (Kernel.A c*sourceColumn 0 (physicalClock time)+Kernel.beta c*sourceColumn 1 (physicalClock time))) time := by
  have ep := (((Complex.ofRealCLM.hasDerivAt (x:=time)).const_mul (star c.value)).cexp)
  have cp : HasDerivAt (fun t:ℝ=>P c (physicalClock t))
      ((physicalClock time:ℂ)*positionExteriorDerivative c (physicalClock time)) time := by
    simpa only [Function.comp_def,Complex.real_smul] using!
      (position_hasDerivAt c _ (clock_positive time)).scomp time (clock_velocity time)
  have actual := ep.mul cp
  convert! actual using 1
  simp only [Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one]
  have source := position_source_euler c (physicalClock time) (clock_positive time)
  linear_combination -(Complex.exp (star c.value*(time:ℂ)))*source

private theorem weighted_fourier_velocity (c:BurnolCompletedMellinCoordinate) (time:ℝ) :
    HasDerivAt (fun t:ℝ=>Complex.exp ((1-star c.value)*(t:ℂ))*b c (physicalClock t))
      (Complex.exp ((1-star c.value)*(time:ℂ))*
        (-Kernel.A c*sourceColumn 1 (physicalClock time)-Kernel.beta c*sourceColumn 0 (physicalClock time))) time := by
  have ep := (((Complex.ofRealCLM.hasDerivAt (x:=time)).const_mul (1-star c.value)).cexp)
  have cp : HasDerivAt (fun t:ℝ=>b c (physicalClock t))
      ((physicalClock time:ℂ)*sourceRawDerivative c (physicalClock time)) time := by
    simpa only [Function.comp_def,Complex.real_smul] using!
      (sourceRaw_hasDerivAt c _ (clock_positive time).ne').scomp time (clock_velocity time)
  have actual := ep.mul cp
  convert! actual using 1
  simp only [Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one]
  have source := fourier_source_euler c (physicalClock time) (clock_positive time).ne'
  linear_combination -(Complex.exp ((1-star c.value)*(time:ℂ)))*source

private theorem position_integral (c:BurnolCompletedMellinCoordinate) (time:ℝ) :
    (∫ t:ℝ in 0..time,Complex.exp (star c.value*(t:ℂ))*
      (Kernel.A c*sourceColumn 0 (physicalClock t)+Kernel.beta c*sourceColumn 1 (physicalClock t)))=
      Kernel.A c*sourceProgramme (star c.value) 0 time+
        Kernel.beta c*sourceProgramme (star c.value) 1 time := by
  calc
    _=∫ t:ℝ in 0..time,Kernel.A c*(Complex.exp (star c.value*(t:ℂ))*sourceColumn 0 (physicalClock t))+
      Kernel.beta c*(Complex.exp (star c.value*(t:ℂ))*sourceColumn 1 (physicalClock t)) := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _=_ := by
      rw [intervalIntegral.integral_add ((programme_integrable _ 0 time).const_mul (Kernel.A c))
        ((programme_integrable _ 1 time).const_mul (Kernel.beta c)),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
      rfl

private theorem fourier_integral (c:BurnolCompletedMellinCoordinate) (time:ℝ) :
    (∫ t:ℝ in 0..time,Complex.exp ((1-star c.value)*(t:ℂ))*
      (-Kernel.A c*sourceColumn 1 (physicalClock t)-Kernel.beta c*sourceColumn 0 (physicalClock t)))=
      -Kernel.A c*sourceProgramme (1-star c.value) 1 time-
        Kernel.beta c*sourceProgramme (1-star c.value) 0 time := by
  calc
    _=∫ t:ℝ in 0..time,(-Kernel.A c)*(Complex.exp ((1-star c.value)*(t:ℂ))*sourceColumn 1 (physicalClock t))-
      Kernel.beta c*(Complex.exp ((1-star c.value)*(t:ℂ))*sourceColumn 0 (physicalClock t)) := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _=_ := by
      rw [intervalIntegral.integral_sub ((programme_integrable _ 1 time).const_mul (-Kernel.A c))
        ((programme_integrable _ 0 time).const_mul (Kernel.beta c)),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
      rfl

/-- Initial values are the actual original right-hand jump charges; no endpoint witness is input. -/
theorem actual_physical_transfer (c:BurnolCompletedMellinCoordinate) (time:ℝ) :
    P c (physicalClock time)=sourceTransfer c time 0 0*Kernel.A c+sourceTransfer c time 0 1*Kernel.beta c ∧
    b c (physicalClock time)=sourceTransfer c time 1 0*Kernel.A c+sourceTransfer c time 1 1*Kernel.beta c := by
  have firstContinuous : Continuous (fun t:ℝ=>Complex.exp (star c.value*(t:ℂ))*
      (Kernel.A c*sourceColumn 0 (physicalClock t)+Kernel.beta c*sourceColumn 1 (physicalClock t))) := by
    have p0 := (source_column_continuous 0).comp (by unfold physicalClock;fun_prop : Continuous physicalClock)
    have p1 := (source_column_continuous 1).comp (by unfold physicalClock;fun_prop : Continuous physicalClock)
    fun_prop
  have secondContinuous : Continuous (fun t:ℝ=>Complex.exp ((1-star c.value)*(t:ℂ))*
      (-Kernel.A c*sourceColumn 1 (physicalClock t)-Kernel.beta c*sourceColumn 0 (physicalClock t))) := by
    have p0 := (source_column_continuous 0).comp (by unfold physicalClock;fun_prop : Continuous physicalClock)
    have p1 := (source_column_continuous 1).comp (by unfold physicalClock;fun_prop : Continuous physicalClock)
    fun_prop
  have first := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _=>weighted_position_velocity c t) (firstContinuous.intervalIntegrable 0 time)
  have second := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _=>weighted_fourier_velocity c t) (secondContinuous.intervalIntegrable 0 time)
  rw [position_integral] at first
  rw [fourier_integral] at second
  simp only [physicalClock,Real.exp_zero,mul_one,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul,
    position_source_trace,sub_neg_eq_add] at first second
  change _=Complex.exp ((1-star c.value)*(time:ℂ))*b c (q*Real.exp time)-Kernel.beta c at second
  have clockNormal : q*Real.exp time=Real.exp time/4 := by ring
  rw [clockNormal] at first second
  constructor
  · simp only [sourceTransfer,Matrix.cons_val_zero,Matrix.cons_val_one,Complex.exp_neg]
    dsimp only [physicalClock]
    field_simp
    linear_combination -first
  · simp only [sourceTransfer,Matrix.cons_val_zero,Matrix.cons_val_one,Complex.exp_neg]
    dsimp only [physicalClock]
    field_simp
    linear_combination -second

theorem actual_source_transfer_initial (c:BurnolCompletedMellinCoordinate) :
    sourceTransfer c 0= ![![-1,0],![0,1]] := by
  simp only [sourceTransfer,sourceProgramme,intervalIntegral.integral_same,Complex.ofReal_zero,mul_zero,
    neg_zero,Complex.exp_zero,one_mul,add_zero,sub_zero,mul_zero]

end OriginalConstantFourierPhysicalTransfer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
