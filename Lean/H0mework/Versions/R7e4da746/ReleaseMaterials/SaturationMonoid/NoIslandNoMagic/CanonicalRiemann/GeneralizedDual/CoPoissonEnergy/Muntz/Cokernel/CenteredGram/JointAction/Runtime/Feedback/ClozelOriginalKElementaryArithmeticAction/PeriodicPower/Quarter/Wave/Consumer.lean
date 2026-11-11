import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Action

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open Complex Filter MeasureTheory Set BurnolPhysicalState FourierTransform
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Endpoint.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Action
open scoped Topology InnerProductSpace FourierTransform
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "F" => fourierL2
local notation "Rq" => burnolQuarterRestriction
local notation "P0" => Constructor.zeroMean
local notation "BI" => burnolMeanZeroBlockInverse
local notation "C" => ConstantDual.seed
local notation "FT" => (fourierCLM ℂ (TemperedDistribution ℝ ℂ))

def resolventForcing (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (1/2:ℂ) • F (companion c)

/-- The same compact wave has its actual Fourier generator, with the opposite clock. -/
theorem actual_fourier_euler (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    GapEuler.euler (F (quarterWave c):TemperedDistribution ℝ ℂ)=
      ((-F (velocity c):BurnolL2):TemperedDistribution ℝ ℂ) := by
  have field : FT (quarterWave c:TemperedDistribution ℝ ℂ)=
      (F (quarterWave c):TemperedDistribution ℝ ℂ):=Lp.fourier_toTemperedDistribution_eq _
  have read : FT (velocity c:TemperedDistribution ℝ ℂ)=
      (F (velocity c):TemperedDistribution ℝ ℂ):=Lp.fourier_toTemperedDistribution_eq _
  have anti : GapEuler.euler (FT (quarterWave c:TemperedDistribution ℝ ℂ))=
      -FT (GapEuler.euler (quarterWave c:TemperedDistribution ℝ ℂ)):=GapEuler.euler_fourier _
  rw [←field,anti,actual_quarter_euler c zero,read]
  exact ((Lp.toTemperedDistributionCLM ℂ volume 2).map_neg _).symm

/-- The original R engine consumes the generated strong source; no domain or realization is supplied. -/
theorem actual_fourier_resolvent (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    F (quarterWave c)=burnolDirectRightResolvent (star c.value/2) (resolventForcing c) := by
  have right : 1/4<(star c.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [c.rightHalf]
  apply burnolDirectRightResolvent_of_strongEquation _ right
  have derivative := DilationWard.strong_derivative _ _ (actual_fourier_euler c zero)
  have reparam : HasDerivAt (fun t:ℝ=>-t/2) (-1/2:ℝ) 0 := by
    simpa only [Pi.neg_apply,neg_div,id_eq] using (hasDerivAt_id (0:ℝ)).neg.div_const 2
  have generated := derivative.scomp_of_eq (0:ℝ) reparam (by norm_num)
  convert! generated using 1
  rw [←algebraMap_smul ℂ (-1/2:ℝ)]
  push_cast
  unfold velocity resolventForcing
  simp only [map_add,map_smul]
  module

def waveDifference (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  burnolMultiplicativeDilation h (quarterWave c)-
    Complex.exp ((star c.value-1/2)*(h:ℂ)) • quarterWave c

/-- The requested two-clock wave is the full signed source boundary of that same R occurrence. -/
theorem actual_wave_source_boundary (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value=0) (h : ℝ) :
    F (waveDifference c h)=Complex.exp ((star c.value-1/2)*(h:ℂ)) •
      burnolDirectRightResolventSignedBoundary (star c.value/2) (resolventForcing c) (2*h) := by
  have right : 1/4<(star c.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [c.rightHalf]
  have source:=burnolDirectRightResolvent_sourceBoundary (star c.value/2) right (resolventForcing c) (2*h)
  have clock:positiveMellinQuarterRightResolventCharacter (star c.value/2) (2*h)=
      Complex.exp ((star c.value-1/2)*(h:ℂ)) := by
    rw [positiveMellinQuarterRightResolventCharacter_exp]
    congr 1
    push_cast
    ring
  rw [←actual_fourier_resolvent c zero,clock,show -(2*h)/2= -h by ring] at source
  rw [waveDifference,map_sub,map_smul,fourierL2_burnolMultiplicativeDilation]
  exact source

def quarterMean (c : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolQuarterMeanCoefficient (periodicQuarter c)
def centeredWave (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  E (P0 (periodicQuarter c):Hq)

theorem actual_centered_wave (c : BurnolCompletedMellinCoordinate) :
    centeredWave c=quarterWave c-quarterMean c • C := by
  rw [centeredWave,Constructor.zeroMean_read,map_sub,map_smul]
  rfl

private theorem constant_euler :
    GapEuler.euler (C:TemperedDistribution ℝ ℂ)=
      -GapEuler.edge q-(1/2:ℂ) • (C:TemperedDistribution ℝ ℂ) := by
  ext test
  have source:=ConstantDual.seed_edge test
  rw [ConstantDual.edgeRead_apply] at source
  simp only [sub_apply,neg_apply,smul_apply,smul_eq_mul]
  linear_combination -source

/-- Centering restores the actual mean edge; the zero endpoint is not assigned to P0 H. -/
theorem actual_centered_euler (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    GapEuler.euler (centeredWave c:TemperedDistribution ℝ ℂ)=
      (star c.value-1/2) • (centeredWave c:TemperedDistribution ℝ ℂ)+
      (companion c:TemperedDistribution ℝ ℂ)+
      (star c.value*quarterMean c) • (C:TemperedDistribution ℝ ℂ)+
      quarterMean c • GapEuler.edge q := by
  have centered : (centeredWave c:TemperedDistribution ℝ ℂ)=
      (quarterWave c:TemperedDistribution ℝ ℂ)-quarterMean c • (C:TemperedDistribution ℝ ℂ) := by
    change Lp.toTemperedDistributionCLM ℂ volume 2 (centeredWave c)=_
    rw [actual_centered_wave,map_sub,map_smul]
    rfl
  simp only [centered,map_sub,map_smul]
  rw [actual_quarter_euler c zero,constant_euler]
  change Lp.toTemperedDistributionCLM ℂ volume 2
    ((star c.value-1/2) • quarterWave c+companion c)-_=_
  simp only [map_add,map_smul,Lp.toTemperedDistributionCLM_apply]
  module

/-- The original B inverse receives the generated R field and all aliases and Unit terms. -/
theorem actual_original_inverse_source (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    burnolRieszSingleFourierSource c=BI (P0
      (Rq (fourierL2.symm (burnolDirectRightResolvent (star c.value/2) (resolventForcing c)))-
        aliasQuarter c+jumpCoefficient c • Rq (F C))) := by
  rw [←actual_fourier_resolvent c zero,fourierL2.symm_apply_apply,quarterWave,burnolQuarterRestriction_zeroExtension]
  exact actual_original_B_periodic_source c

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
