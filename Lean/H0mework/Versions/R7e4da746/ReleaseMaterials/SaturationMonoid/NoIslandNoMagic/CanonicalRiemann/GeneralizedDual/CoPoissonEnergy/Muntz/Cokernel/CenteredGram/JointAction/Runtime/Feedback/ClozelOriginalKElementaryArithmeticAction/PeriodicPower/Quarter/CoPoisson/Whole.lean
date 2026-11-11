import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Landing

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Completion
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Landing
open scoped Topology InnerProductSpace
open private valueRead valueRead_eq from
  H0mework.Versions.R7e4da746.Arithmetic.RiemannResolvent.CompleteRemainder

def valuePiece (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (n : ℕ) : BurnolL2 :=
  -(inverseClock c h)^(n+1) • burnolMultiplicativeDilation ((n:ℝ)*h)
    (fourierL2 (countedValue c zero h nonnegative))

theorem actual_value_piece_summable (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) : Summable (fun n:ℕ=>‖valuePiece c zero h positive.le n‖) := by
  simp only [valuePiece,norm_smul,norm_neg,norm_pow,(burnolMultiplicativeDilation _).norm_map]
  simp_rw [pow_succ,mul_assoc]
  have geometric : Summable (fun n:ℕ=>‖inverseClock c h‖^n) := by
    apply summable_geometric_of_norm_lt_one
    simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using (actual_clock_contraction c h positive)
  exact geometric.mul_right (‖inverseClock c h‖*‖fourierL2 (countedValue c zero h positive.le)‖)

def wholeValue (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) : BurnolL2 := ∑'n:ℕ,valuePiece c zero h positive.le n

theorem actual_value_completion (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) : HasSum (valuePiece c zero h positive.le) (wholeValue c zero h positive) :=
  (actual_value_piece_summable c zero h positive).of_norm.hasSum

private theorem piece_realizes (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) (n : ℕ) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (sourcePiece c h n) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (valuePiece c zero h positive.le n)) test := by
  unfold sourcePiece valuePiece
  rw [←burnolRemainderSourceReadCLM_apply,map_smul,burnolRemainderSourceReadCLM_apply,
    burnolRemainderRealization_dilation (waveDifference c h) (fourierL2 (countedValue c zero h positive.le))
      (actual_difference_realizes c zero h positive.le)]
  simp only [map_smul,smul_apply]

/-- Both sides are strong sums of the same source-generated programme. -/
theorem actual_whole_realizes (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (quarterWave c) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (wholeValue c zero h positive)) test := by
  have source:=(burnolRemainderSourceReadCLM test).hasSum (actual_source_completion c h positive)
  have value:=(valueRead test).hasSum (actual_value_completion c zero h positive)
  simp only [burnolRemainderSourceReadCLM_apply,piece_realizes c zero h positive] at source
  simp only [valueRead_eq] at value
  exact source.unique value

theorem actual_whole_tate_realizes (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolTateReciprocalL2 (quarterWave c)) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierL2 (wholeValue c zero h positive))) test :=
  burnolRemainderRealization_fourier (quarterWave c) (wholeValue c zero h positive)
    (actual_whole_realizes c zero h positive) test

theorem actual_whole_clock (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (positive : 0<h) :
    burnolMultiplicativeDilation h (wholeValue c zero h positive)-
      Complex.exp ((star c.value-1/2)*(h:ℂ)) • wholeValue c zero h positive=
        fourierL2 (countedValue c zero h positive.le) := by
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F:=ℂ) (μ:=volume))
  change (Lp.toTemperedDistributionCLM ℂ volume 2
    (burnolMultiplicativeDilation h (wholeValue c zero h positive)-
      Complex.exp ((star c.value-1/2)*(h:ℂ)) • wholeValue c zero h positive))=
    Lp.toTemperedDistributionCLM ℂ volume 2 (fourierL2 (countedValue c zero h positive.le))
  ext test
  have source:=actual_difference_realizes c zero h positive.le test
  rw [waveDifference,←burnolRemainderSourceReadCLM_apply,map_sub,map_smul,
    burnolRemainderSourceReadCLM_apply,burnolRemainderSourceReadCLM_apply,
    burnolRemainderRealization_dilation (quarterWave c) (wholeValue c zero h positive)
      (actual_whole_realizes c zero h positive),actual_whole_realizes c zero h positive] at source
  simpa only [map_sub,map_smul,sub_apply,smul_apply] using source

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
