import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Completion
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source
open scoped Topology InnerProductSpace

def inverseClock (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  Complex.exp (-((star c.value-1/2)*(h:ℂ)))

private theorem inverse_clock_cancel (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inverseClock c h*Complex.exp ((star c.value-1/2)*(h:ℂ))=1 := by
  rw [inverseClock,←Complex.exp_add,neg_add_cancel,Complex.exp_zero]

theorem actual_clock_contraction (c : BurnolCompletedMellinCoordinate) (h : ℝ) (positive : 0<h) :
    ‖inverseClock c h‖<1 := by
  rw [inverseClock,Complex.norm_exp,Real.exp_lt_one_iff]
  simp only [neg_re,mul_re,sub_re,star_def,conj_re,div_ofNat_re,one_re,
    Complex.ofReal_re,sub_im,conj_im,div_ofNat_im,one_im,Complex.ofReal_im,mul_zero,sub_zero]
  exact neg_neg_of_pos (mul_pos (by linarith [c.rightHalf]) positive)

def sourcePiece (c : BurnolCompletedMellinCoordinate) (h : ℝ) (n : ℕ) : BurnolL2 :=
  -(inverseClock c h)^(n+1) • burnolMultiplicativeDilation ((n:ℝ)*h) (waveDifference c h)

theorem actual_source_piece_norm (c : BurnolCompletedMellinCoordinate) (h : ℝ) (n : ℕ) :
    ‖sourcePiece c h n‖=‖inverseClock c h‖^(n+1)*‖waveDifference c h‖ := by
  rw [sourcePiece,norm_smul,norm_neg,norm_pow,(burnolMultiplicativeDilation _).norm_map]

theorem actual_source_piece_summable (c : BurnolCompletedMellinCoordinate) (h : ℝ) (positive : 0<h) :
    Summable (fun n:ℕ=>‖sourcePiece c h n‖) := by
  simp_rw [actual_source_piece_norm,pow_succ,mul_assoc]
  have geometric : Summable (fun n:ℕ=>‖inverseClock c h‖^n) := by
    apply summable_geometric_of_norm_lt_one
    simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using (actual_clock_contraction c h positive)
  exact geometric.mul_right (‖inverseClock c h‖*‖waveDifference c h‖)

private theorem source_piece_difference (c : BurnolCompletedMellinCoordinate) (h : ℝ) (n : ℕ) :
    sourcePiece c h n=(inverseClock c h)^n • burnolMultiplicativeDilation ((n:ℝ)*h) (quarterWave c)-
      (inverseClock c h)^(n+1) • burnolMultiplicativeDilation (((n+1:ℕ):ℝ)*h) (quarterWave c) := by
  rw [sourcePiece,waveDifference,map_sub,map_smul,burnolMultiplicativeDilation_add]
  have parameter : (n:ℝ)*h+h=((n+1:ℕ):ℝ)*h := by push_cast;ring
  rw [parameter]
  have scalar : (inverseClock c h)^(n+1)*Complex.exp ((star c.value-1/2)*(h:ℂ))=
      (inverseClock c h)^n := by
    rw [pow_succ,mul_assoc,inverse_clock_cancel,mul_one]
  simp only [smul_sub,smul_smul,neg_mul,scalar,neg_smul]
  abel

theorem actual_finite_source_completion (c : BurnolCompletedMellinCoordinate) (h : ℝ) (N : ℕ) :
    ∑n∈Finset.range N,sourcePiece c h n=quarterWave c-
      (inverseClock c h)^N • burnolMultiplicativeDilation ((N:ℝ)*h) (quarterWave c) := by
  induction N with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,pow_zero,Nat.cast_zero,zero_mul,
      burnolMultiplicativeDilation_zero,one_smul,sub_self]
  | succ N hypothesis =>
      rw [Finset.sum_range_succ,hypothesis,source_piece_difference]
      abel

/-- The same H_h source reconstructs the full original H through a genuine L² strong sum. -/
theorem actual_source_completion (c : BurnolCompletedMellinCoordinate) (h : ℝ) (positive : 0<h) :
    HasSum (sourcePiece c h) (quarterWave c) := by
  apply (hasSum_iff_tendsto_nat_of_summable_norm (actual_source_piece_summable c h positive)).mpr
  simp_rw [actual_finite_source_completion]
  have tail:Tendsto (fun N:ℕ=>(inverseClock c h)^N •
      burnolMultiplicativeDilation ((N:ℝ)*h) (quarterWave c)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp only [norm_smul,norm_pow,(burnolMultiplicativeDilation _).norm_map]
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (actual_clock_contraction c h positive)).mul_const
        ‖quarterWave c‖
  simpa only [sub_zero] using tendsto_const_nhds.sub tail

/-- The original comb reader consumes this source completion on each original Schwartz measurement. -/
theorem actual_comb_completion (c : BurnolCompletedMellinCoordinate) (h : ℝ) (positive : 0<h)
    (test : SchwartzMap ℝ ℂ) :
    HasSum (fun n:ℕ=>-(inverseClock c h)^(n+1)*
      burnolRemainderSourceRead (waveDifference c h)
        (burnolRemainderSchwartzDilation (-((n:ℝ)*h)) test))
      (burnolRemainderSourceRead (quarterWave c) test) := by
  have generated:=(burnolRemainderSourceReadCLM test).hasSum (actual_source_completion c h positive)
  simpa only [sourcePiece,map_smul,burnolRemainderSourceReadCLM_apply,smul_eq_mul,
    burnolRemainderSourceRead_dilation] using generated

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Completion
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
