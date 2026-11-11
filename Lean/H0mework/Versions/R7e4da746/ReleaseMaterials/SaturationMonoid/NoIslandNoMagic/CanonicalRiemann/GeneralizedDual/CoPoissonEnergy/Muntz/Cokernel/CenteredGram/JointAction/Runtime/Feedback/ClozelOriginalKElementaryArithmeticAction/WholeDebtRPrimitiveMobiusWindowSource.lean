import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPrimitiveMobiusSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRPrimitiveMobiusSource
open Complex MeasureTheory Set FourierTransform BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalWholeDebtRPowerWaveDilationSource OriginalKSourceResolventReconstruction
open scoped InnerProductSpace BigOperators FourierTransform
open private mean_of_gap from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPrimitiveMobiusSource
local notation "DT" => TemperedDistribution ℝ ℂ
local notation "FL" => fourierL2
local notation "Tate" => burnolTateReciprocalL2
local notation "q" => (1/4 : ℝ)
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "p" => Flux.primitiveSource observation nontrivial half
local notation "K" => OriginalKCombCofinalTwoDirection.originalK observation nontrivial half
local notation "aa" => Flux.sourceA observation

private theorem M_local (left right : BurnolL2)
    (read : (left : ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval 4)] right) :
    Flux.M left=Flux.M right := by
  have source:=(ae_restrict_iff' (measurableSet_symmetricInterval 4)).mp read
  have quarter : burnolQuarterRestriction left=burnolQuarterRestriction right := by
    apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) left,
      LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) right,
      ae_restrict_of_ae source,ae_restrict_mem (measurableSet_symmetricInterval q)]
      with x l r same inside
    change burnolQuarterRestriction left x=left x at l
    change burnolQuarterRestriction right x=right x at r
    rw [l,r]
    exact same ⟨by linarith [inside.1],by linarith [inside.2]⟩
  have mean : Flux.actualMean left=Flux.actualMean right := by
    change (‖intervalConstant q‖^2 : ℂ)⁻¹*inner ℂ (intervalConstant q) (burnolQuarterRestriction left)=_
    rw [quarter]
    rfl
  have each (n : ℕ+) : Flux.lowerPullback n left=Flux.lowerPullback n right := by
    have np : 0<((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => x/((n : ℕ) : ℝ)) volume volume := by
      simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using
        Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
          (r := (((n : ℕ) : ℝ))⁻¹) (inv_ne_zero np.ne')
    apply Lp.ext
    filter_upwards [FiniteMobiusResolventFlux.lower_pullback_read n left,
      FiniteMobiusResolventFlux.lower_pullback_read n right,
      ae_restrict_of_ae (qmp.ae source),ae_restrict_mem (measurableSet_symmetricInterval 4)]
      with x l r same inside
    rw [l,r,mean]
    congr 1
    apply same
    apply abs_le.mp
    rw [abs_div,abs_of_pos np,div_le_iff₀ np]
    have one : (1 : ℝ)≤((n : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr n.pos)
    have bound:=abs_le.mpr inside
    nlinarith
  unfold Flux.M Flux.lowerWindow
  simp only [ContinuousLinearMap.comp_apply,sum_apply,smul_apply,each]

private theorem M_cutoff (value : BurnolL2) : Flux.M (F.cutoff 4 value)=Flux.M value := by
  apply M_local
  filter_upwards [ae_restrict_of_ae (FiniteMobiusResolventFlux.cutoff_read 4 value),
    ae_restrict_mem (measurableSet_symmetricInterval 4)] with x read inside
  rw [read,indicator_of_mem inside]

theorem M_box_zero : Flux.M (F.box 4)=0 := by
  have quarter : burnolQuarterRestriction (F.box 4)=(1 : ℂ) • intervalConstant q := by
    apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (F.box 4),
      ae_restrict_of_ae (FiniteMobiusResolventFlux.box_read 4),
      Lp.coeFn_smul (1 : ℂ) (intervalConstant q),intervalConstant_coeFn q,
      ae_restrict_mem (measurableSet_symmetricInterval q)] with x restricted raw scalar unit inside
    rw [show burnolQuarterRestriction (F.box 4) x=F.box 4 x from restricted,raw,scalar]
    simp only [Pi.smul_apply,smul_eq_mul,unit,one_mul]
    rw [indicator_of_mem (show x∈symmetricInterval 4 from ⟨by linarith [inside.1],by linarith [inside.2]⟩)]
  have mean:=mean_of_gap (F.box 4) 1 quarter
  have each (n : ℕ+) : Flux.lowerPullback n (F.box 4)=0 := by
    have np : 0<((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => x/((n : ℕ) : ℝ)) volume volume := by
      simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using
        Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
          (r := (((n : ℕ) : ℝ))⁻¹) (inv_ne_zero np.ne')
    apply Lp.ext
    filter_upwards [FiniteMobiusResolventFlux.lower_pullback_read n (F.box 4),
      ae_restrict_of_ae (qmp.ae_eq (FiniteMobiusResolventFlux.box_read 4)),
      ae_restrict_mem (measurableSet_symmetricInterval 4),Lp.coeFn_zero ℂ 2 (volume.restrict (symmetricInterval 4))]
      with x source raw inside zero
    rw [source,mean,zero]
    have small : x/((n : ℕ) : ℝ)∈symmetricInterval 4 := by
      apply abs_le.mp
      rw [abs_div,abs_of_pos np,div_le_iff₀ np]
      have one : (1 : ℝ)≤((n : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr n.pos)
      have bound:=abs_le.mpr inside
      nlinarith
    simp only [Function.comp_def] at raw
    rw [raw,indicator_of_mem small,sub_self]
    simp only [Pi.zero_apply]
  unfold Flux.M Flux.lowerWindow
  simp only [ContinuousLinearMap.comp_apply,sum_apply,smul_apply,each,smul_zero,
    Finset.sum_const_zero,map_zero]

def spread : ℝ := -Real.log 16
private theorem spread_radius : q*Real.exp (-spread)=4 := by
  unfold spread
  rw [neg_neg,Real.exp_log (by norm_num : (0 : ℝ)<16)]
  norm_num

/-- The real finite source operation now reads only the supplied original quarter. -/
theorem window_spread (value : BurnolL2) :
    Flux.M (burnolMultiplicativeDilation spread value)=
      Flux.M (burnolMultiplicativeDilation spread
        (burnolQuarterZeroExtension (burnolQuarterRestriction value))) := by
  have actual:=FiniteMobiusResolventFlux.action_cutoff q (by norm_num) spread value
  rw [spread_radius] at actual
  change burnolMultiplicativeDilation spread
    (burnolQuarterZeroExtension (burnolQuarterRestriction value))=F.cutoff 4
      (burnolMultiplicativeDilation spread value) at actual
  rw [actual,M_cutoff]

theorem spread_flat_zero (value : BurnolL2) (k : ℂ)
    (gap : burnolQuarterRestriction value=k • intervalConstant q) :
    Flux.M (burnolMultiplicativeDilation spread value)=0 := by
  rw [window_spread,gap,map_smul,map_smul,map_smul]
  have box:=FiniteMobiusResolventFlux.action_box q (by norm_num) spread
  rw [spread_radius] at box
  change burnolMultiplicativeDilation spread (burnolQuarterZeroExtension (intervalConstant q))=_ at box
  rw [box,map_smul,M_box_zero,smul_zero,smul_zero]

theorem fourier_kernel_quarter :
    burnolQuarterRestriction (FL K)=Flux.actualMean (FL K) • intervalConstant q := by
  let physical : BurnolPaAmbientCarrier :=
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompletedMellinRieszVector c)
  have source : burnolQuarterRestriction (FL K)=
      burnolConstantGapCoefficient q physical • intervalConstant q :=
    (burnolGenericPhysicalValue_gap physical).symm
  rw [mean_of_gap _ _ source]
  exact source


end OriginalWholeDebtRPrimitiveMobiusSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
