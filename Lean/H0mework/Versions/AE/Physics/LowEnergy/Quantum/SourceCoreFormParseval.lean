import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceBulkTimeFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceCoreFormParseval
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceBulkTwoTime SourceInverseNoetherChannelGap SourceInverseNoetherEnergy SourceJointResidualEnergy
open SourceFourPoleEnergyClosed SourceInverseFormSpectral SourceScalarPositiveBulkWard SourceScalarInverseNativeEnergy
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def coreForm (A : End) (f : QuantumTest) : ℝ := (sourcePair f (A f)).re

private def coefficient (F : Index) (A T : End) (g : diagonal.domain) (i j : Channel F) : ℂ :=
  sourcePair (T (channelTest F g i)) (A (T (channelTest F g j)))
private def frequencyGram (F : Index) (μ : ℝ) (A T : End) (g : diagonal.domain) (w : ℝ) : ℂ :=
  ∑ i : Channel F,∑ j : Channel F,star (pole μ (channelValue F i) w)*pole μ (channelValue F j) w*coefficient F A T g i j
private def timeGram (F : Index) (μ : ℝ) (A T : End) (g : diagonal.domain) (t : ℝ) : ℂ :=
  ∑ i : Channel F,∑ j : Channel F,Complex.exp (-gap μ (channelValue F i) (channelValue F j)*(t : ℂ))*coefficient F A T g i j

private theorem pair_sum (F : Index) (A T : End) (g : diagonal.domain) (c : Channel F → ℂ) :
    sourcePair (T (∑ i,c i • channelTest F g i)) (A (T (∑ j,c j • channelTest F g j)))=
      ∑ i,∑ j,star (c i)*c j*coefficient F A T g i j := by
  simp only [coefficient,sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,
    inner_smul_right,starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem frequency_value (F : Index) (μ : ℝ) (hμ : 0<μ) (A T : End) (g : diagonal.domain) (w : ℝ) :
    (frequencyGram F μ A T g w).re=coreForm A (T (state F (line μ w) (by simpa only [line_im] using hμ.ne') g)) := by
  unfold coreForm
  rw [actual_state_channels,pair_sum]
  rfl

private theorem time_factor (μ a b t : ℝ) :
    Complex.exp (-gap μ a b*(t : ℂ))=
      (Real.exp (-2*μ*t) : ℂ)*star (phase a t)*phase b t := by
  simp only [gap,phase,Complex.star_def,←Complex.exp_conj,Complex.ofReal_exp]
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal]
  push_cast
  ring

private theorem time_value (F : Index) (μ : ℝ) (A T : End) (g : diagonal.domain) (t : ℝ) :
    (timeGram F μ A T g t).re=Real.exp (-2*μ*t)*coreForm A (T (coreTime F g t)) := by
  have he : timeGram F μ A T g t=(Real.exp (-2*μ*t) : ℂ)*
      sourcePair (T (coreTime F g t)) (A (T (coreTime F g t))) := by
    unfold timeGram
    simp_rw [time_factor]
    rw [coreTime,pair_sum]
    simp only [Finset.mul_sum,phase]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,coreForm]

private theorem decay_integrable (μ a b : ℝ) (hμ : 0<μ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-gap μ a b*(t : ℂ))) (Set.Ioi 0) := by
  apply integrableOn_exp_mul_complex_Ioi
  simp [gap]
  linarith

private theorem decay_integral (μ a b : ℝ) (hμ : 0<μ) :
    (∫ t : ℝ in Set.Ioi 0,Complex.exp (-gap μ a b*(t : ℂ)))=(gap μ a b)⁻¹ := by
  have hn : (-gap μ a b).re<0 := by simp [gap];linarith
  rw [integral_exp_mul_complex_Ioi hn 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,div_neg,neg_div,neg_neg,one_div]

private theorem frequency_integrable (F : Index) (μ : ℝ) (hμ : 0<μ) (A T : End) (g : diagonal.domain) :
    Integrable (frequencyGram F μ A T g) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (two_pole_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _))
private theorem time_integrable (F : Index) (μ : ℝ) (hμ : 0<μ) (A T : End) (g : diagonal.domain) :
    IntegrableOn (timeGram F μ A T g) (Set.Ioi 0) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (decay_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _))

private theorem gram_integral (F : Index) (μ : ℝ) (hμ : 0<μ) (A T : End) (g : diagonal.domain) :
    (∫ w : ℝ,frequencyGram F μ A T g w)=
      (2*Real.pi : ℂ)*(∫ t : ℝ in Set.Ioi 0,timeGram F μ A T g t) := by
  unfold frequencyGram timeGram
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (two_pole_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (decay_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (two_pole_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _),
    integral_finsetSum _ (fun j _ => (decay_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const,integral_mul_const,decay_integral μ _ _ hμ]
  change twoPole μ (channelValue F i) (channelValue F j)*_= _
  rw [two_pole_closed μ _ _ hμ]
  ring

/-- The original single-source time form of a core insertion, retaining every interference term. -/
def formTime (F : Index) (μ : ℝ) (A T : End) (g : diagonal.domain) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*coreForm A (T (coreTime F g t))

/-- Full-frequency Parseval for every original core insertion, including collisions and escape. -/
theorem actual_core_form_parseval (F : Index) (μ : ℝ) (hμ : 0<μ) (A T : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => coreForm A (T (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))) ∧
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*coreForm A (T (coreTime F g t))) (Set.Ioi 0) ∧
    (∫ w : ℝ,coreForm A (T (state F (line μ w) (by simpa only [line_im] using hμ.ne') g)))=
      2*Real.pi*formTime F μ A T g := by
  have hf := (frequency_integrable F μ hμ A T g).re
  have ht := (time_integrable F μ hμ A T g).re
  refine ⟨hf.congr (Eventually.of_forall (frequency_value F μ hμ A T g)),
    ht.congr (Eventually.of_forall (time_value F μ A T g)),?_⟩
  have h := congrArg Complex.re (gram_integral F μ hμ A T g)
  have hr1 : (∫ w : ℝ,frequencyGram F μ A T g w).re=∫ w : ℝ,(frequencyGram F μ A T g w).re :=
    (integral_re (frequency_integrable F μ hμ A T g)).symm
  have hr2 : (∫ t : ℝ in Set.Ioi 0,timeGram F μ A T g t).re=∫ t : ℝ in Set.Ioi 0,(timeGram F μ A T g t).re :=
    (integral_re (time_integrable F μ hμ A T g)).symm
  rw [hr1,Complex.mul_re,
    show (2*Real.pi : ℂ).re=2*Real.pi by simp,
    show (2*Real.pi : ℂ).im=0 by simp,zero_mul,sub_zero,hr2] at h
  simpa only [frequency_value F μ hμ A T g,time_value F μ A T g,formTime] using! h

end LowEnergy.SourceCoreFormParseval
