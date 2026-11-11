import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.TestSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial
open Complex Filter MeasureTheory Set
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped BigOperators Topology InnerProductSpace
namespace Material
export CenteredGram.IntegralGraphJointAction.OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial (actualIterate)
end Material

/-- The scalar source recursively consumes the preceding bill at the actual inward scale. -/
def resolventBill (parameter:ℂ) (initial:ℝ→ℂ) : ℕ→ℝ→ℂ
  | 0 => initial
  | k+1 => fun b => -∫t:ℝ in Ioi 0,
      Complex.exp (-star parameter*(t:ℂ)/2)*resolventBill parameter initial k (b*Real.exp (-t/2))

def generatorBill (c:BurnolCompletedMellinCoordinate) (k:ℕ)
    (g:burnolCompactAnnulusSource) (p:Fin 2) (b:ℝ) : ℂ :=
  resolventBill c.value (baseBill g p) k b

/-- The continuous subtraction uses the same [0,N] source inventory as the integer count. -/
def countedBill (c:BurnolCompletedMellinCoordinate) (k N:ℕ)
    (g:burnolCompactAnnulusSource) (p:Fin 2) : ℂ :=
  (∑n∈Finset.Ico 1 N,generatorBill c k g p n)-
    ∫b:ℝ in Ioc 0 (N:ℝ),generatorBill c k g p b

def arithmeticFunctional (c:BurnolCompletedMellinCoordinate) (k N:ℕ) :
    BurnolCompactCoPoissonLinearSource →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun i => LinearMap.toSpanSingleton ℂ ℂ (countedBill c k N i.1 i.2)

private theorem channel_shift (b s:ℝ) (hb:0<b) (value:BurnolL2) :
    ContinuousChannels.channel 1 b (burnolMultiplicativeDilation s value)=
      (Real.exp (s/2):ℂ) • ContinuousChannels.channel 1 (b*Real.exp s) value := by
  apply Lp.ext
  filter_upwards [channel1_read (burnolMultiplicativeDilation s value)
    (burnolL2RawNormalizedDilation s value) (burnolMultiplicativeDilation_coeFn s value) b hb,
    Lp.coeFn_smul (Real.exp (s/2):ℂ) (ContinuousChannels.channel 1 (b*Real.exp s) value),
    channel1_read value value (Filter.EventuallyEq.refl _ _) (b*Real.exp s) (by positivity)] with x first smulRead last
  rw [first,smulRead]
  change burnolL2RawNormalizedDilation s value (b*x)=(Real.exp (s/2):ℂ)*
    ContinuousChannels.channel 1 (b*Real.exp s) value x
  rw [last,burnolL2RawNormalizedDilation]
  congr 2
  ring

private theorem right_quarter (c:BurnolCompletedMellinCoordinate) :
    (1/4:ℝ)<(c.value/2).re := by
  rw [Complex.div_re]
  norm_num
  linarith [c.rightHalf]

private def channelMap (b:ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
  (Real.sqrt b:ℂ)⁻¹ • (burnolMultiplicativeDilation (Real.log b)).toLinearIsometry.toContinuousLinearMap

private theorem channelMap_read (b:ℝ) (value:BurnolL2) :
    channelMap b value=ContinuousChannels.channel 1 b value := by
  simp only [channelMap,smul_apply,ContinuousChannels.channel,one_mul]
  rfl

private theorem source_weight (c:BurnolCompletedMellinCoordinate) (t:ℝ) :
    star (positiveMellinQuarterRightResolventWeight (c.value/2) t * (Real.exp ((-t/2)/2):ℂ))=
      Complex.exp (-star c.value*(t:ℂ)/2) := by
  have exponent:((1/4:ℂ)-c.value/2)*(t:ℂ)+(((-t/2)/2:ℝ):ℂ)= -c.value*(t:ℂ)/2 := by
    push_cast
    ring
  rw [positiveMellinQuarterRightResolventWeight,Complex.ofReal_exp,←Complex.exp_add,exponent,
    ←starRingEnd_apply,←Complex.exp_conj]
  congr 1
  rw [starRingEnd_apply,star_div₀,star_mul,star_neg,star_ofNat]
  rw [show star (t:ℂ)=(t:ℂ) from Complex.conj_ofReal t]
  ring

private theorem action_integrand (c:BurnolCompletedMellinCoordinate) (b:ℝ) (hb:0<b)
    (value test:BurnolL2) (t:ℝ) :
    inner ℂ (channelMap b (burnolDirectRightResolventIntegrand (c.value/2) value t)) test=
      Complex.exp (-star c.value*(t:ℂ)/2)*
        inner ℂ (ContinuousChannels.channel 1 (b*Real.exp (-t/2)) value) test := by
  rw [burnolDirectRightResolventIntegrand,map_smul,channelMap_read,channel_shift b (-t/2) hb,
    smul_smul,inner_smul_left,starRingEnd_apply,source_weight]

private theorem left_integral (family:ℝ→BurnolL2) (hf:IntegrableOn family (Ioi 0)) (test:BurnolL2) :
    inner ℂ (∫t:ℝ in Ioi 0,family t) test=∫t:ℝ in Ioi 0,inner ℂ (family t) test := by
  rw [←inner_conj_symm,←integral_inner hf]
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  exact inner_conj_symm _ _

private theorem R_pairing (c:BurnolCompletedMellinCoordinate) (b:ℝ) (hb:0<b) (value test:BurnolL2) :
    inner ℂ (ContinuousChannels.channel 1 b (burnolDirectRightResolvent (c.value/2) value)) test=
      -∫t:ℝ in Ioi 0,Complex.exp (-star c.value*(t:ℂ)/2)*
        inner ℂ (ContinuousChannels.channel 1 (b*Real.exp (-t/2)) value) test := by
  have native:=burnolDirectRightResolventIntegrand_integrableOn (c.value/2) (right_quarter c) value
  rw [←channelMap_read,burnolDirectRightResolvent,map_neg,inner_neg_left,
    ←(channelMap b).integral_comp_comm native,left_integral _ ((channelMap b).integrable_comp native)]
  congr 1
  exact integral_congr_ae (ae_of_all _ (action_integrand c b hb value test))

/-- Only the proof identifies the independent scalar recursion with the original R action. -/
theorem resolventBill_read (c:BurnolCompletedMellinCoordinate) (initial:ℝ→ℂ)
    (value test:BurnolL2)
    (source:∀b,0<b → initial b=inner ℂ (ContinuousChannels.channel 1 b value) test)
    (k:ℕ) (b:ℝ) (hb:0<b) :
    resolventBill c.value initial k b=
      inner ℂ (ContinuousChannels.channel 1 b (Material.actualIterate c value k)) test := by
  induction k generalizing b with
  | zero => exact source b hb
  | succ k previous =>
    rw [resolventBill,Material.actualIterate,R_pairing c b hb]
    dsimp only
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    rw [previous _ (by positivity)]

theorem generatorBill_read (c:BurnolCompletedMellinCoordinate) (k:ℕ)
    (g:burnolCompactAnnulusSource) (p:Fin 2) (b:ℝ) (hb:0<b) :
    generatorBill c k g p b=inner ℂ
      (ContinuousChannels.channel 1 b (Material.actualIterate c
        (2 • fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))) k))
      (burnolCompactCoPoissonGenerator (g,p):BurnolL2) :=
  resolventBill_read c _ _ _ (baseBill_read g p) k b hb

/-- Every scalar R step inherits Bochner integrability from that same full original action. -/
theorem generator_step_integrable (c:BurnolCompletedMellinCoordinate) (k:ℕ)
    (g:burnolCompactAnnulusSource) (p:Fin 2) (b:ℝ) (hb:0<b) :
    IntegrableOn (fun t:ℝ=>Complex.exp (-star c.value*(t:ℂ)/2)*
      generatorBill c k g p (b*Real.exp (-t/2))) (Ioi 0) := by
  have native := ((channelMap b).integrable_comp
    (burnolDirectRightResolventIntegrand_integrableOn (c.value/2) (right_quarter c)
      (Material.actualIterate c (2 • fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))) k))).inner_const
        (𝕜:=ℂ) (burnolCompactCoPoissonGenerator (g,p):BurnolL2)
  apply native.congr
  filter_upwards with t
  rw [action_integrand c b hb,generatorBill_read c k g p _ (by positivity)]

theorem generator_count_integrable (c:BurnolCompletedMellinCoordinate) (k N:ℕ)
    (g:burnolCompactAnnulusSource) (p:Fin 2) :
    IntegrableOn (generatorBill c k g p) (Ioc 0 (N:ℝ)) := by
  have native := (ContinuousChannels.channel_integrable 1 N (Material.actualIterate c
    (2 • fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))) k)).inner_const
      (𝕜:=ℂ) (burnolCompactCoPoissonGenerator (g,p):BurnolL2)
  apply native.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with b inside
  exact (generatorBill_read c k g p b inside.1).symm

theorem counted_zero (c:BurnolCompletedMellinCoordinate) (k:ℕ)
    (g:burnolCompactAnnulusSource) (p:Fin 2) : countedBill c k 0 g p=0 := by
  simp [countedBill]

theorem counted_one (c:BurnolCompletedMellinCoordinate) (k:ℕ)
    (g:burnolCompactAnnulusSource) (p:Fin 2) :
    countedBill c k 1 g p= -∫b:ℝ in Ioc 0 1,generatorBill c k g p b := by
  simp [countedBill]

theorem countedBill_read (c:BurnolCompletedMellinCoordinate) (k N:ℕ)
    (g:burnolCompactAnnulusSource) (p:Fin 2) :
    countedBill c k N g p=inner ℂ
      (DualSource.source N (Material.actualIterate c
        (2 • fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))) k))
      (burnolCompactCoPoissonGenerator (g,p):BurnolL2) := by
  rw [countedBill,DualSource.source,inner_sub_left,sum_inner]
  congr 1
  · apply Finset.sum_congr rfl
    intro n inside
    exact generatorBill_read c k g p n (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Ico.mp inside).1)
  · have int:=ContinuousChannels.channel_integrable 1 N (Material.actualIterate c
        (2 • fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))) k)
    have left:(∫b:ℝ in Ioc 0 (N:ℝ),inner ℂ
        (ContinuousChannels.channel 1 b (Material.actualIterate c
          (2 • fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))) k))
        (burnolCompactCoPoissonGenerator (g,p):BurnolL2))=
          inner ℂ (∫b:ℝ in Ioc 0 (N:ℝ),ContinuousChannels.channel 1 b (Material.actualIterate c
          (2 • fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))) k))
        (burnolCompactCoPoissonGenerator (g,p):BurnolL2) := by
      rw [←inner_conj_symm,←integral_inner int,←integral_conj]
      exact integral_congr_ae (ae_of_all _ (fun b=>(inner_conj_symm _ _).symm))
    rw [←left]
    exact setIntegral_congr_fun measurableSet_Ioc (fun b inside=>generatorBill_read c k g p b inside.1)

theorem functional_single (c:BurnolCompletedMellinCoordinate) (k N:ℕ)
    (i:BurnolCompactCoPoissonGeneratorIndex) (a:ℂ) :
    arithmeticFunctional c k N (Finsupp.single i a)=a*countedBill c k N i.1 i.2 := by
  simp [arithmeticFunctional]

theorem functional_read (c:BurnolCompletedMellinCoordinate) (k N:ℕ)
    (u:BurnolCompactCoPoissonLinearSource) :
    arithmeticFunctional c k N u=inner ℂ
      (DualSource.source N (Material.actualIterate c
        (2 • fourierL2 (burnolReciprocalStepNativeWave 1 (3/2))) k))
      (burnolCompactCoPoissonLanding u:BurnolL2) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add,Submodule.coe_add,inner_add_right,ha,hb]
  | single i a =>
    rw [functional_single,burnolCompactCoPoissonLanding_single]
    change _=inner ℂ _ (a • (burnolCompactCoPoissonGenerator i:BurnolL2))
    rw [inner_smul_right,countedBill_read]

end CountedPaInitial
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
