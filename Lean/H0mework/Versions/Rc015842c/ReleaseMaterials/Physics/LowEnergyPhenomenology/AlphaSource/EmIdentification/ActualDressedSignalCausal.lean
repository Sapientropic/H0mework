import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalPrice

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSignal
open CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumOriginalGreenFeedback
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumPhysicalHalfAxis
open SourcePropagationMotherEulerKernel
open ActualDressedFullCoulomb ActualDressedNoether
open Filter Set MeasureTheory
open scoped BigOperators Topology Interval Matrix
attribute [local irreducible] dressedSignalQuadrature dressedNoetherJet originalReadback

def dressedSignalCausalCoefficient (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) : ℝ :=
  2*((4/sourceReadGap p lambda)*dressedSignalLinearCoefficient event transfer (sourceCausalEta p lambda)+
    dressedSignalConstantCoefficient event transfer (sourceCausalEta p lambda))

def dressedSignalWeighted (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (t : ℝ) : SignalAmplitude→L[ℝ] (Fin 289→ℂ) :=
  laplaceWeight lambda t • dressedSignalQuadrature event transfer p t

private theorem scalar_growth_price (gap t : ℝ) (positive : 0<gap) :
    t ≤ (4/gap)*Real.exp ((gap/4)*t) := by
  have source : (gap/4)*t ≤ Real.exp ((gap/4)*t) :=
    (le_add_of_nonneg_right (show (0:ℝ) ≤ 1 by norm_num)).trans (Real.add_one_le_exp _)
  calc
    t ≤ Real.exp ((gap/4)*t)/(gap/4) :=
      (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm t (gap/4)] using source)
    _=(4/gap)*Real.exp ((gap/4)*t) := by field_simp

private theorem scalar_operator_price {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G]
    (c : ℂ) (A : E→L[ℝ]G) : ‖c • A‖ ≤ ‖c‖*‖A‖ := by
  apply (c • A).opNorm_le_bound (mul_nonneg (norm_nonneg c) A.opNorm_nonneg)
  intro x
  rw [smul_apply,norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg c)

private theorem decay_normalization (C sigma growth t : ℝ) :
    Real.exp (-sigma*t)*(2*(C*Real.exp ((sigma-growth)/4*t))*
      Real.exp ((4*((sigma-growth)/16)+growth)*t))=
        2*C*Real.exp (-((sigma-growth)/2)*t) := by
  calc
    _=2*C*(Real.exp (-sigma*t)*Real.exp ((sigma-growth)/4*t)*
      Real.exp ((4*((sigma-growth)/16)+growth)*t)) := by ring
    _=_ := by
      rw [←Real.exp_add,←Real.exp_add]
      congr 2
      ring

/-- This bound depends on source operator prices and the actual two unit states. -/
theorem dressed_signal_weighted_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re) (t : ℝ) (future : 0 ≤ t) :
    ‖dressedSignalWeighted event transfer p lambda t‖ ≤ dressedSignalCausalCoefficient event transfer p lambda*
      Real.exp (-(sourceReadGap p lambda/2)*t) := by
  have gap : 0<sourceReadGap p lambda := sub_pos.mpr off
  have eta : 0<sourceCausalEta p lambda := by unfold sourceCausalEta;positivity
  have coefficients:=dressed_signal_coefficient_nonnegative event transfer (sourceCausalEta p lambda) eta
  have source:=dressed_signal_quadrature_price event transfer p (sourceCausalEta p lambda) t eta future
  have rotated : ‖dressedSignalWeighted event transfer p lambda t‖ ≤
      ‖laplaceWeight lambda t‖*‖dressedSignalQuadrature event transfer p t‖ := by
    unfold dressedSignalWeighted
    exact scalar_operator_price _ _
  have multiply:=rotated.trans (mul_le_mul_of_nonneg_left source (norm_nonneg _))
  rw [laplace_norm] at multiply
  have grow:=scalar_growth_price (sourceReadGap p lambda) t gap
  have exponential : 1 ≤ Real.exp ((sourceReadGap p lambda/4)*t) := Real.one_le_exp (by positivity)
  have polynomial : dressedSignalLinearCoefficient event transfer (sourceCausalEta p lambda)*t+
      dressedSignalConstantCoefficient event transfer (sourceCausalEta p lambda)  ≤
      ((4/sourceReadGap p lambda)*dressedSignalLinearCoefficient event transfer (sourceCausalEta p lambda)+
        dressedSignalConstantCoefficient event transfer (sourceCausalEta p lambda))*
          Real.exp ((sourceReadGap p lambda/4)*t) := by
    have first:=mul_le_mul_of_nonneg_left grow coefficients.1
    have second:=le_mul_of_one_le_right coefficients.2 exponential
    refine (add_le_add first second).trans_eq ?_
    ring
  have polynomialScaled:=mul_le_mul_of_nonneg_left polynomial (show (0:ℝ) ≤ 2 by norm_num)
  have fullScaled:=mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right polynomialScaled (Real.exp_pos ((4*sourceCausalEta p lambda+sourceClockGrowth p)*t)).le)
      (Real.exp_pos (-lambda.re*t)).le
  exact multiply.trans (fullScaled.trans_eq (decay_normalization _ lambda.re (sourceClockGrowth p) t))

theorem dressed_signal_weighted_continuous (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) : Continuous (dressedSignalWeighted event transfer p lambda) := by
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  exact weight.smul (dressed_signal_quadrature_continuous event transfer p)

theorem dressed_signal_weighted_integrable (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re) :
    IntegrableOn (dressedSignalWeighted event transfer p lambda) (Ioi (0:ℝ)) := by
  have gap : 0<sourceReadGap p lambda := sub_pos.mpr off
  have majorant : IntegrableOn (fun t=>dressedSignalCausalCoefficient event transfer p lambda*
      Real.exp (-(sourceReadGap p lambda/2)*t)) (Ioi (0:ℝ)) :=
    (integrableOn_exp_mul_Ioi (a:=-(sourceReadGap p lambda/2)) (by linarith) 0).const_mul _
  apply majorant.mono' (dressed_signal_weighted_continuous event transfer p lambda).aestronglyMeasurable.restrict
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  exact dressed_signal_weighted_price event transfer p lambda off t ht.le

def dressedSignalWindow (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) : SignalAmplitude→L[ℝ] (Fin 289→ℂ) :=
  ∫t in (0:ℝ)..T,dressedSignalWeighted event transfer p lambda t

def dressedSignalHalfOperator (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) : SignalAmplitude→L[ℝ] (Fin 289→ℂ) :=
  ∫t in Ioi (0:ℝ),dressedSignalWeighted event transfer p lambda t

theorem dressed_signal_window_actual (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (a : SignalAmplitude) :
    dressedSignalWindow event transfer p lambda T a=
      fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*dressedSignalQuadrature event transfer p t a i := by
  rw [dressedSignalWindow,ContinuousLinearMap.intervalIntegral_apply
    ((dressed_signal_weighted_continuous event transfer p lambda).intervalIntegrable 0 T)]
  funext i
  have integrable : IntervalIntegrable (fun t=>dressedSignalWeighted event transfer p lambda t a) volume 0 T :=
    ((dressed_signal_weighted_continuous event transfer p lambda).clm_apply
      (continuous_const : Continuous (fun _ : ℝ=>a))).intervalIntegrable 0 T
  have coordinate:=(ContinuousLinearMap.proj i : (Fin 289→ℂ)→L[ℝ]ℂ).intervalIntegral_comp_comm integrable
  simp only [ContinuousLinearMap.proj_apply] at coordinate
  rw [←coordinate]
  rfl

theorem dressed_signal_window_noether (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (a : SignalAmplitude) :
    dressedSignalWindow event transfer p lambda T a=
      dressedNoetherForcing event transfer (nativeTimeSignal (sourceRealSignal p a)) lambda T+
        Complex.I • dressedNoetherForcing event transfer
          (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) lambda T := by
  rw [dressed_signal_window_actual]
  funext i
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  have first : IntervalIntegrable (fun t=>laplaceWeight lambda t*
      (dressedNoetherJet event transfer (nativeTimeSignal (sourceRealSignal p a)) t i).value) volume 0 T :=
    (weight.mul ((dressed_noether_jet_continuous event transfer _ (sourceTimeSignal_continuous p a) i).1)).intervalIntegrable 0 T
  have second : IntervalIntegrable (fun t=>laplaceWeight lambda t*
      (dressedNoetherJet event transfer (nativeTimeSignal (sourceRealSignal p (sourceQuadrature a))) t i).value) volume 0 T :=
    (weight.mul ((dressed_noether_jet_continuous event transfer _
      (sourceTimeSignal_continuous p (sourceQuadrature a)) i).1)).intervalIntegrable 0 T
  simp only [dressed_signal_quadrature_actual,mul_add,mul_left_comm (laplaceWeight lambda _),
    dressedNoetherForcing,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [intervalIntegral.integral_add first (second.const_mul Complex.I),intervalIntegral.integral_const_mul]

theorem dressed_signal_window_operator_norm (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re) :
    Tendsto (fun T=>dressedSignalWindow event transfer p lambda T) atTop
      (𝓝 (dressedSignalHalfOperator event transfer p lambda)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (dressed_signal_weighted_integrable event transfer p lambda off) tendsto_id

def dressedSignalTailPrice (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) : ℝ :=
  (2/sourceReadGap p lambda)*dressedSignalCausalCoefficient event transfer p lambda*
    Real.exp (-(sourceReadGap p lambda/2)*T)

/-- A bound on the complete linearized quantum operator, not an experimental alpha error. -/
theorem dressed_signal_half_operator_tail (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re) (T : ℝ) (future : 0 ≤ T) :
    ‖dressedSignalHalfOperator event transfer p lambda-dressedSignalWindow event transfer p lambda T‖ ≤
      dressedSignalTailPrice event transfer p lambda T := by
  have gap : 0<sourceReadGap p lambda := sub_pos.mpr off
  have whole:=dressed_signal_weighted_integrable event transfer p lambda off
  have tail:=whole.mono_set (Ioi_subset_Ioi future)
  have equation:=intervalIntegral.integral_interval_add_Ioi whole tail
  have difference : dressedSignalHalfOperator event transfer p lambda-dressedSignalWindow event transfer p lambda T=
      ∫t in Ioi T,dressedSignalWeighted event transfer p lambda t := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [dressedSignalHalfOperator,dressedSignalWindow,add_comm] using equation.symm
  have majorant : IntegrableOn (fun t=>dressedSignalCausalCoefficient event transfer p lambda*
      Real.exp (-(sourceReadGap p lambda/2)*t)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi (a:=-(sourceReadGap p lambda/2)) (by linarith) T).const_mul _
  have bounded : ∀ᵐt ∂volume.restrict (Ioi T),‖dressedSignalWeighted event transfer p lambda t‖ ≤
      dressedSignalCausalCoefficient event transfer p lambda*Real.exp (-(sourceReadGap p lambda/2)*t) := by
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t ht
    exact dressed_signal_weighted_price event transfer p lambda off t (future.trans ht.le)
  rw [difference]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono_ae tail.norm majorant bounded).trans_eq ?_)
  rw [integral_const_mul,integral_exp_mul_Ioi (by linarith)]
  unfold dressedSignalTailPrice
  field_simp

end LowEnergy.GaussComposite.ActualDressedSignal
