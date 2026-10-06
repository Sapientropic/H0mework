import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceFourPoleEnergyClosed
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceClockWindowTime
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceClockFixedInputSeed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPoleInput
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceResolventLorentzian
open SourceResolventBandLimit MeasureTheory Filter
open scoped InnerProductSpace Topology
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussUnitaryHistory
open SourceScalarPairedTransport SourceMovingJetFlux SourceScalarPositiveBulkWard
open SourceRadiusHalfSourceBudget SourceRadiusHalfWindow
open SourceClockAcceleration SourceClockFixedInputSeed

private theorem denominator_ne (μ a w : ℝ) (hμ : 0<μ) : ((a:ℂ)-line μ w)≠0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im,Complex.ofReal_im,line_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
  exact hμ.ne' hi

private theorem pole_difference_formula (μ a w : ℝ) (hμ : 0<μ) :
    pole μ a w-pole μ 0 w=(-a:ℂ)*polePair μ a 0 w := by
  simp only [polePair,pole]
  simp only [Complex.ofReal_zero,zero_sub]
  have h0 : line μ w≠0 := by
    intro h
    have hi := congrArg Complex.im h
    rw [line_im,Complex.zero_im] at hi
    exact hμ.ne' hi
  change ((a:ℂ)-line μ w)⁻¹-(-line μ w)⁻¹=
    (-a:ℂ)*(((a:ℂ)-line μ w)⁻¹*(-line μ w)⁻¹)
  field_simp [denominator_ne μ a w hμ,h0]
  ring

private theorem difference_integrable (μ a : ℝ) (hμ : 0<μ) :
    Integrable (fun w : ℝ => pole μ a w-pole μ 0 w) := by
  simp_rw [pole_difference_formula μ a _ hμ]
  exact (same_half_integrable μ a 0 hμ).const_mul _

private theorem pole_imaginary (μ a w : ℝ) : (pole μ a w).im=μ*kernel μ a w := by
  simp [pole,line,kernel,Complex.inv_im,Complex.normSq_apply]
  ring

section Finite
variable {ι : Type*} [Fintype ι]

def input (a : ι → ℝ) (c : ι → ℂ) (μ w : ℝ) : ℂ :=
  ∑ i,c i*pole μ (a i) w
private def differenceInput (a : ι → ℝ) (c : ι → ℂ) (μ w : ℝ) : ℂ :=
  ∑ i,c i*(pole μ (a i) w-pole μ 0 w)

private theorem input_split (a : ι → ℝ) (c : ι → ℂ) (μ w : ℝ) :
    input a c μ w=differenceInput a c μ w+(∑ i,c i)*pole μ 0 w := by
  unfold input differenceInput
  simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
  ring

private theorem difference_input_integrable (a : ι → ℝ) (c : ι → ℂ) (μ : ℝ) (hμ : 0<μ) :
    Integrable (differenceInput a c μ) :=
  integrable_finsetSum Finset.univ (fun i _ => (difference_integrable μ (a i) hμ).const_mul (c i))

private theorem difference_input_integral (a : ι → ℝ) (c : ι → ℂ) (μ : ℝ) (hμ : 0<μ) :
    (∫ w : ℝ,differenceInput a c μ w)=0 := by
  unfold differenceInput
  rw [integral_finsetSum Finset.univ (fun i _ => (difference_integrable μ (a i) hμ).const_mul (c i))]
  simp_rw [integral_const_mul,pole_difference_integral μ _ 0 hμ,mul_zero]
  exact Finset.sum_const_zero

/-- The real total mass cancels the nonintegrable imaginary first-pole asymptote; every coherent channel is retained. -/
theorem finite_real_mass_input (a : ι → ℝ) (c : ι → ℂ) (μ : ℝ) (hμ : 0<μ)
    (hc : (∑ i,c i).im=0) :
    Integrable (fun w : ℝ => (input a c μ w).im) ∧
      (∫ w : ℝ,(input a c μ w).im)=Real.pi*(∑ i,c i).re := by
  have he (w : ℝ) : (input a c μ w).im=(differenceInput a c μ w).im+
      ((∑ i,c i).re*μ)*kernel μ 0 w := by
    rw [input_split,Complex.add_im,Complex.mul_im,hc,zero_mul,add_zero,pole_imaginary]
    ring
  have hd := difference_input_integrable a c μ hμ
  have hdi : Integrable (fun w : ℝ => (differenceInput a c μ w).im) := by
    simpa only [RCLike.im_to_complex] using hd.im
  have hk := (kernel_integrable μ 0 hμ).const_mul ((∑ i,c i).re*μ)
  have hi : Integrable (fun w : ℝ => (input a c μ w).im) :=
    (hdi.add hk).congr (Filter.Eventually.of_forall (fun w => (he w).symm))
  refine ⟨hi,?_⟩
  simp_rw [he]
  have him : (∫ w : ℝ,differenceInput a c μ w).im=∫ w : ℝ,(differenceInput a c μ w).im := by
    simpa only [RCLike.im_to_complex] using (integral_im hd).symm
  rw [integral_add hdi hk,←him,difference_input_integral a c μ hμ,
    Complex.zero_im,zero_add,integral_const_mul,kernel_integral μ 0 hμ]
  field_simp [hμ.ne']

def causalInput (advanced : Bool) (a : ι → ℝ) (c : ι → ℂ) (μ w : ℝ) : ℂ :=
  ∑ i,c i*(if advanced then star (pole μ (a i) w) else pole μ (a i) w)

/-- The advanced leg retains its independent channel phases; only the total real mass is used. -/
theorem finite_causal_real_mass_input (advanced : Bool) (a : ι → ℝ) (c : ι → ℂ)
    (μ : ℝ) (hμ : 0<μ) (hc : (∑ i,c i).im=0) :
    Integrable (fun w : ℝ => (causalInput advanced a c μ w).im) ∧
      (∫ w : ℝ,(causalInput advanced a c μ w).im)=causalSign advanced*Real.pi*(∑ i,c i).re := by
  cases advanced
  · simpa only [causalInput,causalSign,Bool.false_eq_true,↓reduceIte,one_mul,input] using
      finite_real_mass_input a c μ hμ hc
  · have hs : (∑ i,star (c i))=star (∑ i,c i) := by simp only [Complex.star_def,map_sum]
    have hc' : (∑ i,star (c i)).im=0 := by rw [hs,Complex.star_def,Complex.conj_im,hc,neg_zero]
    obtain ⟨hi,he⟩ := finite_real_mass_input a (fun i => star (c i)) μ hμ hc'
    have hf (w : ℝ) : causalInput true a c μ w=star (input a (fun i => star (c i)) μ w) := by
      simp only [causalInput,input,↓reduceIte,Complex.star_def,map_sum,map_mul,Complex.conj_conj]
    have him (w : ℝ) : (causalInput true a c μ w).im= -(input a (fun i => star (c i)) μ w).im := by
      rw [hf,Complex.star_def,Complex.conj_im]
    refine ⟨hi.neg.congr (Filter.Eventually.of_forall (fun w => (him w).symm)),?_⟩
    simp_rw [him]
    rw [integral_neg,he,hs,Complex.star_def,Complex.conj_re]
    simp only [causalSign,↓reduceIte,neg_mul,one_mul]

end Finite

def clockSeedIntegrand (advanced : Bool) (F : Index) (m ell : ℕ) (μ : ℝ) (hμ : 0<μ)
    (g : QuantumTest) (w : ℝ) : ℝ :=
  (sourcePair (halfAction m ell g) (clockCurrent (halfAction m ell
    (state F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) (coreEquiv g))))).im

private theorem causal_coefficient (advanced : Bool) (μ a w : ℝ) :
    ((a:ℂ)-causalPoint advanced μ w)⁻¹=
      if advanced then star (pole μ a w) else pole μ a w := by
  cases advanced
  · rfl
  · simp only [causalPoint,↓reduceIte,pole,star_inv₀,map_sub,Complex.star_def,Complex.conj_ofReal]

private theorem actual_seed_input (advanced : Bool) (F : Index) (m ell : ℕ)
    (μ : ℝ) (hμ : 0<μ) (g : QuantumTest) (w : ℝ) :
    clockSeedIntegrand advanced F m ell μ hμ g w=
      (causalInput advanced (channelValue F) (fixedClockCoefficient F m ell g) μ w).im := by
  unfold clockSeedIntegrand
  rw [actual_fixed_clock_channels]
  simp only [causalInput,causal_coefficient]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The original same-F current input has an exact all-frequency return to its fixed source seed, including escape. -/
theorem actual_fixed_clock_input_integral (advanced : Bool) (F : Index) (m ell : ℕ)
    (μ : ℝ) (hμ : 0<μ) (g : QuantumTest) :
    Integrable (clockSeedIntegrand advanced F m ell μ hμ g) ∧
      (∫ w : ℝ,clockSeedIntegrand advanced F m ell μ hμ g w)=
        causalSign advanced*Real.pi*fixedClockSeed m ell g := by
  have hc : (∑ i : Channel F,fixedClockCoefficient F m ell g i).im=0 := by
    rw [original_fixed_clock_coefficient_mass]
    exact Complex.ofReal_im _
  have h := finite_causal_real_mass_input advanced (channelValue F)
    (fixedClockCoefficient F m ell g) μ hμ hc
  have hf : clockSeedIntegrand advanced F m ell μ hμ g=
      fun w => (causalInput advanced (channelValue F) (fixedClockCoefficient F m ell g) μ w).im :=
    funext (actual_seed_input advanced F m ell μ hμ g)
  rw [hf]
  simpa only [original_fixed_clock_coefficient_mass,Complex.ofReal_re] using h

/-- The actual fixed clock forcing term is paid before F, upper cutoff, damping, or causal orientation are chosen. -/
theorem actual_fixed_clock_input_common_tail (g : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell : ℕ,∀ F : Index,∀ advanced : Bool,
      ∀ μ : ℝ,∀ hμ : 0<μ,
        |∫ w : ℝ,2*clockSeedIntegrand advanced F m ell μ hμ g w|≤ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := original_fixed_clock_seed_tail g (ε/(2*Real.pi)) (by positivity)
  refine ⟨N,fun m hm ell F advanced μ hμ => ?_⟩
  rw [integral_const_mul,(actual_fixed_clock_input_integral advanced F m ell μ hμ g).2]
  have hsign : |causalSign advanced|=1 := by cases advanced <;> simp [causalSign]
  rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),hsign,
    one_mul,abs_of_pos Real.pi_pos]
  have h := mul_le_mul_of_nonneg_left (hN m hm ell) (by positivity : 0≤2*Real.pi)
  have he : (2*Real.pi)*(ε/(2*Real.pi))=ε := mul_div_cancel₀ ε (by positivity)
  calc
    _=(2*Real.pi)*|fixedClockSeed m ell g| := by ring
    _≤(2*Real.pi)*(ε/(2*Real.pi)) := h
    _=ε := he

end LowEnergy.SourceClockPoleInput
