import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaSpinJointForce
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaRadialGammaNativeBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaJointSpinRemainingBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceClockYukawaCubicCurrent
open SourceClockYukawaSpinJointForce SourceClockYukawaRadialMixedClock
open SourceClockYukawaRadialMixedCore SourceClockYukawaRadialMixedBudget SourceClockYukawaRadialGammaNativeBudget
open SourceRelativePowerTail SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit
open SourceFourPoleEnergyClosed MeasureTheory Filter
open scoped InnerProductSpace Topology
attribute [local irreducible] state finiteResolvent compressionCore defectAction
  jointState jointForcing spinWord mixedState mixedPrice sourceMuFactor
  SourceClockYukawaRadialMixedGamma.mixedResponse

/-- The complete non-spin forcing is kept as one same-source word. -/
def remainingForce (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  jointForcing sharp m ell F z hz g mu-spinWord sharp m ell F z hz g mu

def remainingPrice (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) : ℝ :=
  η*(sourceTime 0)^2*jointCoframe (jointState sharp m ell F z hz g)-
    (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
      (remainingForce sharp m ell F z hz g mu)).im

def remainingBudget (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (η : ℝ) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (remainingPrice sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g η)

def jointMuEnergy (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (μ*columnNorm (jointState sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g))

private theorem compression_pair (F : Index) (p q : QuantumTest) :
    sourcePair p (compressionCore F q)=sourcePair (compressionCore F p) q := by
  have he (f : QuantumTest) : embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simp only [sourcePair,he]
  exact (GaussGradedCompression.compression_pair F _ _).symm

private theorem component_mu_ward (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (mu : Fin 8) :
    z.im*‖embed (jointState sharp m ell F z hz g mu)‖^2=
      -(sourcePair (jointState sharp m ell F z hz g mu) (jointForcing sharp m ell F z hz g mu)).im := by
  let f := jointState sharp m ell F z hz g mu
  have hroute : compressionCore F f=jointForcing sharp m ell F z hz g mu+z • f := by
    have h := actual_joint_source_equation sharp m ell F z hz g mu
    change diagonalAction f=jointForcing sharp m ell F z hz g mu+z • f+defectAction F f at h
    unfold defectAction at h
    simp only [LinearMap.sub_apply] at h
    linear_combination (norm := module) h
  have hreal : (sourcePair f (compressionCore F f)).im=0 := by
    have h := congrArg Complex.im (pair_conjugate f (compressionCore F f))
    rw [←compression_pair] at h
    simp only [Complex.conj_im] at h
    linarith
  have hn : inner ℂ (embed f) (embed f)=((‖embed f‖^2:ℝ):ℂ) := by
    simpa only [Complex.ofReal_pow] using! inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed f)
  have h := congrArg (fun q => (sourcePair f q).im) hroute
  rw [hreal] at h
  simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right] at h
  rw [hn] at h
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add] at h
  change 0=(sourcePair f (jointForcing sharp m ell F z hz g mu)).im+z.im*‖embed f‖^2 at h
  change z.im*‖embed f‖^2=-(sourcePair f (jointForcing sharp m ell F z hz g mu)).im
  linarith only [h]

/-- Every component uses the same actual selfadjoint compression and its complete defect. -/
theorem actual_joint_mu_ward (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    z.im*columnNorm (jointState sharp m ell F z hz g)=
      -(∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
        (jointForcing sharp m ell F z hz g mu)).im := by
  unfold columnNorm
  rw [Finset.mul_sum,Complex.im_sum,←Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun mu _ => component_mu_ward sharp m ell F z hz g mu)

private theorem remaining_point (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    z.im*columnNorm (jointState sharp m ell F z hz g) ≤
      remainingPrice sharp m ell F z hz g η+
        (jointPrice/η)*columnNorm (errorColumn sharp m ell F z hz g) := by
  have hs := original_joint_spin_pair_price sharp (windowState m ell F z hz g)
    (errorColumn sharp m ell F z hz g) η hη
  have hs' : |(∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
    (spinWord sharp m ell F z hz g mu)).im| ≤
    η*(sourceTime 0)^2*jointCoframe (jointState sharp m ell F z hz g)+
      jointPrice/η*columnNorm (errorColumn sharp m ell F z hz g) := by
    simpa only [jointState,spinWord] using hs
  have hf : (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
      (jointForcing sharp m ell F z hz g mu)).im=
    (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
      (remainingForce sharp m ell F z hz g mu)).im+
    (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
      (spinWord sharp m ell F z hz g mu)).im := by
    simp only [remainingForce,sourcePair,map_sub,inner_sub_right,Finset.sum_sub_distrib,
      Complex.sub_im]
    ring
  have hneg := neg_le_abs (∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
    (spinWord sharp m ell F z hz g mu)).im
  rw [actual_joint_mu_ward,hf]
  unfold remainingPrice
  linarith only [hs',hneg]

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem error_embed (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (mu : Fin 8) :
    embed (errorColumn sharp m ell F z hz g mu)=
      inverseRadius (finiteResolvent F z (embed (thetaAction m ell
        (SourceClockYukawaSpinClosure.spinClosureCoefficient sharp mu (inputCore g)))))-
      finiteResolvent F z (inverseRadius (embed (thetaAction m ell
        (SourceClockYukawaSpinClosure.spinClosureCoefficient sharp mu (inputCore g))))) := by
  simp only [errorColumn,radialMap,LinearMap.sub_apply,Module.End.mul_apply,map_sub,
    ←GaussRadialDomain.inverse_core,resolvent_embed]

private theorem error_measurable (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal (columnNorm (errorColumn sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g))) := by
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hm (mu : Fin 8) : Measurable (fun w : ℝ => ENNReal.ofReal
      (‖embed (errorColumn sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g mu)‖^2)) := by
    simp_rw [error_embed]
    exact (((inverseRadius.continuous.comp (hr.clm_apply continuous_const)).sub
      (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  have he : (fun w : ℝ => ENNReal.ofReal (columnNorm (errorColumn sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g)))=
    (fun w : ℝ => ∑ mu : Fin 8,ENNReal.ofReal (‖embed (errorColumn sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g mu)‖^2)) := by
    funext w
    exact ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)
  rw [he]
  exact Finset.measurable_sum Finset.univ (fun mu _ => hm mu)

private theorem remaining_integral (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    jointMuEnergy sharp m ell F μ hμ g ≤ remainingBudget sharp m ell F μ hμ g η+
      ENNReal.ofReal (jointPrice/η)*(∫⁻ w : ℝ,ENNReal.ofReal (columnNorm
        (errorColumn sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g))) := by
  have hP : 0 ≤ jointPrice/η := by unfold jointPrice;positivity
  have hm : Measurable (fun w : ℝ => ENNReal.ofReal (jointPrice/η)*ENNReal.ofReal (columnNorm
      (errorColumn sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g))) :=
    (error_measurable sharp m ell F μ hμ g).const_mul _
  unfold jointMuEnergy remainingBudget
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (remainingPrice sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g η)+
      ENNReal.ofReal (jointPrice/η)*ENNReal.ofReal (columnNorm (errorColumn sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g)) := by
      apply lintegral_mono
      intro w
      have h := remaining_point sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g η hη
      have h' : μ*columnNorm (jointState sharp m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g) ≤
        remainingPrice sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g η+
          jointPrice/η*columnNorm (errorColumn sharp m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g) := by simpa only [line_im] using h
      apply (ENNReal.ofReal_le_ofReal h').trans
      exact ENNReal.ofReal_add_le.trans (add_le_add (le_refl _) (le_of_eq (ENNReal.ofReal_mul hP)))
    _ = _ := by rw [lintegral_add_right _ hm,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Source-fixed endpoint tails pay the complete spin part of the original eight-component mu Ward. -/
theorem actual_joint_remaining_mu_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,∀ sharp : Bool,
      jointMuEnergy sharp m ell F μ hμ g ≤ ENNReal.ofReal ε+remainingBudget sharp m ell F μ hμ g η := by
  intro ε hε
  let C := jointPrice/η
  have hC : 0 ≤ C := by unfold C jointPrice;positivity
  let δ := ε/(C+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨N,hN⟩ := actual_joint_error_common_tail μ hμ g δ hδ
  refine ⟨N,fun m hm ell hml F sharp => ?_⟩
  have hb := remaining_integral sharp m ell F μ hμ g η hη
  have he := hN m hm ell hml F sharp
  have hc : ENNReal.ofReal C*ENNReal.ofReal δ ≤ ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    have hd : δ*(C+1)=ε := by dsimp [δ];field_simp
    nlinarith only [hd,hδ]
  exact (hb.trans (add_le_add (le_refl _) ((mul_le_mul le_rfl he zero_le zero_le).trans hc))).trans_eq (add_comm _ _)

private theorem actual_mixed_amplitude (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) :
    mixedAmplitude sharp m ell F z g k=
      inner ℂ (k:H) (finiteResolvent F z (embed (jointState sharp m ell F z hz g 0))) := by
  rw [actual_joint_zero_state]
  unfold mixedAmplitude SourceClockYukawaRadialMixedClock.mixedState
  have he : embed (coreEquiv.symm (radiusSource g))=(radiusSource g:H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [←he,actual_mixed_response_source sharp m ell F z hz]

private theorem amplitude_joint_mu_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (w : ℝ) :
    ‖mixedAmplitude sharp m ell F (line μ w) g k‖^2 ≤ sourceMuFactor μ k*
      (μ*columnNorm (jointState sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)) := by
  let z := line μ w
  have hz : z.im≠0 := by simpa only [z,line_im] using hμ.ne'
  let f := jointState sharp m ell F z hz g 0
  have hR : ‖finiteResolvent F z‖ ≤ 1/μ := by
    simpa only [z,line_im,abs_of_pos hμ] using finite_resolvent_norm F z hz
  have hi := (norm_inner_le_norm (𝕜 := ℂ) (k:H) (finiteResolvent F z (embed f))).trans
    (mul_le_mul_of_nonneg_left (((finiteResolvent F z).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hR (norm_nonneg _))) (norm_nonneg (k:H)))
  have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
  have hs : ‖embed f‖^2 ≤ columnNorm (jointState sharp m ell F z hz g) :=
    Finset.single_le_sum (fun mu _ => sq_nonneg ‖embed (jointState sharp m ell F z hz g mu)‖)
      (Finset.mem_univ (0:Fin 8))
  have hc : 0 ≤ sourceMuFactor μ k := by unfold sourceMuFactor;positivity
  have he : (‖(k:H)‖*((1/μ)*‖embed f‖))^2=sourceMuFactor μ k*(μ*‖embed f‖^2) := by
    unfold sourceMuFactor
    field_simp
  rw [he] at hi2
  rw [actual_mixed_amplitude sharp m ell F _ hz]
  exact hi2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hμ.le) hc)

private theorem actual_joint_mu_cost (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    mixedResponseCost sharp m ell F μ hμ g k ≤ ENNReal.ofReal (sourceMuFactor μ k)*jointMuEnergy sharp m ell F μ hμ g := by
  have hc : 0 ≤ sourceMuFactor μ k := by unfold sourceMuFactor;positivity
  unfold mixedResponseCost jointMuEnergy
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (sourceMuFactor μ k)*ENNReal.ofReal
      (μ*columnNorm (jointState sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hc]
      exact ENNReal.ofReal_le_ofReal (amplitude_joint_mu_bound sharp m ell F μ hμ g k w)
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Original Gamma directly consumes the same-source joint word after the full spin endpoint payment. -/
theorem actual_original_joint_remaining_budget (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (η : ℝ) (hη : 0<η) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+ENNReal.ofReal (3*sourceMuFactor μ k)*remainingBudget sharp m ell F μ hμ g η := by
  intro ε hε
  let κ := 3*sourceMuFactor μ k
  have hκ : 0 ≤ κ := by dsimp [κ];unfold sourceMuFactor;positivity
  let δ := ε/(2*(κ+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨N₀,h₀⟩ := actual_original_mixed_response_budget false μ hμ g k (ε/2) (by positivity)
  obtain ⟨N₁,h₁⟩ := actual_original_mixed_response_budget true μ hμ g k (ε/2) (by positivity)
  obtain ⟨N₂,h₂⟩ := actual_joint_remaining_mu_budget μ hμ g η hη δ hδ
  refine ⟨max N₀ (max N₁ N₂),fun m hm ell hml => ?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml] with F hf ht sharp
  have hg : ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
      ENNReal.ofReal (ε/2)+ENNReal.ofReal (3:ℝ)*mixedResponseCost sharp m ell F μ hμ g k := by
    cases sharp <;> assumption
  have hc := mul_le_mul (le_refl (ENNReal.ofReal (3:ℝ))) (actual_joint_mu_cost sharp m ell F μ hμ g k) zero_le zero_le
  rw [←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)] at hc
  have hp : ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*ENNReal.ofReal δ ≤ ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul hκ,←ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hd : δ*(2*(κ+1))=ε := by dsimp [δ];field_simp
    nlinarith only [hd,hδ]
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*jointMuEnergy sharp m ell F μ hμ g := hg.trans (add_le_add (le_refl _) hc)
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*(ENNReal.ofReal δ+remainingBudget sharp m ell F μ hμ g η) :=
      add_le_add (le_refl _) (mul_le_mul le_rfl (h₂ m (by omega) ell hml F sharp) zero_le zero_le)
    _ = (ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*ENNReal.ofReal δ)+
        ENNReal.ofReal κ*remainingBudget sharp m ell F μ hμ g η := by rw [mul_add,add_assoc]
    _ ≤ _ := add_le_add hp le_rfl

end LowEnergy.SourceClockYukawaJointSpinRemainingBudget
