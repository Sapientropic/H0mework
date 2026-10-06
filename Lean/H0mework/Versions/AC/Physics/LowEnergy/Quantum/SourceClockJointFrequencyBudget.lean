import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceClockSourceTail
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceClockSourceFixedReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockJointFrequencyBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussAdjointHistory SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceClockAcceleration SourceClockReflectedForm SourceClockWindowTime
open SourcePhysicalKineticSquare SourceScalarPositiveBulkWard SourceScalarPairedTransport SourceCoframeVolumeCurrent
open SourceRadiusHalfWindow SourceRadiusHalfSourceBudget SourceClockPoleInput SourceClockFixedInputSeed
open SourceClockSourceFixedReturn SourceClockSourceTail SourceJointResidualEnergy SourceFourPoleEnergyClosed
open SourceInverseChannelSourceJets SourceResolventBandLimit MeasureTheory Filter
open SourceInverseNoetherChannelGap
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] state diagonalAction compressionCore defectAction
private theorem causal_im (advanced : Bool) (μ w : ℝ) :
    (causalPoint advanced μ w).im=causalSign advanced*μ := by
  cases advanced <;> simp [causalPoint,causalSign,line_im]

private def causalCoefficient (advanced : Bool) (μ a w : ℝ) : ℂ :=
  if advanced then star (pole μ a w) else pole μ a w

private theorem causal_coefficient (advanced : Bool) (μ a w : ℝ) :
    ((a:ℂ)-causalPoint advanced μ w)⁻¹=causalCoefficient advanced μ a w := by
  cases advanced
  · rfl
  · simp only [causalCoefficient,causalPoint,↓reduceIte,pole,star_inv₀,map_sub,Complex.star_def,Complex.conj_ofReal]

private theorem causal_product_integrable (advanced : Bool) (μ a b : ℝ) (hμ : 0<μ) :
    Integrable (fun w : ℝ => star (causalCoefficient advanced μ a w)*causalCoefficient advanced μ b w) := by
  cases advanced
  · exact two_pole_integrable μ a b hμ
  · simpa only [causalCoefficient,↓reduceIte,star_star,mul_comm] using two_pole_integrable μ b a hμ

private theorem pair_channels (F : Index) (g : diagonal.domain) (A B : End) (c : Channel F → ℂ) :
    sourcePair (A (∑ i,c i • channelTest F g i)) (B (∑ j,c j • channelTest F g j))=
      ∑ i,∑ j,star (c i)*c j*sourcePair (A (channelTest F g i)) (B (channelTest F g j)) := by
  simp only [sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem causal_pair_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (A B : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => sourcePair (A (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g)) (B (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g))) := by
  have hi : Integrable (fun w : ℝ => ∑ i : Channel F,∑ j : Channel F,
      star (causalCoefficient advanced μ (channelValue F i) w)*causalCoefficient advanced μ (channelValue F j) w*
        sourcePair (A (channelTest F g i)) (B (channelTest F g j))) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      (causal_product_integrable advanced μ (channelValue F i) (channelValue F j) hμ).mul_const _))
  apply hi.congr
  exact Eventually.of_forall (fun w => by
    dsimp only
    rw [actual_state_channels F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g,pair_channels]
    simp only [causal_coefficient])

private theorem causal_pair_re_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (A B : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => (sourcePair (A (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g)) (B (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g))).re) := by
  simpa only [RCLike.re_to_complex] using (causal_pair_integrable advanced F μ hμ A B g).re

private theorem causal_form_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (A T : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => (sourcePair (T (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g)) (A (T (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g)))).re) :=
  causal_pair_re_integrable advanced F μ hμ T (A*T) g

private theorem causal_norm_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (A : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => ‖embed (A (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g))‖^2) := by
  have h := causal_pair_re_integrable advanced F μ hμ A A g
  apply h.congr
  exact Eventually.of_forall (fun w => by
    simpa only [sourcePair,RCLike.re_to_complex] using! inner_self_eq_norm_sq (𝕜 := ℂ) _)

private theorem polynomial_smooth (i j : Fin 6) : ContDiff ℝ ∞ (fun z : SourceCoordinateSlice =>
    GaussCoframeKinetic.polynomial z.1 i j) := by
  fin_cases i <;> fin_cases j <;> simp [GaussCoframeKinetic.polynomial] <;> fun_prop

private def polynomialAction (i j : Fin 6) : End := multiply
  (fun z => GaussCoframeKinetic.polynomial z.1 i j) (fun _ => (polynomial_smooth i j).contDiffAt)

private theorem causal_coframe_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (T : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => coframeGram (T (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g))) := by
  simp_rw [←original_reflected_coframe_gram]
  unfold reflectedForm
  have h := integrable_finsetSum (Finset.univ : Finset (Fin 6)) (fun i _ =>
    integrable_finsetSum (Finset.univ : Finset (Fin 6)) (fun j _ =>
      causal_pair_integrable advanced F μ hμ
        (SourceCoframeCovariantAction.covariantMomentum i*T)
        (((coordinateAction i*coordinateAction j)-polynomialAction i j)*
          SourceCoframeCovariantAction.covariantMomentum j*T) g))
  simpa only [Module.End.mul_apply,RCLike.re_to_complex] using! h.re

private theorem causal_scalar_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (T : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => scalarForm (T (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g))) := by
  unfold scalarForm
  exact integrable_finsetSum _ (fun a _ =>
    causal_norm_integrable advanced F μ hμ (covariantMomentum (scalarDirection a)*T) g)

private theorem causal_radius_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (T : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => radiusForm (T (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g))) := by
  unfold radiusForm
  exact causal_form_integrable advanced F μ hμ _ T g

private theorem compression_equation (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    compressionCore F (state F z hz g)=coreEquiv.symm g+z • state F z hz g := by
  have h := actual_raised_source F z hz g (1 : End)
  simp only [Module.End.one_apply,raisedDefect,mul_one,one_mul,sub_self,LinearMap.zero_apply,zero_add,
    defectAction,LinearMap.sub_apply] at h
  linear_combination (norm := module) h

private theorem inverse_real (f : QuantumTest) : (sourcePair f (inverseVolumeAction f)).im=0 := by
  have hp : sourcePair f (inverseVolumeAction f)=sourcePair (inverseVolumeAction f) f := by
    unfold inverseVolumeAction
    exact multiply_pair _ _ _ _
  have h := congrArg Complex.im (pair_conjugate f (inverseVolumeAction f))
  rw [←hp] at h
  simp only [Complex.conj_im] at h
  linarith

private theorem undamped_quadratic_word (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    undampedRemainder F m ell z hz g=sourcePrice F m ell z hz g-
      (sourceTime 0/2)*(sourcePair (inverseVolumeAction (halfAction m ell (state F z hz g)))
        (halfAction m ell (compressionCore F (state F z hz g)))).re+
      2*z.im*(sourcePair (halfAction m ell (state F z hz g))
        (clockCurrent (halfAction m ell (state F z hz g)))).re := by
  rw [compression_equation,map_add,map_smul]
  have hv : sourcePair (inverseVolumeAction (halfAction m ell (state F z hz g)))
      (halfAction m ell (state F z hz g))=sourcePair (halfAction m ell (state F z hz g))
        (inverseVolumeAction (halfAction m ell (state F z hz g))) := by
    unfold inverseVolumeAction
    exact (multiply_pair _ _ _ _).symm
  unfold undampedRemainder sourcePrice
  dsimp only
  simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right,Complex.add_re,Complex.mul_re]
  change _=_
  change (inner ℂ (embed (inverseVolumeAction (halfAction m ell (state F z hz g))))
    (embed (halfAction m ell (state F z hz g))))=
      inner ℂ (embed (halfAction m ell (state F z hz g)))
        (embed (inverseVolumeAction (halfAction m ell (state F z hz g)))) at hv
  rw [hv]
  have hr := inverse_real (halfAction m ell (state F z hz g))
  change (inner ℂ (embed (halfAction m ell (state F z hz g)))
    (embed (inverseVolumeAction (halfAction m ell (state F z hz g))))).im=0 at hr
  rw [hr]
  ring

private theorem undamped_integrable (advanced : Bool) (F : Index) (m ell : ℕ)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Integrable (fun w : ℝ => undampedRemainder F m ell (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g) := by
  have hp := actual_clock_source_price_integrable advanced F m ell μ hμ g
  have hv := (causal_pair_re_integrable advanced F μ hμ
    (inverseVolumeAction*halfAction m ell) (halfAction m ell*compressionCore F) g).const_mul (sourceTime 0/2)
  have hj := (causal_pair_re_integrable advanced F μ hμ (halfAction m ell)
    (clockCurrent*halfAction m ell) g).const_mul (2*causalSign advanced*μ)
  apply ((hp.sub hv).add hj).congr
  exact Eventually.of_forall (fun w => by
    dsimp only [Pi.add_apply,Pi.sub_apply]
    rw [undamped_quadratic_word]
    simp only [Module.End.mul_apply,causal_im]
    ring)

private theorem damping_integrable (advanced : Bool) (F : Index) (m ell : ℕ)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Integrable (fun w : ℝ => dampingError μ m ell
      (state F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g)) := by
  have hj := (causal_pair_re_integrable advanced F μ hμ (halfAction m ell)
    (clockCurrent*halfAction m ell) g).abs.const_mul (2*|μ|)
  have hc := (causal_coframe_integrable advanced F μ hμ (inverseVolumeAction*halfAction m ell) g).const_mul
    ((sourceTime 0)^2/16)
  have hr := (causal_radius_integrable advanced F μ hμ (halfAction m ell) g).const_mul ((sourceTime 0)^2)
  have hi := (hj.sub hc).sub hr
  apply hi.pos_part.congr
  exact Eventually.of_forall (fun w => by
    dsimp only [Pi.sub_apply,Module.End.mul_apply]
    exact max_comm _ _)

/-- The full undamped source retains its signed defect and fields after the paid fixed clock input exits. -/
def signedPrice (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  undampedRemainder F m ell z hz g-2*(sourcePair (halfAction m ell (coreEquiv.symm g))
    (clockCurrent (halfAction m ell (state F z hz g)))).im

def signedBudget (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) : ℝ :=
  ∫ w : ℝ,signedPrice F m ell (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g

def halfNormEnergy (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) : ℝ :=
  ∫ w : ℝ,‖embed (halfAction m ell (state F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g))‖^2

/-- Every remaining word is L1 on the actual causal leg; no separate V input integral or reader norm is assumed. -/
theorem actual_signed_price_integrable (advanced : Bool) (F : Index) (m ell : ℕ)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Integrable (fun w : ℝ => signedPrice F m ell (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g) := by
  have h := (undamped_integrable advanced F m ell μ hμ g).sub
    ((actual_fixed_clock_input_integral advanced F m ell μ hμ (coreEquiv.symm g)).1.const_mul 2)
  apply h.congr
  exact Eventually.of_forall (fun w => by
    dsimp only [Pi.sub_apply]
    simp only [signedPrice,clockSeedIntegrand,coreEquiv.apply_symm_apply])

private theorem source_budget_integral (advanced : Bool) (F : Index) (m ell : ℕ)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    sourceBudget advanced m ell F μ hμ g=ENNReal.ofReal (∫ w : ℝ,sourcePrice F m ell
      (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g) := by
  rw [actual_source_budget_fixed_return]
  unfold remainingBudget
  have hp := actual_clock_source_price_integrable advanced F m ell μ hμ g
  have hc := (actual_fixed_clock_input_integral advanced F m ell μ hμ (coreEquiv.symm g)).1.const_mul 2
  have he (w : ℝ) : SourceClockSourceFixedReturn.remainingPrice F m ell (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g=sourcePrice F m ell (causalPoint advanced μ w)
        (causal_nonreal advanced μ w hμ) g-2*clockSeedIntegrand advanced F m ell μ hμ (coreEquiv.symm g) w := by
    simp only [SourceClockSourceFixedReturn.remainingPrice,clockSeedIntegrand,coreEquiv.apply_symm_apply]
  simp_rw [he]
  rw [integral_sub hp hc,integral_const_mul,
    (actual_fixed_clock_input_integral advanced F m ell μ hμ (coreEquiv.symm g)).2]
  congr 1
  ring

private theorem undamped_integral (advanced : Bool) (F : Index) (m ell : ℕ)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    (∫ w : ℝ,undampedRemainder F m ell (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g)=
      signedBudget advanced m ell F μ hμ g+
        2*causalSign advanced*Real.pi*fixedClockSeed m ell (coreEquiv.symm g) := by
  have hs := actual_signed_price_integrable advanced F m ell μ hμ g
  have hc := (actual_fixed_clock_input_integral advanced F m ell μ hμ (coreEquiv.symm g)).1.const_mul 2
  have he (w : ℝ) : undampedRemainder F m ell (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g=signedPrice F m ell (causalPoint advanced μ w)
        (causal_nonreal advanced μ w hμ) g+2*clockSeedIntegrand advanced F m ell μ hμ (coreEquiv.symm g) w := by
    simp only [signedPrice,clockSeedIntegrand,coreEquiv.apply_symm_apply]
    ring
  simp_rw [he]
  rw [integral_add hs hc,integral_const_mul,
    (actual_fixed_clock_input_integral advanced F m ell μ hμ (coreEquiv.symm g)).2]
  unfold signedBudget
  congr 1
  ring

private theorem damping_sign (advanced : Bool) (μ : ℝ) (m ell : ℕ) (q : QuantumTest) :
    dampingError (causalSign advanced*μ) m ell q=dampingError μ m ell q := by
  cases advanced <;> simp [dampingError,causalSign]

/-- The original signed frequency budget consumes both paid common tails, leaving the joined defect/field integral and the fixed H0 successor. -/
theorem actual_source_budget_joint_frequency (ν : ℝ) (hν : 0<ν) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        sourceBudget advanced m ell F ν hν g ≤ ENNReal.ofReal ε+
          ENNReal.ofReal (4*signedBudget advanced m ell F ν hν g+
            (2/25:ℝ)*halfNormEnergy advanced m ell F ν hν (iterate 1 g)) := by
  intro ε hε
  obtain ⟨Ns,hs⟩ := actual_fixed_clock_input_common_tail (coreEquiv.symm g) (ε/8) (by positivity)
  obtain ⟨Nd,hd⟩ := actual_damping_error_common_tail ν hν g (ε/8) (by positivity)
  refine ⟨max Ns Nd,fun m hm ell hml => ?_⟩
  filter_upwards [actual_source_price_joint_upper g] with F hF advanced
  let P : ℝ → ℝ := fun w => sourcePrice F m ell (causalPoint advanced ν w) (causal_nonreal advanced ν w hν) g
  let U : ℝ → ℝ := fun w => undampedRemainder F m ell (causalPoint advanced ν w) (causal_nonreal advanced ν w hν) g
  let E : ℝ → ℝ := fun w => ‖embed (halfAction m ell (state F (causalPoint advanced ν w)
    (causal_nonreal advanced ν w hν) (iterate 1 g)))‖^2
  let D : ℝ → ℝ := fun w => dampingError ν m ell (state F (causalPoint advanced ν w)
    (causal_nonreal advanced ν w hν) g)
  have hP : Integrable P := actual_clock_source_price_integrable advanced F m ell ν hν g
  have hU : Integrable U := undamped_integrable advanced F m ell ν hν g
  have hE : Integrable E := causal_norm_integrable advanced F ν hν (halfAction m ell) (iterate 1 g)
  have hD : Integrable D := damping_integrable advanced F m ell ν hν g
  have hupper : ∫ w : ℝ,P w ≤ 4*(∫ w : ℝ,U w)+(2/25:ℝ)*(∫ w : ℝ,E w)+4*(∫ w : ℝ,D w) := by
    have hu := (hU.const_mul 4).add (hE.const_mul (2/25:ℝ))
    have hI := integral_mono hP (hu.add (hD.const_mul 4)) (fun w => by
      have h := hF m ell (causalPoint advanced ν w) (causal_nonreal advanced ν w hν)
      rw [causal_im,damping_sign] at h
      change P w ≤ 4*U w+(2/25:ℝ)*E w+4*D w
      exact h)
    have hab := integral_add (hU.const_mul 4) (hE.const_mul (2/25:ℝ))
    have habc := integral_add hu (hD.const_mul 4)
    simp only [Pi.add_apply] at hI hab habc
    rw [habc,hab] at hI
    simpa only [integral_const_mul] using hI
  have hsmallD : ∫ w : ℝ,D w ≤ ε/8 := by
    have he : ENNReal.ofReal (∫ w : ℝ,D w)=(∫⁻ w : ℝ,ENNReal.ofReal (D w)) :=
      ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall (fun w => le_max_left _ _))
    have h := hd m ((le_max_right _ _).trans hm) ell hml F advanced
    rw [←he] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤ε/8)).mp h
  have hsmallS : |2*causalSign advanced*Real.pi*fixedClockSeed m ell (coreEquiv.symm g)| ≤ ε/8 := by
    have h := hs m ((le_max_left _ _).trans hm) ell F advanced ν hν
    rw [integral_const_mul,(actual_fixed_clock_input_integral advanced F m ell ν hν (coreEquiv.symm g)).2] at h
    simpa only [mul_assoc] using h
  have hreal : (∫ w : ℝ,P w) ≤ ε+
      (4*signedBudget advanced m ell F ν hν g+(2/25:ℝ)*halfNormEnergy advanced m ell F ν hν (iterate 1 g)) := by
    change ∫ w : ℝ,sourcePrice F m ell (causalPoint advanced ν w) (causal_nonreal advanced ν w hν) g ≤ _
    change (∫ w : ℝ,sourcePrice F m ell (causalPoint advanced ν w) (causal_nonreal advanced ν w hν) g) ≤
      4*(∫ w : ℝ,undampedRemainder F m ell (causalPoint advanced ν w) (causal_nonreal advanced ν w hν) g)+
      (2/25:ℝ)*halfNormEnergy advanced m ell F ν hν (iterate 1 g)+4*(∫ w : ℝ,D w) at hupper
    rw [undamped_integral advanced F m ell ν hν g] at hupper
    have hs' := (le_abs_self (2*causalSign advanced*Real.pi*fixedClockSeed m ell (coreEquiv.symm g))).trans hsmallS
    linarith only [hupper,hsmallD,hs']
  rw [source_budget_integral]
  exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_add_le

/-- The unchanged original paired-radius cost reads the reduced signed source and fixed H0 successor on one shared cutoff and cofinal F. -/
def jointLegPrice (advanced : Bool) (ε : ℝ) (m ell : ℕ) (F : Index) (ν : ℝ) (hν : 0<ν)
    (g : diagonal.domain) (η : ℝ) : ENNReal :=
  ENNReal.ofReal (η*(Real.pi/ν*‖(g:H)‖^2))+
    ENNReal.ofReal ((1+η⁻¹)/(6*(sourceTime 0)^2))*
      (ENNReal.ofReal ε+ENNReal.ofReal (4*signedBudget advanced m ell F ν hν g+
        (2/25:ℝ)*halfNormEnergy advanced m ell F ν hν (iterate 1 g)))

theorem actual_paired_radius_joint_frequency (ν μ : ℝ) (hν : 0<ν) (hδ : ν<μ)
    (g k : diagonal.domain) (ηg ηk : ℝ) (hηg : 0<ηg) (hηk : 0<ηk) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        SourceRadiusClosedJointCost.pairedRadiusCost m ell F μ g k ≤
          ENNReal.ofReal (1/(4*Real.pi*(μ-ν)))*
            jointLegPrice true ε m ell F ν hν k ηk*jointLegPrice false ε m ell F ν hν g ηg := by
  intro ε hε
  obtain ⟨Ng,hg⟩ := actual_source_budget_joint_frequency ν hν g ε hε
  obtain ⟨Nk,hk⟩ := actual_source_budget_joint_frequency ν hν k ε hε
  refine ⟨max Ng Nk,fun m hm ell hml => ?_⟩
  filter_upwards [hg m ((le_max_left _ _).trans hm) ell hml,
    hk m ((le_max_right _ _).trans hm) ell hml] with F hFg hFk
  have hgl : legPrice false m ell F ν hν g ηg ≤ jointLegPrice false ε m ell F ν hν g ηg := by
    unfold legPrice jointLegPrice
    exact add_le_add (le_refl _) (mul_le_mul_right (hFg false) _)
  have hkl : legPrice true m ell F ν hν k ηk ≤ jointLegPrice true ε m ell F ν hν k ηk := by
    unfold legPrice jointLegPrice
    exact add_le_add (le_refl _) (mul_le_mul_right (hFk true) _)
  apply (actual_paired_radius_clock_budget m ell F ν μ hν hδ g k ηg ηk hηg hηk).trans
  exact mul_le_mul (mul_le_mul (le_refl _) hkl bot_le bot_le) hgl bot_le bot_le

end LowEnergy.SourceClockJointFrequencyBudget
