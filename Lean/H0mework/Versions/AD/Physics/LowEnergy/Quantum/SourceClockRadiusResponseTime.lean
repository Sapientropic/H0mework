import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockRadiusResponseFinite
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCoreFormParseval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockRadiusResponseTime
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory GaussYukawaOperator GaussRadialDomain
open SourceMixedNativeReturn SourceScalarPositiveBulkWard SourceClockYukawaCubicCurrent
open SourceClockYukawaQ8RadiusBudget SourceClockRadiusResponseFinite
open SourceClockYukawaRadialMixedBudget SourceBulkTwoTime SourceJointResidualEnergy
open SourceInverseNoetherChannelGap SourceFourPoleEnergyClosed SourceScalarDoubleCurrent
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

/-- The source radius acts on the original core trajectory before the two returns are subtracted. -/
def radiusTimeCore (m ell : ℕ) (F : Index) (g : diagonal.domain) (t : ℝ) : QuantumTest :=
  thetaAction m ell (radiusAction (coreTime F g t)-coreTime F (radiusSource g) t)

private def coefficient (m ell : ℕ) (F : Index) (g : diagonal.domain) (i : Channel F) : H :=
  embed (thetaAction m ell (radiusAction (channelTest F g i)-channelTest F (radiusSource g) i))

private theorem resolvent_input (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    resolventCore F z hz (coreEquiv.symm g)=state F z hz g := by
  change state F z hz (coreEquiv (coreEquiv.symm g))=state F z hz g
  rw [coreEquiv.apply_symm_apply]

private theorem response_channels (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (w : ℝ) :
    embed (radiusResponseCore m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)=
      ∑ i : Channel F,pole μ (channelValue F i) w • coefficient m ell F g i := by
  unfold radiusResponseCore
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
  have hr : radiusAction (coreEquiv.symm g)=coreEquiv.symm (radiusSource g) := by
    unfold radiusSource
    rw [coreEquiv.symm_apply_apply]
  rw [hr,resolvent_input,resolvent_input,actual_state_channels,actual_state_channels]
  simp only [map_sum,map_smul,←Finset.sum_sub_distrib,←smul_sub,coefficient,pole]

private theorem time_channels (m ell : ℕ) (F : Index) (g : diagonal.domain) (t : ℝ) :
    embed (radiusTimeCore m ell F g t)=
      ∑ i : Channel F,phase (channelValue F i) t • coefficient m ell F g i := by
  unfold radiusTimeCore coreTime
  simp only [map_sum,map_smul,←Finset.sum_sub_distrib,←smul_sub,coefficient,phase]

private def frequencyGram (m ell : ℕ) (F : Index) (μ : ℝ) (g : diagonal.domain) (w : ℝ) : ℂ :=
  ∑ i : Channel F,∑ j : Channel F,
    (star (pole μ (channelValue F i) w)*pole μ (channelValue F j) w)*
      inner ℂ (coefficient m ell F g i) (coefficient m ell F g j)

private def timeGram (m ell : ℕ) (F : Index) (μ : ℝ) (g : diagonal.domain) (t : ℝ) : ℂ :=
  ∑ i : Channel F,∑ j : Channel F,
    Complex.exp (-gap μ (channelValue F i) (channelValue F j)*(t : ℂ))*
      inner ℂ (coefficient m ell F g i) (coefficient m ell F g j)

private theorem sum_square (m ell : ℕ) (F : Index) (g : diagonal.domain) (c : Channel F → ℂ) :
    ‖∑ i,c i • coefficient m ell F g i‖^2=
      (∑ i,∑ j,(star (c i)*c j)*inner ℂ (coefficient m ell F g i) (coefficient m ell F g j)).re := by
  change _=RCLike.re (∑ i,∑ j,(star (c i)*c j)*inner ℂ (coefficient m ell F g i) (coefficient m ell F g j))
  rw [←inner_self_eq_norm_sq (𝕜 := ℂ)]
  apply congrArg (RCLike.re : ℂ → ℝ)
  rw [sum_inner]
  simp only [inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem frequency_value (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (w : ℝ) :
    (frequencyGram m ell F μ g w).re=
      ‖embed (radiusResponseCore m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)‖^2 := by
  rw [response_channels m ell F μ hμ g w,sum_square]
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

private theorem time_value (m ell : ℕ) (F : Index) (μ : ℝ) (g : diagonal.domain) (t : ℝ) :
    (timeGram m ell F μ g t).re=Real.exp (-2*μ*t)*‖embed (radiusTimeCore m ell F g t)‖^2 := by
  rw [time_channels,sum_square]
  have he : timeGram m ell F μ g t=(Real.exp (-2*μ*t) : ℂ)*
      (∑ i : Channel F,∑ j : Channel F,(star (phase (channelValue F i) t)*phase (channelValue F j) t)*
        inner ℂ (coefficient m ell F g i) (coefficient m ell F g j)) := by
    unfold timeGram
    simp_rw [time_factor]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

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

private theorem frequency_integrable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Integrable (frequencyGram m ell F μ g) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (two_pole_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _))

private theorem time_integrable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    IntegrableOn (timeGram m ell F μ g) (Set.Ioi 0) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (decay_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _))

private theorem gram_integral (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    (∫ w : ℝ,frequencyGram m ell F μ g w)=
      (2*Real.pi : ℂ)*(∫ t : ℝ in Set.Ioi 0,timeGram m ell F μ g t) := by
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

/-- A single positive retarded time measure of the actual radius commutator. -/
def radiusTimeBudget (m ell : ℕ) (F : Index) (μ : ℝ) (g : diagonal.domain) : ENNReal :=
  ∫⁻ t : ℝ in Set.Ioi 0,ENNReal.ofReal (Real.exp (-2*μ*t)*‖embed (radiusTimeCore m ell F g t)‖^2)

theorem actual_radius_time_integrable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*‖embed (radiusTimeCore m ell F g t)‖^2) (Set.Ioi 0) :=
  (time_integrable m ell F μ hμ g).re.congr (Eventually.of_forall (time_value m ell F μ g))

theorem actual_radius_response_parseval (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    radiusResponseBudget m ell F μ hμ g=ENNReal.ofReal (2*Real.pi*μ)*radiusTimeBudget m ell F μ g := by
  have hf := ((frequency_integrable m ell F μ hμ g).re.congr
    (Eventually.of_forall (frequency_value m ell F μ hμ g))).const_mul μ
  have ht := actual_radius_time_integrable m ell F μ hμ g
  have h := congrArg Complex.re (gram_integral m ell F μ hμ g)
  have hr1 : (∫ w : ℝ,frequencyGram m ell F μ g w).re=∫ w : ℝ,(frequencyGram m ell F μ g w).re :=
    (integral_re (frequency_integrable m ell F μ hμ g)).symm
  have hr2 : (∫ t : ℝ in Set.Ioi 0,timeGram m ell F μ g t).re=∫ t : ℝ in Set.Ioi 0,(timeGram m ell F μ g t).re :=
    (integral_re (time_integrable m ell F μ hμ g)).symm
  rw [hr1,Complex.mul_re,
    show (2*Real.pi : ℂ).re=2*Real.pi by simp,
    show (2*Real.pi : ℂ).im=0 by simp,zero_mul,sub_zero,
    hr2] at h
  simp only [frequency_value m ell F μ hμ g,time_value] at h
  unfold radiusResponseBudget radiusTimeBudget
  rw [←ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall (fun _ => mul_nonneg hμ.le (sq_nonneg _))),
    ←ofReal_integral_eq_lintegral_ofReal ht (Eventually.of_forall (fun _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))),
    integral_const_mul,h,←ENNReal.ofReal_mul (by positivity : 0≤2*Real.pi*μ)]
  congr 1
  ring

/-- The original Gamma uses the same positive radius-response time measure at one common N. -/
theorem actual_original_radius_time_budget (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        ENNReal.ofReal (SourceFourPoleEnergyClosed.closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+ENNReal.ofReal (12*Real.pi*μ*SourceClockYukawaRadialGammaNativeBudget.sourceMuFactor μ k*radiusPrice)*
            radiusTimeBudget m ell F μ g := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_original_Q8_radius_response_budget μ hμ g k ε hε
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro sharp
  have h := hF sharp
  rw [actual_radius_response_parseval m ell F μ hμ g,←mul_assoc,
    ←ENNReal.ofReal_mul (by unfold SourceClockYukawaRadialGammaNativeBudget.sourceMuFactor radiusPrice;positivity)] at h
  have hc : 6*SourceClockYukawaRadialGammaNativeBudget.sourceMuFactor μ k*radiusPrice*(2*Real.pi*μ)=
      12*Real.pi*μ*SourceClockYukawaRadialGammaNativeBudget.sourceMuFactor μ k*radiusPrice := by ring
  rw [hc] at h
  exact h

end LowEnergy.SourceClockRadiusResponseTime
