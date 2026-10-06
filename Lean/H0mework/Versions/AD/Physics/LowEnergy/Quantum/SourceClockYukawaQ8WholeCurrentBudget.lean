import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaQ8WholeCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaQ8WholeCurrentBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussRadialDomain SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport
open SourceClockYukawaSpinJointForce SourceClockYukawaSpinClosure SourceClockYukawaJointSpinRemainingBudget
open SourceClockYukawaRadialMixedClock SourceClockYukawaRadialMixedCore SourceClockYukawaRadialMixedBudget
open SourceClockYukawaRadialGammaNativeBudget SourceClockYukawaQ8WholeCurrent SourceClockYukawaCubicCurrent
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceFourPoleEnergyClosed MeasureTheory Filter
open scoped InnerProductSpace Topology
attribute [local irreducible] jointState finiteResolvent resolventCore sourceMuFactor wholePrice
  SourceClockYukawaRadialMixedGamma.mixedResponse

/-- One clipping of the complete scalar, matter, defect and original radial source current. -/
def wholeCurrentBudget (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ, ENNReal.ofReal (wholePrice m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g)

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im ≠ 0) (f : QuantumTest) :
    embed (resolventCore F z hz f) = finiteResolvent F z (embed f) := by
  unfold resolventCore SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem error_embed (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (g : diagonal.domain) (mu : Fin 8) :
    embed (errorColumn sharp m ell F z hz g mu) =
      inverseRadius (finiteResolvent F z (embed (thetaAction m ell
        (spinClosureCoefficient sharp mu (inputCore g))))) -
      finiteResolvent F z (embed (inverseAction (thetaAction m ell
        (spinClosureCoefficient sharp mu (inputCore g))))) := by
  simp only [errorColumn, radialMap, LinearMap.sub_apply, Module.End.mul_apply, map_sub,
    ← GaussRadialDomain.inverse_core, resolvent_embed]

private theorem error_measurable (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal (columnNorm (errorColumn sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g))) := by
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hm (mu : Fin 8) : Measurable (fun w : ℝ => ENNReal.ofReal
      (‖embed (errorColumn sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g mu)‖^2)) := by
    simp_rw [error_embed]
    exact (((inverseRadius.continuous.comp (hr.clm_apply continuous_const)).sub
      (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  have he : (fun w : ℝ => ENNReal.ofReal (columnNorm (errorColumn sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g))) =
    (fun w : ℝ => ∑ mu : Fin 8, ENNReal.ofReal (‖embed (errorColumn sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g mu)‖^2)) := by
    funext w
    exact ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)
  rw [he]
  exact Finset.measurable_sum Finset.univ (fun mu _ => hm mu)

private theorem integral_price (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) :
    jointMuEnergy sharp m ell F μ hμ g ≤ ENNReal.ofReal (2 : ℝ) * wholeCurrentBudget m ell F μ hμ g +
      ENNReal.ofReal (2 * μ) * (∫⁻ w : ℝ, ENNReal.ofReal (columnNorm
        (errorColumn sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g))) := by
  unfold jointMuEnergy wholeCurrentBudget
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal
        (wholePrice m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g) +
      ENNReal.ofReal (2 * μ) * ENNReal.ofReal (columnNorm
        (errorColumn sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)) := by
      apply lintegral_mono
      intro w
      have hp := actual_Q8_joint_mu_price sharp m ell F μ hμ g w
      apply (ENNReal.ofReal_le_ofReal hp).trans
      exact ENNReal.ofReal_add_le.trans (add_le_add
        (le_of_eq (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)))
        (le_of_eq (ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * μ))))
    _ = _ := by
      rw [lintegral_add_right _ ((error_measurable sharp m ell F μ hμ g).const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The already-generated fixed error tail pays internally at one N for both original branches. -/
theorem actual_Q8_whole_mu_payment (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ F : Index, ∀ sharp : Bool,
      jointMuEnergy sharp m ell F μ hμ g ≤
        ENNReal.ofReal ε + ENNReal.ofReal (2 : ℝ) * wholeCurrentBudget m ell F μ hμ g := by
  intro ε hε
  let δ := ε / (2 * μ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N, hN⟩ := actual_joint_error_common_tail μ hμ g δ hδ
  refine ⟨N, fun m hm ell hml F sharp => ?_⟩
  have he := hN m hm ell hml F sharp
  have hc : ENNReal.ofReal (2 * μ) * ENNReal.ofReal δ = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * μ)]
    congr 1
    dsimp [δ]
    field_simp
  exact ((integral_price sharp m ell F μ hμ g).trans
    (add_le_add le_rfl ((mul_le_mul le_rfl he zero_le zero_le).trans_eq hc))).trans_eq (add_comm _ _)

private theorem actual_mixed_amplitude (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (g k : diagonal.domain) :
    mixedAmplitude sharp m ell F z g k =
      inner ℂ (k : H) (finiteResolvent F z (embed (jointState sharp m ell F z hz g 0))) := by
  rw [actual_joint_zero_state]
  unfold mixedAmplitude SourceClockYukawaRadialMixedClock.mixedState
  have he : embed (coreEquiv.symm (radiusSource g)) = (radiusSource g : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [← he, actual_mixed_response_source sharp m ell F z hz]

private theorem amplitude_mu_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g k : diagonal.domain) (w : ℝ) :
    ‖mixedAmplitude sharp m ell F (line μ w) g k‖^2 ≤ sourceMuFactor μ k *
      (μ * columnNorm (jointState sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)) := by
  let z := line μ w
  have hz : z.im ≠ 0 := by simpa only [z, line_im] using hμ.ne'
  let f := jointState sharp m ell F z hz g 0
  have hR : ‖finiteResolvent F z‖ ≤ 1 / μ := by
    simpa only [z, line_im, abs_of_pos hμ] using finite_resolvent_norm F z hz
  have hi := (norm_inner_le_norm (𝕜 := ℂ) (k : H) (finiteResolvent F z (embed f))).trans
    (mul_le_mul_of_nonneg_left (((finiteResolvent F z).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hR (norm_nonneg _))) (norm_nonneg (k : H)))
  have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
  have hs : ‖embed f‖^2 ≤ columnNorm (jointState sharp m ell F z hz g) :=
    Finset.single_le_sum (fun mu _ => sq_nonneg ‖embed (jointState sharp m ell F z hz g mu)‖)
      (Finset.mem_univ (0 : Fin 8))
  have hc : 0 ≤ sourceMuFactor μ k := by unfold sourceMuFactor; positivity
  have he : (‖(k : H)‖ * ((1 / μ) * ‖embed f‖))^2 = sourceMuFactor μ k * (μ * ‖embed f‖^2) := by
    unfold sourceMuFactor
    field_simp
  rw [he] at hi2
  rw [actual_mixed_amplitude sharp m ell F _ hz]
  exact hi2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hμ.le) hc)

private theorem mixed_mu_cost (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g k : diagonal.domain) :
    mixedResponseCost sharp m ell F μ hμ g k ≤
      ENNReal.ofReal (sourceMuFactor μ k) * jointMuEnergy sharp m ell F μ hμ g := by
  have hc : 0 ≤ sourceMuFactor μ k := by unfold sourceMuFactor; positivity
  unfold mixedResponseCost jointMuEnergy
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal (sourceMuFactor μ k) * ENNReal.ofReal
        (μ * columnNorm (jointState sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [← ENNReal.ofReal_mul hc]
      exact ENNReal.ofReal_le_ofReal (amplitude_mu_bound sharp m ell F μ hμ g k w)
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Original Gamma consumes the complete Q8 current and radial source, without a graph or target-tail premise. -/
theorem actual_original_Q8_whole_current_budget (μ : ℝ) (hμ : 0 < μ) (g k : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index), ∀ sharp : Bool,
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g : H) (k : H)) ≤
          ENNReal.ofReal ε + ENNReal.ofReal (6 * sourceMuFactor μ k) * wholeCurrentBudget m ell F μ hμ g := by
  intro ε hε
  let κ := 3 * sourceMuFactor μ k
  have hκ : 0 ≤ κ := by dsimp [κ]; unfold sourceMuFactor; positivity
  let δ := ε / (2 * (κ + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N₀, h₀⟩ := actual_original_mixed_response_budget false μ hμ g k (ε / 2) (by positivity)
  obtain ⟨N₁, h₁⟩ := actual_original_mixed_response_budget true μ hμ g k (ε / 2) (by positivity)
  obtain ⟨N₂, h₂⟩ := actual_Q8_whole_mu_payment μ hμ g δ hδ
  refine ⟨max N₀ (max N₁ N₂), fun m hm ell hml => ?_⟩
  filter_upwards [h₀ m (by omega) ell hml, h₁ m (by omega) ell hml] with F hf ht
  intro sharp
  have hg : ENNReal.ofReal (closedJointCost sharp m ell F μ (g : H) (k : H)) ≤
      ENNReal.ofReal (ε / 2) + ENNReal.ofReal (3 : ℝ) * mixedResponseCost sharp m ell F μ hμ g k := by
    cases sharp <;> assumption
  have hc := mul_le_mul (le_refl (ENNReal.ofReal (3 : ℝ))) (mixed_mu_cost sharp m ell F μ hμ g k) zero_le zero_le
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)] at hc
  have hp : ENNReal.ofReal (ε / 2) + ENNReal.ofReal κ * ENNReal.ofReal δ ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul hκ, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hd : δ * (2 * (κ + 1)) = ε := by dsimp [δ]; field_simp
    nlinarith only [hd, hδ]
  have hfactor : ENNReal.ofReal κ * ENNReal.ofReal (2 : ℝ) = ENNReal.ofReal (6 * sourceMuFactor μ k) := by
    rw [← ENNReal.ofReal_mul hκ]
    congr 1
    dsimp [κ]
    ring
  calc
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal κ * jointMuEnergy sharp m ell F μ hμ g :=
      hg.trans (add_le_add le_rfl hc)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal κ * (ENNReal.ofReal δ +
        ENNReal.ofReal (2 : ℝ) * wholeCurrentBudget m ell F μ hμ g) :=
      add_le_add le_rfl (mul_le_mul le_rfl (h₂ m (by omega) ell hml F sharp) zero_le zero_le)
    _ = (ENNReal.ofReal (ε / 2) + ENNReal.ofReal κ * ENNReal.ofReal δ) +
        ENNReal.ofReal (6 * sourceMuFactor μ k) * wholeCurrentBudget m ell F μ hμ g := by
      rw [mul_add, ← mul_assoc, hfactor, add_assoc]
    _ ≤ _ := add_le_add hp le_rfl

end LowEnergy.SourceClockYukawaQ8WholeCurrentBudget
