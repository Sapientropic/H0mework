import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaRadialNativeAbsorption
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaRadialHessianBudget
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockYukawaRadialBoundaryBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialGammaNativeBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockYukawaRadialMixedCore SourceClockYukawaRadialMixedClock SourceClockYukawaRadialNativeAbsorption
open SourceClockYukawaRadialMixedBudget SourceFourPoleEnergyClosed
open SourceMixedNativeReturn SourceRelativePowerTail SourceRetardedForcingTail SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped Topology InnerProductSpace
attribute [local irreducible] state finiteResolvent mixedState mixedPrice
  SourceClockYukawaRadialMixedGamma.mixedResponse

private theorem actual_mixed_amplitude (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    mixedAmplitude sharp m ell F z g k=
      inner ℂ (k:H) (finiteResolvent F z (embed (mixedState sharp m ell F z hz g))) := by
  unfold mixedAmplitude mixedState
  have he : embed (coreEquiv.symm (radiusSource g))=(radiusSource g:H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [←he,actual_mixed_response_source sharp m ell F z hz]

private theorem reordered_square (a b c : ℝ) : (a*(b*c))^2=(b*a)^2*c^2 := by ring

def sourceMuFactor (μ : ℝ) (k : diagonal.domain) : ℝ := ((1/μ)*‖(k:H)‖)^2/μ

attribute [local irreducible] sourceMuFactor

private theorem amplitude_mu_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (w : ℝ) :
    ‖mixedAmplitude sharp m ell F (line μ w) g k‖^2 ≤
      sourceMuFactor μ k*(μ*‖embed (mixedState sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g)‖^2) := by
  let z := line μ w
  have hz : z.im≠0 := by simpa only [z,line_im] using hμ.ne'
  let f := mixedState sharp m ell F z hz g
  have hR : ‖finiteResolvent F z‖ ≤ 1/μ := by
    simpa only [z,line_im,abs_of_pos hμ] using finite_resolvent_norm F z hz
  have hret : ‖finiteResolvent F z (embed f)‖ ≤ (1/μ)*‖embed f‖ :=
    ((finiteResolvent F z).le_opNorm _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hi := (norm_inner_le_norm (𝕜 := ℂ) (k:H) (finiteResolvent F z (embed f))).trans
    (mul_le_mul_of_nonneg_left hret (norm_nonneg (k:H)))
  have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
  rw [reordered_square] at hi2
  rw [actual_mixed_amplitude sharp m ell F _ hz]
  change ‖inner ℂ (k:H) (finiteResolvent F z (embed f))‖^2 ≤ sourceMuFactor μ k*(μ*‖embed f‖^2)
  have he : sourceMuFactor μ k*(μ*‖embed f‖^2)=((1/μ)*‖(k:H)‖)^2*‖embed f‖^2 := by
    unfold sourceMuFactor
    field_simp [hμ.ne']
  rw [he]
  exact hi2

private theorem actual_mixed_mu_cost (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    mixedResponseCost sharp m ell F μ hμ g k ≤
      ENNReal.ofReal (sourceMuFactor μ k)*mixedNormEnergy sharp m ell F μ hμ g := by
  have hC : 0 ≤ sourceMuFactor μ k := by unfold sourceMuFactor;positivity
  unfold mixedResponseCost mixedNormEnergy
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (sourceMuFactor μ k)*ENNReal.ofReal
        (μ*‖embed (mixedState sharp m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (amplitude_mu_bound sharp m ell F μ hμ g k w)
    _=_ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Original Gamma consumes the reduced whole source price after all native, inverse-Hessian and fullX payments. -/
theorem actual_original_reduced_native_budget (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain)
    (η : ℝ) (hη : 0<η) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+ENNReal.ofReal (3*sourceMuFactor μ k)*
            SourceClockYukawaRadialHessianBudget.reducedBudget sharp m ell F μ hμ g η := by
  intro ε hε
  let κ := 3*sourceMuFactor μ k
  have hκ : 0≤κ := by dsimp only [κ];unfold sourceMuFactor;positivity
  let δ := ε/(2*(κ+1))
  have hδ : 0<δ := by dsimp only [δ];positivity
  obtain ⟨N₀,h₀⟩ := actual_original_mixed_response_budget false μ hμ g k (ε/2) (by positivity)
  obtain ⟨N₁,h₁⟩ := actual_original_mixed_response_budget true μ hμ g k (ε/2) (by positivity)
  obtain ⟨N₂,h₂⟩ := SourceClockYukawaRadialHessianBudget.actual_reduced_mu_remaining_budget μ hμ g η hη δ hδ
  refine ⟨max N₀ (max N₁ N₂),fun m hm ell hml => ?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml,h₂ m (by omega) ell hml] with F hf ht hR sharp
  have hcost : ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
      ENNReal.ofReal (ε/2)+ENNReal.ofReal (3:ℝ)*mixedResponseCost sharp m ell F μ hμ g k := by
    cases sharp <;> assumption
  have hM := actual_mixed_mu_cost sharp m ell F μ hμ g k
  have hpay : ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*ENNReal.ofReal δ ≤ ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul hκ,←ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hd : κ/(κ+1) ≤ 1 := (div_le_one (by positivity : 0<κ+1)).mpr (by linarith)
    have he : ε/2+κ*δ=ε/2+(ε/2)*(κ/(κ+1)) := by
      dsimp only [δ]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_left hd (by positivity : 0≤ε/2)]
  have htransport := mul_le_mul (le_refl (ENNReal.ofReal (3:ℝ))) hM bot_le bot_le
  rw [←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)] at htransport
  change ENNReal.ofReal (3:ℝ)*mixedResponseCost sharp m ell F μ hμ g k ≤
    ENNReal.ofReal κ*mixedNormEnergy sharp m ell F μ hμ g at htransport
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*mixedNormEnergy sharp m ell F μ hμ g :=
      hcost.trans (add_le_add (le_refl _) htransport)
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*(ENNReal.ofReal δ+
        SourceClockYukawaRadialHessianBudget.reducedBudget sharp m ell F μ hμ g η) :=
      add_le_add (le_refl _) (mul_le_mul (le_refl _) (hR sharp) bot_le bot_le)
    _=(ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*ENNReal.ofReal δ)+ENNReal.ofReal κ*
        SourceClockYukawaRadialHessianBudget.reducedBudget sharp m ell F μ hμ g η := by rw [mul_add,add_assoc]
    _ ≤ _ := add_le_add hpay (le_refl _)

/-- Original Gamma consumes the field source price after the actual joined radial boundary payment. -/
theorem actual_original_field_native_budget (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain)
    (η : ℝ) (hη : 0<η) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+ENNReal.ofReal (3*sourceMuFactor μ k)*
            SourceClockYukawaRadialBoundaryBudget.fieldBudget sharp m ell F μ hμ g η := by
  intro ε hε
  let κ := 3*sourceMuFactor μ k
  have hκ : 0≤κ := by dsimp only [κ];unfold sourceMuFactor;positivity
  let δ := ε/(2*(κ+1))
  have hδ : 0<δ := by dsimp only [δ];positivity
  obtain ⟨N₀,h₀⟩ := actual_original_mixed_response_budget false μ hμ g k (ε/2) (by positivity)
  obtain ⟨N₁,h₁⟩ := actual_original_mixed_response_budget true μ hμ g k (ε/2) (by positivity)
  obtain ⟨N₂,h₂⟩ := SourceClockYukawaRadialBoundaryBudget.actual_field_mu_remaining_budget μ hμ g η hη δ hδ
  refine ⟨max N₀ (max N₁ N₂),fun m hm ell hml => ?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml,h₂ m (by omega) ell hml] with F hf ht hR sharp
  have hcost : ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
      ENNReal.ofReal (ε/2)+ENNReal.ofReal (3:ℝ)*mixedResponseCost sharp m ell F μ hμ g k := by
    cases sharp <;> assumption
  have hM := actual_mixed_mu_cost sharp m ell F μ hμ g k
  have hpay : ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*ENNReal.ofReal δ ≤ ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul hκ,←ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hd : κ/(κ+1) ≤ 1 := (div_le_one (by positivity : 0<κ+1)).mpr (by linarith)
    have he : ε/2+κ*δ=ε/2+(ε/2)*(κ/(κ+1)) := by
      dsimp only [δ]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_left hd (by positivity : 0≤ε/2)]
  have htransport := mul_le_mul (le_refl (ENNReal.ofReal (3:ℝ))) hM bot_le bot_le
  rw [←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)] at htransport
  change ENNReal.ofReal (3:ℝ)*mixedResponseCost sharp m ell F μ hμ g k ≤
    ENNReal.ofReal κ*mixedNormEnergy sharp m ell F μ hμ g at htransport
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*mixedNormEnergy sharp m ell F μ hμ g :=
      hcost.trans (add_le_add (le_refl _) htransport)
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*(ENNReal.ofReal δ+
        SourceClockYukawaRadialBoundaryBudget.fieldBudget sharp m ell F μ hμ g η) :=
      add_le_add (le_refl _) (mul_le_mul (le_refl _) (hR sharp) bot_le bot_le)
    _=(ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*ENNReal.ofReal δ)+ENNReal.ofReal κ*
        SourceClockYukawaRadialBoundaryBudget.fieldBudget sharp m ell F μ hμ g η := by rw [mul_add,add_assoc]
    _ ≤ _ := add_le_add hpay (le_refl _)

end LowEnergy.SourceClockYukawaRadialGammaNativeBudget
