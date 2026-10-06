import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceScalarDoubleEndpoint
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceScalarForceBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarEndpointCost
open MeasureTheory Filter GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceScalarForceBudget
open SourceJointResidualEnergy SourceFourPoleEnergyClosed
open scoped InnerProductSpace

private theorem double_profile_return (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) :
    response F z (SourceScalarForceBudget.doubleResponse sharp m ell F g) (g : H) (k : H)=
      SourceScalarDoubleEndpoint.doubleResponse sharp m ell F g k z := rfl

private theorem norm_energy (f : ℝ → ℂ) (e : ℝ)
    (hi : Integrable (fun w : ℝ => ‖f w‖^2)) (he : (∫ w : ℝ, ‖f w‖^2)=e) :
    (∫⁻ w : ℝ, ENNReal.ofReal (‖f w‖^2))=ENNReal.ofReal e := by
  rw [←ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),he]

private theorem double_energy_return (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    (∫⁻ w : ℝ, ENNReal.ofReal
      (‖SourceScalarDoubleEndpoint.doubleResponse sharp m ell F g k (line μ w)‖^2))=
      ENNReal.ofReal (pairEnergy F μ (SourceScalarForceBudget.doubleResponse sharp m ell F g)
        (g : H) (k : H)) := by
  have he := norm_energy
    (fun w => response F (line μ w) (SourceScalarForceBudget.doubleResponse sharp m ell F g)
      (g : H) (k : H)) _
    (actual_response_integrable F μ hμ _ (g : H) (k : H))
    (actual_response_energy F μ hμ _ (g : H) (k : H))
  simpa only [double_profile_return] using! he

/-- The exact whole-channel endpoint Gram has its source-generated cofinal cutoff tail. -/
theorem actual_double_cost_tail (sharp : Bool) (g k : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        pairEnergy F μ (SourceScalarForceBudget.doubleResponse sharp m ell F g)
          (g : H) (k : H) ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := SourceScalarDoubleEndpoint.actual_double_tail sharp g k μ hμ ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp
    ((double_energy_return sharp m ell F g k μ hμ).symm.trans_le hF)

private def cutoffTail {I : Type*} (l : Filter I) (c : ℕ → ℕ → I → ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ᶠ F in l, c m ell F ≤ ε

private theorem paired_tail_iff {I : Type*} (l : Filter I) (a : ℝ) (ha : 0<a)
    (c b d : ℕ → ℕ → I → ℝ)
    (hf : ∀ m ell F, a^2*c m ell F ≤ 2*(b m ell F+d m ell F))
    (hr : ∀ m ell F, b m ell F ≤ 2*(a^2*c m ell F+d m ell F))
    (hd : cutoffTail l d) : cutoffTail l c ↔ cutoffTail l b := by
  have ha2 : 0<a^2 := sq_pos_of_ne_zero ha.ne'
  constructor
  · intro hc ε hε
    obtain ⟨N₁,h₁⟩ := hc (ε/(4*a^2)) (div_pos hε (by positivity))
    obtain ⟨N₂,h₂⟩ := hd (ε/4) (by positivity)
    refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
    filter_upwards [h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell,
      h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell] with F hF hD
    have hC := mul_le_mul_of_nonneg_left hF ha2.le
    have he : a^2*(ε/(4*a^2))=ε/4 := by field_simp [ha.ne']
    rw [he] at hC
    calc
      _ ≤ 2*(a^2*c m ell F+d m ell F) := hr m ell F
      _ ≤ 2*(ε/4+ε/4) := mul_le_mul_of_nonneg_left (add_le_add hC hD) (by norm_num)
      _ = ε := by ring
  · intro hb ε hε
    obtain ⟨N₁,h₁⟩ := hb (ε*a^2/4) (by positivity)
    obtain ⟨N₂,h₂⟩ := hd (ε*a^2/4) (by positivity)
    refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
    filter_upwards [h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell,
      h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell] with F hB hD
    have h := (hf m ell F).trans
      (mul_le_mul_of_nonneg_left (add_le_add hB hD) (by norm_num : (0 : ℝ) ≤ 2))
    have he : 2*(ε*a^2/4+ε*a^2/4)=a^2*ε := by ring
    rw [he] at h
    exact (mul_le_mul_iff_right₀ ha2).mp h

/-- Paying the literal double endpoints makes the source force tail exactly the original joint target. -/
theorem actual_joint_force_tail_iff (sharp : Bool) (g k : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    (∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index), closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε) ↔
    (∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        pairEnergy F μ (balancedForce sharp m ell F g) (g : H) (k : H) ≤ ε) := by
  have hm : 0<oscillatorMass :=
    mul_pos (by norm_num) (sq_pos_of_ne_zero GaussNativeEnergy.source_time_nonzero)
  exact paired_tail_iff (sourceFilter : Filter Index) oscillatorMass hm
    (fun m ell F => closedJointCost sharp m ell F μ (g : H) (k : H))
    (fun m ell F => pairEnergy F μ (balancedForce sharp m ell F g) (g : H) (k : H))
    (fun m ell F => pairEnergy F μ (SourceScalarForceBudget.doubleResponse sharp m ell F g) (g : H) (k : H))
    (fun m ell F => actual_force_energy_bound sharp m ell F μ hμ g k)
    (fun m ell F => actual_reverse_force_energy_bound sharp m ell F μ hμ g k)
    (actual_double_cost_tail sharp g k μ hμ)

end LowEnergy.SourceScalarEndpointCost
