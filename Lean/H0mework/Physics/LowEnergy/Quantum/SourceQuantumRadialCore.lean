import H0mework.Physics.LowEnergy.Quantum.SourceQuantumFockGrade56
import Mathlib.Tactic

/-! The radial grade weights preserve the source compact smooth core.
The transported dual carries the inverse weight, so the original pairing returns. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceRadialCore
open SourceQuantumConfigurationHilbert MeasureTheory Set
open scoped ContDiff

def radius (z : Configuration) : ℝ := Real.sqrt (1 + ‖z.2.1‖ ^ 2 / 4)

theorem radius_pos (z : Configuration) : 0 < radius z := by
  unfold radius
  positivity

theorem radius_smooth : ContDiff ℝ ∞ radius := by
  apply ContDiff.sqrt
  · exact contDiff_const.add (((contDiff_fst.comp contDiff_snd).norm_sq ℝ).div_const 4)
  · intro z; positivity

def multiplier (k : ℕ) (z : Configuration) : ℂ := (radius z : ℂ) ^ k

theorem multiplier_ne_zero (k : ℕ) (z : Configuration) : multiplier k z ≠ 0 := by
  apply pow_ne_zero
  exact_mod_cast (radius_pos z).ne'

theorem multiplier_smooth (k : ℕ) : ContDiff ℝ ∞ (multiplier k) := by
  exact (Complex.ofRealCLM.contDiff.comp radius_smooth).pow k

theorem inverse_smooth (k : ℕ) : ContDiff ℝ ∞ (fun z => (multiplier k z)⁻¹) :=
  (multiplier_smooth k).inv (multiplier_ne_zero k)

theorem restricted_compact {g : Configuration → ℂ} (compact : HasCompactSupport g)
    (inside : tsupport g ⊆ (chart : Set Configuration)) :
    HasCompactSupport (fun z : chart => g z) := by
  have hk : IsCompact ((Subtype.val : chart → Configuration) ⁻¹' tsupport g) := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [image_preimage_eq_of_subset]
    · exact compact
    · intro x hx
      exact ⟨⟨x, inside hx⟩, rfl⟩
  apply hk.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro z hz
    exact subset_tsupport g hz
  · exact isClosed_closure.preimage continuous_subtype_val

theorem smooth_multiplier_preserves_test (w : Configuration → ℂ)
    (smooth : ContDiff ℝ ∞ w) (N : ℕ) (f : SectorHilbert N) (hf : f ∈ testDomain N) :
    ∃ h : SectorHilbert N, h ∈ testDomain N ∧
      h =ᵐ[numberMeasure N] (fun z : chart => w z * f z) := by
  rcases hf with ⟨g, hfg, hgk, hgc, hgs⟩
  have compact : HasCompactSupport (w * g) := hgk.mul_left
  have continuous := smooth.mul hgc
  have inside : tsupport (w * g) ⊆ (chart : Set Configuration) :=
    tsupport_mul_subset_right.trans hgs
  have mem : MemLp (fun z : chart => (w * g) z) 2 (numberMeasure N) :=
    (continuous.continuous.comp continuous_subtype_val).memLp_of_hasCompactSupport
      (restricted_compact compact inside)
  refine ⟨mem.toLp _, ⟨w * g, mem.coeFn_toLp, compact, continuous, inside⟩, ?_⟩
  filter_upwards [mem.coeFn_toLp, hfg] with z h₁ h₂
  simpa only [Pi.mul_apply, h₂] using h₁

theorem source_weight_preserves_test (k N : ℕ) (f : SectorHilbert N) (hf : f ∈ testDomain N) :
    ∃ h : SectorHilbert N, h ∈ testDomain N ∧
      h =ᵐ[numberMeasure N] (fun z : chart => multiplier k z * f z) :=
  smooth_multiplier_preserves_test _ (multiplier_smooth k) N f hf

theorem source_inverse_preserves_test (k N : ℕ) (f : SectorHilbert N) (hf : f ∈ testDomain N) :
    ∃ h : SectorHilbert N, h ∈ testDomain N ∧
      h =ᵐ[numberMeasure N] (fun z : chart => (multiplier k z)⁻¹ * f z) :=
  smooth_multiplier_preserves_test _ (inverse_smooth k) N f hf

def exponent (word : Occupation) : ℕ :=
  56 - (word.filter (fun i => i ∈ SourceQuantumFockGrade56.target)).card

def fullWeight (inverse : Bool) (word : Occupation) (z : Configuration) : ℂ :=
  if inverse then (multiplier (exponent word) z)⁻¹ else multiplier (exponent word) z

theorem fullWeight_smooth (inverse : Bool) (word : Occupation) :
    ContDiff ℝ ∞ (fullWeight inverse word) := by
  cases inverse
  · exact multiplier_smooth _
  · exact inverse_smooth _

theorem original_full_core_preserved (inverse : Bool) (f : FockHilbert)
    (hf : f ∈ fockTestDomain) :
    ∃ h : FockHilbert, h ∈ fockTestDomain ∧ ∀ word,
      h word =ᵐ[numberMeasure word.card]
        (fun z : chart => fullWeight inverse word z * f word z) := by
  have all (word : Occupation) := smooth_multiplier_preserves_test
    (fullWeight inverse word) (fullWeight_smooth inverse word) word.card (f word) (hf word)
  choose h hc ha using all
  exact ⟨WithLp.toLp 2 h, hc, ha⟩

theorem pairing_return (k : ℕ) (z : Configuration) (psi phi : ℂ) :
    star (multiplier k z * psi) * ((multiplier k z)⁻¹ * phi) = star psi * phi := by
  have hn := multiplier_ne_zero k z
  have hs : star (multiplier k z) = multiplier k z := by
    simp only [multiplier, star_pow, Complex.star_def, Complex.conj_ofReal]
  rw [star_mul, hs]
  field_simp

#print axioms source_weight_preserves_test
#print axioms source_inverse_preserves_test
#print axioms original_full_core_preserved
#print axioms pairing_return
end LowEnergy.SourceRadialCore
