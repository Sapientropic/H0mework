import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterSector
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCompositeBornMeasure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace LowEnergy.GeneralThreeParticleResponse
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussFockPair
open FullYDynamicSource FullYDynamicSourceRefinement FullYDynamicResponse FullYSourceResolventGraphSplice
open SourceClockYukawaCubicCurrent GaussCoreLabel GaussYukawaGrade GaussYukawaInteraction
open NativeHistoryGrade NamedColorQtNext GaussYukawaOperator CompositeFullYBorn
open SourceResolventBandLimit SourceResolventLorentzian SourceQuantumConfigurationHilbert
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace ENNReal
attribute [local irreducible] embed sourcePair GaussCoreLabel.project NativeHistoryGrade.projection
  literalCoreResolvent literalSharpResolvent

/-- A literal resolvent/Y word of an arbitrary actual core input. No named-mode
or wedge220 coordinates occur in this carrier. -/
def leg (F : Index) (z : ℂ) (hz : z.im ≠ 0) (q : QuantumTest) (j : ℕ) : QuantumTest :=
  ((literalStep F z hz)^j) (resolventCore F z hz q)

private theorem step_sector (F : Index) (n : Fin 505) (k : Fin 57) (hk : k.val+1 < 57)
    (z : ℂ) (hz : z.im ≠ 0) (q : QuantumTest) (hq : project (n,k) q = q) :
    project (n,⟨k.val+1,hk⟩) (literalStep F z hz q) = literalStep F z hz q := by
  have h := actual_resolvent_sector F (n,⟨k.val+1,hk⟩) z hz (originalAction q)
    (actual_Y_sector_successor n k hk q hq)
  simpa only [literalStep,LinearMap.neg_apply,Module.End.mul_apply,map_neg] using congrArg Neg.neg h

theorem leg_sector (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (hq : project (3,0) q = q) :
    ∀j : ℕ, ∀hj : j < 57, project (3,⟨j,hj⟩) (leg F z hz q j) = leg F z hz q j := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [leg,pow_zero,Module.End.one_apply]
    exact actual_resolvent_sector F (3,0) z hz q hq
  | succ j ih =>
    intro hj
    have h := step_sector F 3 ⟨j,by omega⟩ hj z hz (leg F z hz q j) (ih (by omega))
    simpa only [leg,pow_succ',Module.End.mul_apply] using h

theorem fourth_leg_zero (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (hq : project (3,0) q = q) : leg F z hz q 4 = 0 :=
  (leg_sector F z hz q hq 4 (by decide)).symm.trans (actual_empty_sector 3 4 (by decide) _)

private theorem long_leg_zero (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (hq : project (3,0) q = q) (j : ℕ) (hj : 4 ≤ j) : leg F z hz q j = 0 := by
  change ((literalStep F z hz)^j) (resolventCore F z hz q) = 0
  calc
    _ = ((literalStep F z hz)^(j-4) * (literalStep F z hz)^4) (resolventCore F z hz q) := by
      rw [←pow_add,Nat.sub_add_cancel hj]
    _ = ((literalStep F z hz)^(j-4)) (leg F z hz q 4) := rfl
    _ = 0 := by rw [fourth_leg_zero F z hz q hq,map_zero]

/-- Every actual Number-three grade-zero core has exactly the complete four
primal response words; the fourth Y insertion vanishes by its particle count. -/
theorem full_response (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (hq : project (3,0) q = q) :
    literalCoreResolvent F z hz q = ∑j : Fin 4, leg F z hz q j.val := by
  simp only [literalCoreResolvent,Module.End.mul_apply,LinearMap.sum_apply,leg]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((literalStep F z hz)^j) (resolventCore F z hz q)) 4]
  symm
  apply Finset.sum_subset (Finset.range_mono (by decide : 4 ≤ 57))
  intro j _ hj
  exact long_leg_zero F z hz q hq j (by simpa only [Finset.mem_range,not_lt] using hj)

/-- The independent sharp leg consumes the actual bottom-grade law. -/
theorem sharp_response (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (hq : project (3,0) q = q) :
    literalSharpResolvent F z hz q = resolventCore F z hz q := by
  apply actual_bottom_sharp_resolvent
  apply embed_injective
  rw [←grade_core,map_zero]
  have hp : NativeHistoryGrade.projection (3,0) (embed q) = embed q :=
    (embed_project (3,0) q).symm.trans (congrArg embed hq)
  have h := congrArg (fun A : H →L[ℂ] H => A (embed q)) (source_grade_right (3,0))
  simpa [mul_apply_eq_comp,hp] using h

private theorem cross_grade_zero (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (q r : QuantumTest) (hq : project (3,0) q = q) (hr : project (3,0) r = r)
    (i j : Fin 4) (hij : i ≠ j) :
    inner ℂ (embed (leg F z hz q i.val)) (embed (leg F z hz r j.val)) = 0 := by
  let li : Label := (3,⟨i.val,by omega⟩)
  let lj : Label := (3,⟨j.val,by omega⟩)
  have hi : projection li (embed (leg F z hz q i.val)) = embed (leg F z hz q i.val) :=
    (embed_project li _).symm.trans (congrArg embed (leg_sector F z hz q hq i.val (by omega)))
  have hj : projection lj (embed (leg F z hz r j.val)) = embed (leg F z hz r j.val) :=
    (embed_project lj _).symm.trans (congrArg embed (leg_sector F z hz r hr j.val (by omega)))
  have different : li ≠ lj := by
    intro h
    exact hij (Fin.ext (congrArg (fun l : Label => l.2.val) h))
  have hzproj := congrArg (fun T : H →L[ℂ] H => T (embed (leg F z hz r j.val)))
    (projection_product li lj)
  simp only [if_neg different,mul_apply_eq_comp,zero_apply,hj] at hzproj
  calc
    _ = inner ℂ (projection li (embed (leg F z hz q i.val))) (embed (leg F z hz r j.val)) := by rw [hi]
    _ = inner ℂ (embed (leg F z hz q i.val)) (projection li (embed (leg F z hz r j.val))) := projection_symmetric li _ _
    _ = 0 := by rw [hzproj,inner_zero_right]

/-- Complex coherence is retained within each actual output grade; only
cross-grade terms disappear by source projection orthogonality. -/
theorem full_response_gram (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (q r : QuantumTest) (hq : project (3,0) q = q) (hr : project (3,0) r = r) :
    inner ℂ (embed (literalCoreResolvent F z hz q)) (embed (literalCoreResolvent F z hz r)) =
      ∑j : Fin 4, inner ℂ (embed (leg F z hz q j.val)) (embed (leg F z hz r j.val)) := by
  rw [full_response F z hz q hq,full_response F z hz r hr,map_sum,map_sum,sum_inner]
  simp only [inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact cross_grade_zero F z hz q r hq hr i j (Ne.symm hji)
  · simp

theorem full_response_norm (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (q : QuantumTest) (hq : project (3,0) q = q) :
    ‖embed (literalCoreResolvent F z hz q)‖^2 = ∑j : Fin 4, ‖embed (leg F z hz q j.val)‖^2 := by
  have h := full_response_gram F z hz q q hq hq
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- Paid original full-Y frequency costs apply to the general core, with no
extra wedge realization or caller-supplied response budget. -/
theorem response_gram_integrable (F : Index) (q r : QuantumTest) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun ω : ℝ => inner ℂ (embed (literalResponse F sharp q advanced μ hμ ω))
      (embed (literalResponse F sharp r advanced μ hμ ω))) := by
  have hq := actual_response_square_integrable F sharp q advanced μ hμ
  have hr := actual_response_square_integrable F sharp r advanced μ hμ
  have cq := actual_response_continuous F sharp q advanced μ hμ
  have cr := actual_response_continuous F sharp r advanced μ hμ
  apply ((hq.add hr).div_const 2).mono' (cq.inner (𝕜 := ℂ) cr).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  have hb := norm_inner_le_norm (𝕜 := ℂ)
    (embed (literalResponse F sharp q advanced μ hμ ω)) (embed (literalResponse F sharp r advanced μ hμ ω))
  change ‖inner ℂ (embed (literalResponse F sharp q advanced μ hμ ω))
    (embed (literalResponse F sharp r advanced μ hμ ω))‖ ≤
      (‖embed (literalResponse F sharp q advanced μ hμ ω)‖^2 +
        ‖embed (literalResponse F sharp r advanced μ hμ ω)‖^2)/2
  nlinarith [sq_nonneg (‖embed (literalResponse F sharp q advanced μ hμ ω)‖ -
    ‖embed (literalResponse F sharp r advanced μ hμ ω)‖)]

/-- A common ordinary source event returns both full-H0+Y and independent
sharp pulses of two arbitrary core inputs before selecting cause or frequency. -/
theorem full_source_pulse_return (B : Index) (q r : QuantumTest) :
    ∃K₀ : Index, B ⊆ K₀ ∧ ∀K : Index, K₀ ⊆ K → ∀s : QuantumTest, s=q ∨ s=r →
      ∀sharp advanced : Bool, ∀μ : ℝ, ∀hμ : 0 < μ, ∀ω : ℝ,
      embed (literalResponse K sharp (fullSourcePulse sharp s advanced μ ω) advanced μ hμ ω) =
        (line (FullYPairedParseval.direction advanced * μ) ω)⁻¹ • embed s := by
  classical
  obtain ⟨Kq, hBq, hq⟩ := actual_full_source_forcing_return B q q
  obtain ⟨Kr, hBr, hr⟩ := actual_full_source_forcing_return B r r
  refine ⟨Kq ∪ Kr, fun x hx => Finset.mem_union.mpr (Or.inl (hBq hx)), ?_⟩
  intro K hK s hs sharp advanced μ hμ ω
  have hqK : Kq ⊆ K := fun x hx => hK (Finset.mem_union.mpr (Or.inl hx))
  have hrK : Kr ⊆ K := fun x hx => hK (Finset.mem_union.mpr (Or.inr hx))
  have h :
      literalCoreResolvent K (line (FullYPairedParseval.direction advanced * μ) ω)
        (causal_line_nonreal advanced μ ω hμ)
        ((GaussFullHamiltonian.fullAction - line (FullYPairedParseval.direction advanced * μ) ω •
          (1 : QuantumTest →ₗ[ℂ] QuantumTest)) s) = s ∧
      literalSharpResolvent K (line (FullYPairedParseval.direction advanced * μ) ω)
        (causal_line_nonreal advanced μ ω hμ)
        ((GaussFullHamiltonian.sharpAction - line (FullYPairedParseval.direction advanced * μ) ω •
          (1 : QuantumTest →ₗ[ℂ] QuantumTest)) s) = s := by
    obtain h | h := hs
    · subst s; exact hq K hqK _ _
    · subst s; exact hr K hrK _ _
  cases sharp
  · simp only [literalResponse,fullSourcePulse,Bool.false_eq_true,ite_false,map_smul,h.1]
  · simp only [literalResponse,fullSourcePulse,ite_true,map_smul,h.2]

def sourcePulseGram (F : Index) (q r : QuantumTest) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (ω : ℝ) : ℂ :=
  inner ℂ (embed (literalResponse F sharp (fullSourcePulse sharp q advanced μ ω) advanced μ hμ ω))
    (embed (literalResponse F sharp (fullSourcePulse sharp r advanced μ ω) advanced μ hμ ω))

def sourcePulseMeasure (F : Index) (q : QuantumTest) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) : Measure ℝ :=
  volume.withDensity (fun ω => ENNReal.ofReal
    (‖embed (literalResponse F sharp (fullSourcePulse sharp q advanced μ ω) advanced μ hμ ω)‖^2))

private theorem pulse_line_norm (advanced : Bool) (μ ω : ℝ) :
    ‖(line (FullYPairedParseval.direction advanced * μ) ω)⁻¹‖^2 = kernel μ 0 ω := by
  have h := inverse_norm_square (FullYPairedParseval.direction advanced * μ) 0 ω
  cases advanced <;> simpa only [FullYPairedParseval.direction, ite_true, Bool.false_eq_true,
    ite_false, one_mul, neg_one_mul, Complex.ofReal_zero, zero_sub, inv_neg, norm_neg,
    line, mul_comm Complex.I, kernel, neg_sq] using h

/-- Original frequency-dependent full-H0+Y forcing generates a common-event
complex spectral Gram and its positive diagonal measure on the general core.
The factor π/μ is the pulse's Lorentzian mass. -/
theorem actual_source_pulse_spectrum (B : Index) (q r : QuantumTest) :
    ∃K₀ : Index, B ⊆ K₀ ∧ ∀K : Index, K₀ ⊆ K →
      ∀sharp advanced : Bool, ∀μ : ℝ, ∀hμ : 0 < μ,
      (∀ω : ℝ, sourcePulseGram K q r sharp advanced μ hμ ω =
        (kernel μ 0 ω : ℂ) * inner ℂ (embed q) (embed r)) ∧
      Integrable (sourcePulseGram K q r sharp advanced μ hμ) ∧
      (∫ω : ℝ, sourcePulseGram K q r sharp advanced μ hμ ω) =
        (Real.pi / μ : ℂ) * inner ℂ (embed q) (embed r) ∧
      sourcePulseMeasure K q sharp advanced μ hμ =
        volume.withDensity (fun ω => ENNReal.ofReal (kernel μ 0 ω * ‖embed q‖^2)) ∧
      sourcePulseMeasure K q sharp advanced μ hμ Set.univ =
        ENNReal.ofReal ((Real.pi / μ) * ‖embed q‖^2) := by
  obtain ⟨K₀,hB,hR⟩ := full_source_pulse_return B q r
  refine ⟨K₀,hB,?_⟩
  intro K hK sharp advanced μ hμ
  have hq := hR K hK q (Or.inl rfl) sharp advanced μ hμ
  have hr := hR K hK r (Or.inr rfl) sharp advanced μ hμ
  have he (ω : ℝ) : sourcePulseGram K q r sharp advanced μ hμ ω =
      (kernel μ 0 ω : ℂ) * inner ℂ (embed q) (embed r) := by
    unfold sourcePulseGram
    rw [hq ω,hr ω]
    simp only [inner_smul_left,inner_smul_right]
    have scalar_norm (c : ℂ) : c * (starRingEnd ℂ) c = Complex.ofReal (‖c‖^2) :=
      (Complex.mul_conj c).trans (congrArg Complex.ofReal (Complex.normSq_eq_norm_sq c))
    rw [←mul_assoc,scalar_norm,pulse_line_norm]
  have hi : Integrable (sourcePulseGram K q r sharp advanced μ hμ) :=
    ((Complex.ofRealCLM.integrable_comp (kernel_integrable μ 0 hμ)).mul_const _).congr
      (Filter.Eventually.of_forall (fun ω => (he ω).symm))
  have hm : sourcePulseMeasure K q sharp advanced μ hμ =
      volume.withDensity (fun ω => ENNReal.ofReal (kernel μ 0 ω * ‖embed q‖^2)) := by
    unfold sourcePulseMeasure
    simp_rw [hq,norm_smul,mul_pow,pulse_line_norm]
  refine ⟨he,hi,?_,hm,?_⟩
  · rw [integral_congr_ae (Filter.Eventually.of_forall he),integral_mul_const]
    congr 1
    have hreal := Complex.ofRealCLM.integral_comp_comm (kernel_integrable μ 0 hμ)
    simp only [Complex.ofRealCLM_apply] at hreal
    rw [kernel_integral μ 0 hμ] at hreal
    simpa only [Complex.ofReal_div] using hreal
  · rw [hm,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    have hi := (kernel_integrable μ 0 hμ).mul_const (‖embed q‖^2)
    rw [←ofReal_integral_eq_lintegral_ofReal hi]
    · simp only [integral_mul_const,kernel_integral μ 0 hμ]
    · apply Filter.Eventually.of_forall
      intro ω
      unfold kernel
      positivity

end LowEnergy.GeneralThreeParticleResponse
