import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCutoffFrequencyBase
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCausalFourierSource
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceFamilyLinearMap
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualCutoffBandMap
open MeasureTheory Filter Set
open scoped Topology

/-- The angular-frequency character from the original oriented causal Fourier convention. -/
def phase (advanced : Bool) (t w : ℝ) : ℂ :=
  (Real.fourierChar (-FullYPairedParseval.direction advanced*w*t/(2*Real.pi)) : ℂ)

theorem actual_phase_continuous (advanced : Bool) (t : ℝ) : Continuous (phase advanced t) := by
  unfold phase
  fun_prop

theorem actual_phase_norm (advanced : Bool) (t w : ℝ) : ‖phase advanced t w‖ = 1 :=
  Circle.norm_coe _

theorem actual_phase_zero (advanced : Bool) (w : ℝ) : phase advanced 0 w = 1 := by
  simp [phase]

theorem actual_source_frequency_normalization (advanced : Bool) (μ w : ℝ) :
    ActualCutoffFrequencyBase.frequency advanced μ w =
      FullYPairedParseval.sourceLine advanced μ (-FullYPairedParseval.direction advanced*w/(2*Real.pi)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  cases advanced <;>
    simp only [ActualCutoffFrequencyBase.frequency,FullYPairedParseval.sourceLine,
      FullYPairedParseval.direction,ite_true,ite_false,Bool.false_eq_true,SourceResolventBandLimit.line]
  all_goals
    push_cast
    field_simp
    all_goals ring

section Read
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem readMemLp (B : Set ℝ) (advanced : Bool) (t : ℝ) (f : Lp E 2 (volume : Measure ℝ)) :
    MemLp (fun w : ℝ => phase advanced t w • f w) 2 ((volume : Measure ℝ).restrict B) :=
  ((Lp.memLp f).restrict B).of_le_mul
    ((actual_phase_continuous advanced t).aestronglyMeasurable.smul
      ((Lp.aestronglyMeasurable f).restrict))
    (Eventually.of_forall (fun w => by rw [norm_smul,actual_phase_norm,one_mul]))

def readLp (B : Set ℝ) (advanced : Bool) (t : ℝ) (f : Lp E 2 (volume : Measure ℝ)) :
    Lp E 2 ((volume : Measure ℝ).restrict B) :=
  (readMemLp B advanced t f).toLp (fun w => phase advanced t w • f w)

theorem actual_read_ae (B : Set ℝ) (advanced : Bool) (t : ℝ) (f : Lp E 2 (volume : Measure ℝ)) :
    (fun w : ℝ => readLp B advanced t f w) =ᵐ[(volume : Measure ℝ).restrict B]
      (fun w => phase advanced t w • f w) :=
  (readMemLp B advanced t f).coeFn_toLp

def readLinear (B : Set ℝ) (advanced : Bool) (t : ℝ) :
    Lp E 2 (volume : Measure ℝ) →ₗ[ℂ] Lp E 2 ((volume : Measure ℝ).restrict B) where
  toFun := readLp B advanced t
  map_add' f g := by
    apply Lp.ext
    filter_upwards [actual_read_ae B advanced t (f+g),actual_read_ae B advanced t f,
      actual_read_ae B advanced t g,ae_restrict_of_ae (Lp.coeFn_add f g),
      Lp.coeFn_add (readLp B advanced t f) (readLp B advanced t g)] with w hfg hf hg hadd hr
    change readLp B advanced t (f+g) w = (readLp B advanced t f + readLp B advanced t g) w
    rw [hfg,hr,hadd]
    simp only [Pi.add_apply]
    rw [hf,hg]
    exact smul_add _ _ _
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [actual_read_ae B advanced t (c • f),actual_read_ae B advanced t f,
      ae_restrict_of_ae (Lp.coeFn_smul c f),Lp.coeFn_smul c (readLp B advanced t f)] with w hcf hf hs hr
    change readLp B advanced t (c • f) w = (c • readLp B advanced t f) w
    rw [hcf,hr,hs]
    simp only [Pi.smul_apply]
    rw [hf]
    exact smul_comm _ _ _

theorem actual_read_norm (B : Set ℝ) (advanced : Bool) (t : ℝ) (f : Lp E 2 (volume : Measure ℝ)) :
    ‖readLp B advanced t f‖ ≤ ‖f‖ := by
  simp only [Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
  rw [eLpNorm_congr_ae (actual_read_ae B advanced t f)]
  calc
    _ = eLpNorm f 2 ((volume : Measure ℝ).restrict B) :=
      eLpNorm_congr_norm_ae (Eventually.of_forall (fun w => by rw [norm_smul,actual_phase_norm,one_mul]))
    _ ≤ eLpNorm f 2 (volume : Measure ℝ) := eLpNorm_mono_measure _ Measure.restrict_le_self

/-- Restriction and the source Fourier character form one complex-linear contraction;
finite measure is required only by the downstream actual integral consumer. -/
def read (B : Set ℝ) (advanced : Bool) (t : ℝ) :
    Lp E 2 (volume : Measure ℝ) →L[ℂ] Lp E 2 ((volume : Measure ℝ).restrict B) :=
  (readLinear B advanced t).mkContinuous 1 (fun f => by
    change ‖readLp B advanced t f‖ ≤ 1*‖f‖
    simpa only [one_mul] using actual_read_norm B advanced t f)

theorem actual_read_bound (B : Set ℝ) (advanced : Bool) (t : ℝ) (f : Lp E 2 (volume : Measure ℝ)) :
    ‖read B advanced t f‖ ≤ ‖f‖ := actual_read_norm B advanced t f

theorem actual_read_point (B : Set ℝ) (advanced : Bool) (t : ℝ) (f : Lp E 2 (volume : Measure ℝ)) :
    (fun w : ℝ => read B advanced t f w) =ᵐ[(volume : Measure ℝ).restrict B]
      (fun w => phase advanced t w • f w) := actual_read_ae B advanced t f

end Read
end LowEnergy.ActualCutoffBandMap
