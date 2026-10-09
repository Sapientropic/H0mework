import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleCutoffFamily
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCutoffBandMap
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualThreeParticleCutoffFamily
open GaussCoreHilbert GaussCoreDifferential GaussUnitaryHistory GaussCoreLabel
open ActualThreeParticleCutoffGram ActualCutoffFrequencyBase ActualCutoffBandMap
open SourceFamilyHilbert FullYSourceFiniteTimeIntegral
open FullYSourceResolventGraphSplice MeasureTheory Filter Set
open scoped Topology InnerProductSpace
private abbrev L2H := Lp H 2 (volume : Measure ℝ)

private theorem band_read_bound (B : Set ℝ) (advanced : Bool) (t : ℝ) (_F : Index) (f : L2H) :
    ‖ActualCutoffBandMap.read B advanced t f‖ ≤ 1*‖f‖ := by
  simpa only [one_mul] using actual_read_bound B advanced t f

def bandFamily (B : Set ℝ) (advanced : Bool) (t : ℝ) (n : ℕ) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) :
    Family (Lp H 2 ((volume : Measure ℝ).restrict B)) sourceFilter :=
  FullYSourceFamilyLinearMap.act sourceFilter (fun _ => ActualCutoffBandMap.read B advanced t)
    1 zero_le_one (band_read_bound B advanced t) (responseFamily n advanced μ hμ q hq)

def bandTime (B : Set ℝ) (advanced : Bool) (t : ℝ) (n : ℕ) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) : TimeSpace ((volume : Measure ℝ).restrict B) :=
  (bandFamily B advanced t n μ hμ q hq : TimeSpace ((volume : Measure ℝ).restrict B))

def bandLift (B : Set ℝ) (advanced : Bool) (t : ℝ) :
    TimeSpace (volume : Measure ℝ) →L[ℂ] TimeSpace ((volume : Measure ℝ).restrict B) :=
  FullYSourceFamilyLinearMap.lift sourceFilter (fun _ => ActualCutoffBandMap.read B advanced t)
    1 zero_le_one (band_read_bound B advanced t)

theorem actual_band_time_return (B : Set ℝ) (advanced : Bool) (t : ℝ)
    (n : ℕ) (μ : ℝ) (hμ : 0 < μ) (q : QuantumTest) (hq : project (3,0) q = q) :
    bandLift B advanced t (sourceFrequency n advanced μ hμ q hq) = bandTime B advanced t n μ hμ q hq :=
  FullYSourceFamilyLinearMap.lift_coe sourceFilter _ _ _ _ _

theorem actual_band_time_bound (B : Set ℝ) (advanced : Bool) (t : ℝ)
    (n : ℕ) (μ : ℝ) (hμ : 0 < μ) (q : QuantumTest) (hq : project (3,0) q = q) :
    ‖bandTime B advanced t n μ hμ q hq‖ ≤ ‖sourceFrequency n advanced μ hμ q hq‖ := by
  calc
    _ = ‖bandLift B advanced t (sourceFrequency n advanced μ hμ q hq)‖ :=
      congrArg norm (actual_band_time_return B advanced t n μ hμ q hq).symm
    _ ≤ 1*‖sourceFrequency n advanced μ hμ q hq‖ :=
      FullYSourceFamilyLinearMap.lift_bound sourceFilter _ 1 zero_le_one
        (band_read_bound B advanced t) _
    _ = _ := one_mul _

theorem actual_band_family_value (B : Set ℝ) (advanced : Bool) (t : ℝ)
    (n : ℕ) (μ : ℝ) (hμ : 0 < μ) (q : QuantumTest) (hq : project (3,0) q = q) (F : Index) :
    value (bandFamily B advanced t n μ hμ q hq) F =
      ActualCutoffBandMap.read B advanced t (value (responseFamily n advanced μ hμ q hq) F) := rfl

theorem actual_band_response_read (B : Set ℝ) (advanced : Bool) (t : ℝ)
    (n : ℕ) (μ : ℝ) (hμ : 0 < μ) (q : QuantumTest) (hq : project (3,0) q = q) (F : Index) :
    (fun w : ℝ => value (bandFamily B advanced t n μ hμ q hq) F w) =ᵐ[(volume : Measure ℝ).restrict B]
      (fun w => phase advanced t w • inverse F n (frequency advanced μ w) (embed q)) := by
  have hv := (actual_band_family_value B advanced t n μ hμ q hq F).trans
    (congrArg (ActualCutoffBandMap.read B advanced t)
      (actual_response_family_value n advanced μ hμ q hq F))
  have hh : (fun w : ℝ => value (bandFamily B advanced t n μ hμ q hq) F w) =ᵐ[(volume : Measure ℝ).restrict B]
      (fun w => ActualCutoffBandMap.read B advanced t (finiteResponse F n advanced μ hμ q hq) w) :=
    Eventually.of_forall (fun w => congrArg
      (fun f : Lp H 2 ((volume : Measure ℝ).restrict B) => f w) hv)
  exact hh.trans
    ((actual_read_point B advanced t (finiteResponse F n advanced μ hμ q hq)).trans
      ((ae_restrict_of_ae (actual_finite_response_read F n advanced μ hμ q hq)).mono
        (fun w hw => congrArg (fun v : H => phase advanced t w • v) hw)))

private theorem zero_integral_return {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (ν : Measure ℝ) [IsFiniteMeasure ν]
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (f : Lp E 2 ν) :
    retardedIntegral ν C hC (fun _ : ℝ => 0) measurable_const f = ∫w : ℝ,f w ∂ν := by
  rw [integral_return]
  simp only [neg_zero,SourceFiniteUnitary.time_zero,one_apply_eq_self]

/-- The finite band supplies the actual finite measure required by sourceIntegral.
The original Fourier character remains inside every finite-F Bochner integral. -/
def bandKernel (B : Set ℝ) (hB : (volume : Measure ℝ) B ≠ ⊤) (advanced : Bool) (t : ℝ)
    (n : ℕ) (μ : ℝ) (hμ : 0 < μ) (q : QuantumTest) (hq : project (3,0) q = q) : HistorySpace :=
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict B) := isFiniteMeasure_restrict.mpr hB
  sourceIntegral ((volume : Measure ℝ).restrict B) (fun _ : ℝ => 0) measurable_const
    (bandTime B advanced t n μ hμ q hq)

def bandKernelFamily (B : Set ℝ) (hB : (volume : Measure ℝ) B ≠ ⊤) (advanced : Bool) (t : ℝ)
    (n : ℕ) (μ : ℝ) (hμ : 0 < μ) (q : QuantumTest) (hq : project (3,0) q = q) : Family H sourceFilter :=
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict B) := isFiniteMeasure_restrict.mpr hB
  FullYSourceFamilyLinearMap.act sourceFilter
    (fun F => retardedIntegral ((volume : Measure ℝ).restrict B) (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) (fun _ : ℝ => 0) measurable_const)
    (Real.sqrt (((volume : Measure ℝ).restrict B) univ).toReal) (Real.sqrt_nonneg _)
    (fun F => integral_bound ((volume : Measure ℝ).restrict B) (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) (fun _ : ℝ => 0) measurable_const)
    (bandFamily B advanced t n μ hμ q hq)

theorem actual_band_kernel_return (B : Set ℝ) (hB : (volume : Measure ℝ) B ≠ ⊤)
    (advanced : Bool) (t : ℝ) (n : ℕ) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) :
    bandKernel B hB advanced t n μ hμ q hq = (bandKernelFamily B hB advanced t n μ hμ q hq : HistorySpace) := by
  let _ : IsFiniteMeasure ((volume : Measure ℝ).restrict B) := isFiniteMeasure_restrict.mpr hB
  exact FullYSourceFamilyLinearMap.lift_coe sourceFilter _ _ _ _ _

theorem actual_band_kernel_family_value (B : Set ℝ) (hB : (volume : Measure ℝ) B ≠ ⊤)
    (advanced : Bool) (t : ℝ) (n : ℕ) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) (F : Index) :
    value (bandKernelFamily B hB advanced t n μ hμ q hq) F =
      ∫w : ℝ in B,phase advanced t w • inverse F n (frequency advanced μ w) (embed q) := by
  let _ : IsFiniteMeasure ((volume : Measure ℝ).restrict B) := isFiniteMeasure_restrict.mpr hB
  change retardedIntegral ((volume : Measure ℝ).restrict B) (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) (fun _ : ℝ => 0) measurable_const
    (value (bandFamily B advanced t n μ hμ q hq) F) = _
  exact (zero_integral_return _ _ _ _).trans
    (integral_congr_ae (actual_band_response_read B advanced t n μ hμ q hq F))

theorem actual_band_kernel_bound (B : Set ℝ) (hB : (volume : Measure ℝ) B ≠ ⊤)
    (advanced : Bool) (t : ℝ) (n : ℕ) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) :
    ‖bandKernel B hB advanced t n μ hμ q hq‖ ≤
      Real.sqrt (((volume : Measure ℝ).restrict B) univ).toReal*‖sourceFrequency n advanced μ hμ q hq‖ := by
  let _ : IsFiniteMeasure ((volume : Measure ℝ).restrict B) := isFiniteMeasure_restrict.mpr hB
  exact (source_integral_bound ((volume : Measure ℝ).restrict B) (fun _ : ℝ => 0) measurable_const _).trans
    (mul_le_mul_of_nonneg_left (actual_band_time_bound B advanced t n μ hμ q hq) (Real.sqrt_nonneg _))

theorem actual_band_kernel_energy_limit (B : Set ℝ) (hB : (volume : Measure ℝ) B ≠ ⊤)
    (advanced : Bool) (t : ℝ) (n : ℕ) (μ : ℝ) (hμ : 0 < μ)
    (q : QuantumTest) (hq : project (3,0) q = q) :
    Tendsto (fun F : Index => ‖∫w : ℝ in B,
      phase advanced t w • inverse F n (frequency advanced μ w) (embed q)‖^2)
      sourceFilter (𝓝 (‖bandKernel B hB advanced t n μ hμ q hq‖^2)) := by
  have h := (square_tendsto sourceFilter (bandKernelFamily B hB advanced t n μ hμ q hq)).congr'
    (Eventually.of_forall (fun F => congrArg (fun v : H => ‖v‖^2)
      (actual_band_kernel_family_value B hB advanced t n μ hμ q hq F)))
  have hn : ‖bandKernel B hB advanced t n μ hμ q hq‖ = ‖bandKernelFamily B hB advanced t n μ hμ q hq‖ :=
    (congrArg norm (actual_band_kernel_return B hB advanced t n μ hμ q hq)).trans
      (UniformSpace.Completion.norm_coe _)
  simpa only [hn] using h

end LowEnergy.ActualThreeParticleCutoffFamily
