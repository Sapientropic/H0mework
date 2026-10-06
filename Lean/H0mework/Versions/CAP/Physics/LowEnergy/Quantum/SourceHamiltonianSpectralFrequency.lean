import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceHamiltonianSpectralEnergy
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceHamiltonianSpectralFrequency
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceHamiltonianSpectralEnergy SourceResolventLorentzian SourceResolventBandLimit
open SourceActualResolventEnergy FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped Topology InnerProductSpace

/-- The scalar energy of the same positive source measure on the original frequency line. -/
def profile (ν : Measure ℝ) (μ w : ℝ) : ℝ := ∫ a : ℝ,kernel μ a w ∂ν

private theorem kernel_nonnegative (μ a w : ℝ) : 0 ≤ kernel μ a w := by unfold kernel;positivity

private theorem kernel_product_integrable (ν : Measure ℝ) [IsFiniteMeasure ν] (μ : ℝ) (hμ : 0<μ) :
    Integrable (fun p : ℝ × ℝ => kernel μ p.1 p.2) (ν.prod volume) := by
  have hc : Continuous (fun p : ℝ × ℝ => kernel μ p.1 p.2) := by
    unfold kernel
    exact Continuous.inv₀ (by fun_prop) (fun p => by positivity)
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun a => kernel_integrable μ a hμ),?_⟩
  have he : (fun a : ℝ => ∫ w : ℝ,‖kernel μ a w‖)=(fun _ => Real.pi/μ) := by
    funext a
    simp only [Real.norm_eq_abs,abs_of_nonneg (kernel_nonnegative μ a _),kernel_integral μ a hμ]
  rw [he]
  exact integrable_const _

/-- Fubini returns the complete frequency mass of the generated spectral profile. -/
theorem spectral_frequency_mass (ν : Measure ℝ) [IsFiniteMeasure ν] (μ : ℝ) (hμ : 0<μ) :
    Integrable (profile ν μ) ∧ (∫ w : ℝ,profile ν μ w)=Real.pi/μ*ν.real Set.univ := by
  have hi := kernel_product_integrable ν μ hμ
  refine ⟨hi.integral_prod_right,?_⟩
  unfold profile
  rw [←integral_integral_swap hi]
  simp only [kernel_integral μ _ hμ,integral_const,smul_eq_mul]
  ring

/-- Finite-band uniform control and equal total mass yield L1 convergence for an arbitrary filter. -/
private theorem nonnegative_frequency_L1 {ι : Type*} (l : Filter ι) [NeBot l]
    (f : ι → ℝ → ℝ) (p : ℝ → ℝ) (L : NNReal)
    (hf : ∀ i,LipschitzWith L (f i)) (hp : ∀ w,Tendsto (fun i => f i w) l (𝓝 (p w)))
    (hfi : ∀ i,Integrable (f i)) (hpi : Integrable p)
    (hfn : ∀ i w,0 ≤ f i w) (hpn : ∀ w,0 ≤ p w)
    (hm : ∀ i,(∫ w,f i w)=∫ w,p w) :
    Tendsto (fun i => ∫ w : ℝ,|f i w-p w|) l (𝓝 0) := by
  have hpl : LipschitzWith L p := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hp x).dist (hp y)) (Eventually.of_forall (fun i => (hf i).dist_le_mul x y))
  let m := fun i w => min (f i w) (p w)
  have hml (i : ι) : LipschitzWith L (m i) := by simpa only [max_self] using (hf i).min hpl
  have hmi (i : ι) : Integrable (m i) := (hfi i).inf hpi
  have hmn (i : ι) (w : ℝ) : 0 ≤ m i w := le_min (hfn i w) (hpn w)
  have hmp (w : ℝ) : Tendsto (fun i => m i w) l (𝓝 (p w)) := by
    simpa only [min_self] using (hp w).min (tendsto_const_nhds : Tendsto (fun _ : ι => p w) l (𝓝 (p w)))
  have hband : Tendsto (fun R : ℝ => ∫ w in -R..R,p w) atTop (𝓝 (∫ w,p w)) :=
    intervalIntegral_tendsto_integral hpi tendsto_neg_atTop_atBot tendsto_id
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R,hR,hmass⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((tendsto_order.mp hband).1 ((∫ w,p w)-ε/4) (by linarith))).exists
  have hlim := band_integral_limit l m p L hml hmp (-R) R
  filter_upwards [(tendsto_order.mp hlim).1 ((∫ w in -R..R,p w)-ε/4) (by linarith)] with i hi
  have hle : (∫ w in -R..R,m i w) ≤ ∫ w,m i w := by
    rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
    exact integral_mono_measure Measure.restrict_le_self (Eventually.of_forall (hmn i)) (hmi i)
  have he : (∫ w : ℝ,|f i w-p w|)=2*(∫ w,p w)-2*(∫ w,m i w) := by
    have habs : (fun w : ℝ => |f i w-p w|)=(fun w => f i w+p w-2*m i w) := by
      funext w
      rcases le_total (f i w) (p w) with h | h
      · simp only [m,min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · simp only [m,min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]
        ring
    have hs := integral_sub ((hfi i).add hpi) ((hmi i).const_mul 2)
    simp only [Pi.add_apply] at hs
    rw [habs,hs,integral_add (hfi i) hpi,integral_const_mul,hm]
    ring
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun w => abs_nonneg _)),he]
  linarith

/-- The original source response converges on the entire frequency axis, with no frequency mass lost. -/
theorem actual_source_frequency_measure (g : diagonal.domain) :
    ∃ ν : Measure ℝ,IsFiniteMeasure ν ∧ ν Set.univ=ENNReal.ofReal (‖(g : H)‖^2) ∧
      ∀ (μ : ℝ),0<μ →
        Integrable (profile ν μ) ∧ (∫ w : ℝ,profile ν μ w)=Real.pi/μ*‖(g : H)‖^2 ∧
        Tendsto (fun F => ∫ w : ℝ,|‖finiteResolvent F (line μ w) (g : H)‖^2-profile ν μ w|)
          (sourceFilter : Filter Index) (𝓝 0) := by
  obtain ⟨ν,hfinite,hm,hν⟩ := actual_source_energy_measure g
  let := hfinite
  refine ⟨ν,hfinite,hm,fun μ hμ => ?_⟩
  obtain ⟨hpi,hpm⟩ := spectral_frequency_mass ν μ hμ
  have hmass : ν.real Set.univ=‖(g : H)‖^2 := by rw [Measure.real,hm,ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [hmass] at hpm
  refine ⟨hpi,hpm,?_⟩
  let f := fun (F : Index) (w : ℝ) => ‖finiteResolvent F (line μ w) (g : H)‖^2
  let L : NNReal := ⟨2*μ⁻¹*(μ⁻¹*μ⁻¹)*‖(g : H)‖^2,by positivity⟩
  have hfl (F : Index) : LipschitzWith L (f F) :=
    word_square_lipschitz (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) μ hμ [] (g : H)
  have hpoint (w : ℝ) : Tendsto (fun F => f F w) (sourceFilter : Filter Index) (𝓝 (profile ν μ w)) := by
    have h := (hν (line μ w) (by simpa only [line_im] using hμ.ne')).2
    have he (a : ℝ) : ‖((a : ℂ)-line μ w)⁻¹‖^2=kernel μ a w := by
      simpa only [line,mul_comm (μ : ℂ) Complex.I] using inverse_norm_square μ a w
    simpa only [f,profile,he] using! h
  have hfi (F : Index) : Integrable (f F) := by
    simpa only [f,line,mul_comm (μ : ℂ) Complex.I] using actual_square_integrable F μ hμ (g : H)
  have hfm (F : Index) : (∫ w,f F w)=∫ w,profile ν μ w := by
    rw [hpm]
    simpa only [f,line,mul_comm (μ : ℂ) Complex.I] using actual_square_integral F μ hμ (g : H)
  exact nonnegative_frequency_L1 (sourceFilter : Filter Index) f (profile ν μ) L hfl hpoint hfi hpi
    (fun _ _ => sq_nonneg _) (fun w => integral_nonneg (kernel_nonnegative μ · w)) hfm

end LowEnergy.SourceHamiltonianSpectralFrequency
