import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.Kernel
import H0mework.Versions.X.NavierStokes.SourceWindow.PairingReadout
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.Holder

set_option autoImplicit false
open scoped Topology ENNReal NNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeIsometry
open Set Filter MeasureTheory
open NativeForwardWindowPairingReadout (density density_measurable averageMeasure)
open NativeWindowKernelHalfDensity (rootKernel)
noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Lag := Lp E 2 averageMeasure
abbrev Absolute := Lp E 2 (volume : Measure ℝ)

theorem weighted_ae {f g : ℝ → E} (same : f=ᵐ[averageMeasure] g) :
    (fun x => rootKernel x • f x)=ᵐ[volume] fun x => rootKernel x • g x := by
  have actual:∀ᵐ x ∂(volume : Measure ℝ),(density x : ℝ≥0∞)≠0 → f x=g x :=
    (ae_withDensity_iff density_measurable.coe_nnreal_ennreal).mp same
  filter_upwards [actual] with x equal
  by_cases zero:rootKernel x=0
  · simp only [zero,zero_smul]
  · have positive : (density x : ℝ≥0∞)≠0 := by
      apply ENNReal.coe_ne_zero.mpr
      intro equality
      have scalar : NativeForwardWindowSource.kernel x=0 := congrArg (fun z : ℝ≥0 => (z : ℝ)) equality
      exact zero (sq_eq_zero_iff.mp ((NativeWindowKernelHalfDensity.square x).trans scalar))
    rw [equal positive]

theorem root_cancel (x : ℝ) (v : E) :
    (rootKernel x)⁻¹ • (NativeForwardWindowSource.kernel x • v)=rootKernel x • v := by
  rw [← NativeWindowKernelHalfDensity.square,smul_smul]
  by_cases zero:rootKernel x=0
  · simp [zero]
  · congr 1
    field_simp

theorem weighted_measurable (v : Lag E) : AEStronglyMeasurable (fun x => rootKernel x • v x) volume := by
  have original:=aestronglyMeasurable_withDensity_iff density_measurable |>.mp (Lp.memLp v).aestronglyMeasurable
  have lifted: AEStronglyMeasurable (fun x => (rootKernel x)⁻¹ • (NativeForwardWindowSource.kernel x • v x)) volume :=
    NativeWindowKernelHalfDensity.continuous.measurable.inv.aestronglyMeasurable.smul original
  simpa only [root_cancel] using lifted

theorem norm_square_row (x : ℝ) (v : E) :
    ‖rootKernel x • v‖^2=NativeForwardWindowSource.kernel x*‖v‖^2 := by
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,NativeWindowKernelHalfDensity.square]

theorem weighted_memLp (v : Lag E) : MemLp (fun x => rootKernel x • v x) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (weighted_measurable E v)).mpr
  have original := (Lp.memLp v).integrable_norm_pow (by norm_num : (2 : ℕ)≠0)
  have weighted := (integrable_withDensity_iff_integrable_smul density_measurable).mp original
  exact weighted.congr (Eventually.of_forall fun x => by
    change density x • ‖v x‖^2=‖rootKernel x • v x‖^2
    rw [norm_square_row]
    rfl)

def half (v : Lag E) : Absolute E := (weighted_memLp E v).toLp (fun x => rootKernel x • v x)

theorem half_ae (v : Lag E) : half E v=ᵐ[volume] fun x => rootKernel x • v x :=
  (weighted_memLp E v).coeFn_toLp

theorem norm_square {μ : Measure ℝ} (v : Lp E 2 μ) : ‖v‖^2=∫ x,‖v x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem half_norm (v : Lag E) : ‖half E v‖=‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_square,norm_square,NativeForwardWindowPairingReadout.density_integral]
  apply integral_congr_ae
  filter_upwards [half_ae E v] with x actual
  rw [actual,norm_square_row]
  rfl

def halfIsometry : Lag E →ₗᵢ[ℝ] Absolute E where
  toFun := half E
  map_add' u v := by
    apply Lp.ext
    filter_upwards [half_ae E (u+v),half_ae E u,half_ae E v,
      Lp.coeFn_add (half E u) (half E v),weighted_ae E (Lp.coeFn_add u v)] with x total first last addition same
    rw [total,addition,Pi.add_apply,first,last]
    exact (same.trans (smul_add _ _ _))
  map_smul' r u := by
    apply Lp.ext
    filter_upwards [half_ae E (r • u),half_ae E u,Lp.coeFn_smul r (half E u),
      weighted_ae E (Lp.coeFn_smul r u)] with x total original scale same
    rw [RingHom.id_apply,total,scale,Pi.smul_apply,original]
    exact same.trans (smul_comm _ _ _)
  norm_map' := half_norm E

def map (time : ℝ) : Lag E →ₗᵢ[ℝ] Absolute E :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun s : ℝ => time-s)
    (Measure.measurePreserving_sub_left volume time)).comp (halfIsometry E)

theorem map_ae (time : ℝ) (v : Lag E) :
    map E time v=ᵐ[volume] fun s => rootKernel (time-s) • v (time-s) := by
  have shifted := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae (half_ae E v)
  filter_upwards [Lp.coeFn_compMeasurePreserving (half E v)
    (Measure.measurePreserving_sub_left volume time),shifted] with s read actual
  change map E time v s=_ at read
  exact read.trans actual

def clock (advance : ℝ) : Absolute E →ₗᵢ[ℝ] Absolute E :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun s : ℝ => s-advance)
    (by simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-advance))

theorem clock_ae (advance : ℝ) (v : Absolute E) : clock E advance v=ᵐ[volume] fun s => v (s-advance) :=
  Lp.coeFn_compMeasurePreserving v
    (by simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-advance))

theorem map_clock (time advance : ℝ) (v : Lag E) :
    map E (advance+time) v=clock E advance (map E time v) := by
  apply Lp.ext
  have preserves : MeasurePreserving (fun s : ℝ => s-advance) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-advance)
  have shifted := preserves.quasiMeasurePreserving.ae (map_ae E time v)
  filter_upwards [map_ae E (advance+time) v,clock_ae E advance (map E time v),shifted] with s first last actual
  rw [first,last,actual]
  congr 2 <;> ring

theorem pairing (time : ℝ) (u v : Lag E) : inner ℝ (map E time u) (map E time v)=inner ℝ u v :=
  (map E time).inner_map_map u v

theorem norm_map (time : ℝ) (v : Lag E) : ‖map E time v‖=‖v‖ := (map E time).norm_map v

theorem naturality {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (L : E →L[ℝ] F) (time : ℝ) (v : Lag E) :
    map F time (L.compLpL 2 averageMeasure v)=L.compLpL 2 (volume : Measure ℝ) (map E time v) := by
  apply Lp.ext
  have source := weighted_ae F (L.coeFn_compLpL v)
  have shifted := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae source
  filter_upwards [map_ae F time (L.compLpL 2 averageMeasure v),L.coeFn_compLpL (map E time v),
    map_ae E time v,shifted] with s target applied actual original
  rw [target,applied,actual,map_smul]
  exact original

theorem map_scalar {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]
    (time : ℝ) (c : 𝕜) (v : Lag E) : map E time (c • v)=c • map E time v := by
  apply Lp.ext
  have source := weighted_ae E (Lp.coeFn_smul c v)
  have shifted := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae source
  filter_upwards [map_ae E time (c • v),Lp.coeFn_smul c (map E time v),map_ae E time v,shifted]
    with s target scale actual original
  rw [target,scale,Pi.smul_apply,actual]
  exact original.trans (smul_comm _ _ _)

theorem bilinear_pairing {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (B : E →L[ℝ] E →L[ℝ] F) (time : ℝ) (u v : Lag E) :
    B.lpPairing (volume : Measure ℝ) 2 2 (map E time u) (map E time v)=B.lpPairing averageMeasure 2 2 u v := by
  rw [B.lpPairing_eq_integral,B.lpPairing_eq_integral,NativeForwardWindowPairingReadout.density_integral]
  calc
    _ = ∫ s : ℝ,NativeForwardWindowSource.kernel (time-s) • B (u (time-s)) (v (time-s)) := by
      apply integral_congr_ae
      filter_upwards [map_ae E time u,map_ae E time v] with s first last
      rw [first,last]
      simp only [map_smul,smul_apply,smul_smul,← pow_two,NativeWindowKernelHalfDensity.square]
    _ = _ := integral_sub_left_eq_self
      (fun x : ℝ => NativeForwardWindowSource.kernel x • B (u x) (v x)) volume time

section Adjoint
variable [CompleteSpace E]

def pull (time : ℝ) : Absolute E →L[ℝ] Lag E := (map E time).toContinuousLinearMap.adjoint

theorem pull_map (time : ℝ) (v : Lag E) : pull E time (map E time v)=v := by
  have exactMap:=congrArg (fun L : Lag E →L[ℝ] Lag E => L v) (map E time).adjoint_comp_self
  exact exactMap

def operator (time : ℝ) (A : Lag E →L[ℝ] Lag E) : Absolute E →L[ℝ] Absolute E :=
  (map E time).toContinuousLinearMap.comp (A.comp (pull E time))

theorem operator_map (time : ℝ) (A : Lag E →L[ℝ] Lag E) (v : Lag E) :
    operator E time A (map E time v)=map E time (A v) := by
  simp only [operator,ContinuousLinearMap.comp_apply,pull_map,LinearIsometry.coe_toContinuousLinearMap]

end Adjoint

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeIsometry
