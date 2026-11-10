import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Dynamics.Smearing.Strong
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Generator.Words
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Continuum.Spacetime.Domain.Integral

/-! Strongly continuous unitary time generates spacetime-smeared bounded operators directly on the original Hilbert space. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped InnerProductSpace

namespace SaturationMonoid.PhysicsCore.YangMills.Spacetime.StrongFields
noncomputable section
open Terminal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* (H ≃ₗᵢ[ℂ] H))
  (strong : ∀ v, Continuous (Quantum.Generator.orbit U v)) (A : H →L[ℂ] H)

def kernel (p : Terminal.Spacetime) : H →L[ℂ] H :=
  Quantum.Generator.Commutator.conjugation U A (-p 0)

theorem kernel_bound (p : Terminal.Spacetime) : ‖kernel U A p‖ ≤ ‖A‖ := by
  exact (StarAlgEquiv.norm_map ((U (Multiplicative.ofAdd (-p 0))).conjStarAlgEquiv) A).le

include strong in
omit [CompleteSpace H] in
theorem joint_continuous : Continuous (fun z : ℝ × H => U (Multiplicative.ofAdd z.1) z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply Metric.tendsto_nhds.mpr
  intro ε positive
  have half : 0 < ε/2 := half_pos positive
  have fixed := ((strong z.2).comp (continuous_fst : Continuous (fun w : ℝ × H => w.1))).continuousAt (x := z) |>.eventually
    (Metric.ball_mem_nhds _ half)
  have moving := (continuous_snd : Continuous (fun w : ℝ × H => w.2)).continuousAt (x := z) |>.eventually (Metric.ball_mem_nhds z.2 half)
  filter_upwards [fixed, moving] with w hf hm
  calc
    dist (U (Multiplicative.ofAdd w.1) w.2) (U (Multiplicative.ofAdd z.1) z.2) ≤
      dist (U (Multiplicative.ofAdd w.1) w.2) (U (Multiplicative.ofAdd w.1) z.2) +
        dist (U (Multiplicative.ofAdd w.1) z.2) (U (Multiplicative.ofAdd z.1) z.2) := dist_triangle _ _ _
    _ = dist w.2 z.2 + dist (U (Multiplicative.ofAdd w.1) z.2)
        (U (Multiplicative.ofAdd z.1) z.2) := by rw [(U (Multiplicative.ofAdd w.1)).isometry.dist_eq]
    _ < ε := by dsimp [Metric.mem_ball, Quantum.Generator.orbit] at hf hm; linarith

include strong in
theorem kernel_continuous (v : H) : Continuous (fun p => kernel U A p v) := by
  have each := (joint_continuous U strong).comp
    (((PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0).neg).prodMk
      (A.continuous.comp ((strong v).comp (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0))))
  convert each using 1
  funext p
  change U (Multiplicative.ofAdd (-p 0)) (A ((U (Multiplicative.ofAdd (-p 0))).symm v)) = _
  have inverse : (U (Multiplicative.ofAdd (-p 0))).symm = U (Multiplicative.ofAdd (p 0)) := by
    rw [show Multiplicative.ofAdd (-p 0) = (Multiplicative.ofAdd (p 0))⁻¹ from rfl, map_inv]
    rfl
  rw [inverse]
  rfl

def onL1 : Lp ℂ 1 (volume : Measure Terminal.Spacetime) →L[ℂ] (H →L[ℂ] H) :=
  Quantum.Dynamics.Smearing.onL1 volume (kernel U A)
    (fun v => (kernel_continuous U strong A v).aestronglyMeasurable)
    ‖A‖ (norm_nonneg _) (kernel_bound U A)

def field : Terminal.Test →L[ℂ] (H →L[ℂ] H) :=
  (onL1 U strong A).comp (SchwartzMap.toLpCLM ℂ ℂ 1 volume)

theorem field_integral (f : Terminal.Test) (v : H) :
    field U strong A f v = ∫ p, f p • kernel U A p v := by
  rw [field, ContinuousLinearMap.comp_apply, onL1, Quantum.Dynamics.Smearing.onL1_integral]
  exact integral_congr_ae ((f.coeFn_toLp 1 volume).mono (fun p same => congrArg (· • kernel U A p v) same))


include strong in
theorem field_integrable (f : Terminal.Test) (v : H) : Integrable (fun p => f p • kernel U A p v) :=
  f.integrable.smul_bdd (‖A‖*‖v‖) (kernel_continuous U strong A v).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => (kernel U A p).le_of_opNorm_le (kernel_bound U A p) v))

end
end SaturationMonoid.PhysicsCore.YangMills.Spacetime.StrongFields
