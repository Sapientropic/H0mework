import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Continuum.Spacetime.Strong.Field
import Mathlib.Topology.ContinuousMap.Bounded.Normed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

namespace SaturationMonoid.PhysicsCore.YangMills.Spacetime.SpatialFields
noncomputable section
open Terminal

def spatialPoint : Terminal.Spacetime →L[ℝ] Terminal.Spacetime :=
  (LinearMap.id - timeLine.comp (EuclideanSpace.proj 0).toLinearMap).toContinuousLinearMap

theorem spatialPoint_apply (p : Terminal.Spacetime) :
    spatialPoint p = p - timeLine (p 0) := rfl

theorem spatialPoint_shift (p : Terminal.Spacetime) (t : ℝ) :
    spatialPoint (p + timeLine t) = spatialPoint p := by
  simp only [spatialPoint_apply, map_add, timeLine_time]
  module

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* (H ≃ₗᵢ[ℂ] H))
  (strong : ∀ v, Continuous (Quantum.Generator.orbit U v))
  (B : Terminal.Spacetime →ᵇ (H →L[ℂ] H))

def kernel (p : Terminal.Spacetime) : H →L[ℂ] H :=
  StrongFields.kernel U (B (spatialPoint p)) p

theorem kernel_bound (p : Terminal.Spacetime) : ‖kernel U B p‖ ≤ ‖B‖ :=
  (StrongFields.kernel_bound U _ p).trans (B.norm_coe_le_norm _)

include strong in
theorem kernel_continuous (v : H) : Continuous (fun p => kernel U B p v) := by
  have each := (StrongFields.joint_continuous U strong).comp
    (((PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0).neg).prodMk
      (((B.continuous.comp spatialPoint.continuous).clm_apply
        ((strong v).comp (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0)))))
  convert each using 1
  funext p
  change U (Multiplicative.ofAdd (-p 0))
    (B (spatialPoint p) ((U (Multiplicative.ofAdd (-p 0))).symm v)) = _
  have inverse : (U (Multiplicative.ofAdd (-p 0))).symm = U (Multiplicative.ofAdd (p 0)) := by
    rw [show Multiplicative.ofAdd (-p 0) = (Multiplicative.ofAdd (p 0))⁻¹ from rfl, map_inv]
    rfl
  rw [inverse]
  rfl

def onL1 : Lp ℂ 1 (volume : Measure Terminal.Spacetime) →L[ℂ] (H →L[ℂ] H) :=
  Quantum.Dynamics.Smearing.onL1 volume (kernel U B)
    (fun v => (kernel_continuous U strong B v).aestronglyMeasurable)
    ‖B‖ (norm_nonneg _) (kernel_bound U B)

def field : Terminal.Test →L[ℂ] (H →L[ℂ] H) :=
  (onL1 U strong B).comp (SchwartzMap.toLpCLM ℂ ℂ 1 volume)

theorem field_integral (f : Terminal.Test) (v : H) :
    field U strong B f v = ∫ p, f p • kernel U B p v := by
  rw [field, ContinuousLinearMap.comp_apply, onL1, Quantum.Dynamics.Smearing.onL1_integral]
  exact integral_congr_ae ((f.coeFn_toLp 1 volume).mono
    (fun p same => congrArg (· • kernel U B p v) same))

include strong in
theorem field_integrable (f : Terminal.Test) (v : H) : Integrable (fun p => f p • kernel U B p v) :=
  f.integrable.smul_bdd (‖B‖*‖v‖) (kernel_continuous U strong B v).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => (kernel U B p).le_of_opNorm_le (kernel_bound U B p) v))

end
end SaturationMonoid.PhysicsCore.YangMills.Spacetime.SpatialFields
