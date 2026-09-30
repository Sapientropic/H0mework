import H0mework.Versions.X.NavierStokes.WindowSchurMean.Blocks
import H0mework.Versions.X.NavierStokes.WindowHistoryOseen.Gap
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryBathResolvent
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowHistoryMeanBlocks (bath)
open NativeWindowTraceWholeHistory (gradient)
noncomputable section
variable {nu : Viscosity}
local notation "Q" => NativeWindowHistoryMeanProjection.residual

private theorem shifted_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E) : inner ℝ v (v-w)=‖v‖^2-inner ℝ v w := by
  rw [inner_sub_right,real_inner_self_eq_norm_sq]

private theorem shifted_coercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E) (dissipative : ∀ v,inner ℝ v (B v) ≤ 0) :
    IsCoercive ((innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ).comp (ContinuousLinearMap.id ℝ E-B)) := by
  refine ⟨1,by norm_num,fun v => ?_⟩
  change 1*‖v‖*‖v‖ ≤ inner ℝ (v-B v) v
  rw [real_inner_comm,shifted_pair]
  nlinarith only [dissipative v]

private theorem equiv_original {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (h : IsCoercive ((innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ).comp A)) (v : E) :
    h.continuousLinearEquivOfBilin v=A v := by
  apply ext_inner_right ℝ
  intro w
  exact IsCoercive.continuousLinearEquivOfBilin_apply h v w

theorem residual_square (v : H) : Q (Q v)=Q v := by
  change Q v-NativeWindowHistoryMeanProjection.projection (Q v)=Q v
  rw [NativeWindowHistoryMeanProjection.projection_residual,sub_zero]

theorem residual_bath (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    Q (bath seed M time v)=bath seed M time v := residual_square _

theorem bath_residual (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    bath seed M time (Q v)=bath seed M time v := by
  change Q (NativeWindowHistoryOseen.action seed M time (Q (Q v)))=_
  rw [residual_square]
  rfl

theorem bath_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    inner ℝ v (bath seed M time v)=-nu.coeff*gradient M (Q v) :=
  (NativeWindowHistoryMeanProjection.residual_symmetric v
    (NativeWindowHistoryOseen.action seed M time (Q v))).symm.trans
      (NativeWindowHistoryOseenGap.action_energy seed M time (Q v))

def operator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H-bath seed M time

def form (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H →L[ℝ] ℝ :=
  (innerSL ℝ (E := H) : H →L[ℝ] H →L[ℝ] ℝ).comp (operator seed M time)

theorem coercive (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    IsCoercive (E := H) (form seed M time) := by
  simpa only [form,operator] using! shifted_coercive (E := H) (bath seed M time)
    (NativeWindowHistoryMeanBlocks.bath_dissipative seed M time)

def equivalence (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H ≃L[ℝ] H :=
  IsCoercive.continuousLinearEquivOfBilin (V := H) (B := form seed M time) (coercive seed M time)

theorem equivalence_apply (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    equivalence seed M time v=operator seed M time v := by
  simpa only [equivalence,form] using! equiv_original (E := H) (operator seed M time) (by exact coercive seed M time) v

def resolve (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  (equivalence seed M time).symm.toContinuousLinearMap

theorem resolve_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : H) :
    resolve seed M time f-bath seed M time (resolve seed M time f)=f :=
  (equivalence_apply seed M time (resolve seed M time f)).symm.trans
    ((equivalence seed M time).apply_symm_apply f)

theorem resolve_inverse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    resolve seed M time (v-bath seed M time v)=v :=
  (congrArg (resolve seed M time) (equivalence_apply seed M time v).symm).trans
    ((equivalence seed M time).symm_apply_apply v)

theorem resolve_unique (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v f : H)
    (equation : v-bath seed M time v=f) : v=resolve seed M time f :=
  (resolve_inverse seed M time v).symm.trans (congrArg (resolve seed M time) equation)

theorem resolve_residual (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : H) :
    Q (resolve seed M time f)=resolve seed M time (Q f) := by
  apply resolve_unique
  have source:=congrArg Q (resolve_equation seed M time f)
  have mapped:=(Q).map_sub (resolve seed M time f) (bath seed M time (resolve seed M time f))
  have recognized:=congrArg (fun w : H => Q (resolve seed M time f)-w)
    (residual_bath seed M time (resolve seed M time f))
  have actual:=recognized.symm.trans (mapped.symm.trans source)
  exact (congrArg (fun w : H => Q (resolve seed M time f)-w)
    (bath_residual seed M time (resolve seed M time f))).trans actual

theorem energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : H) :
    ‖resolve seed M time f‖^2+nu.coeff*gradient M (Q (resolve seed M time f))=
      inner ℝ (resolve seed M time f) f := by
  have source:=congrArg (fun w : H => inner ℝ (resolve seed M time f) w)
    (resolve_equation seed M time f)
  have paired:=(shifted_pair (E := H) (resolve seed M time f) (bath seed M time (resolve seed M time f))).symm.trans source
  rw [bath_energy] at paired
  linarith only [paired]

theorem norm_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : H) :
    ‖resolve seed M time f‖ ≤ ‖f‖ := by
  have source:=congrArg (fun w : H => inner ℝ (resolve seed M time f) w)
    (resolve_equation seed M time f)
  have paired:=(shifted_pair (E := H) (resolve seed M time f) (bath seed M time (resolve seed M time f))).symm.trans source
  have sign:=NativeWindowHistoryMeanBlocks.bath_dissipative seed M time (resolve seed M time f)
  have cauchy:=real_inner_le_norm (resolve seed M time f) f
  nlinarith [norm_nonneg (resolve seed M time f),norm_nonneg f]

theorem energy_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : H) :
    ‖resolve seed M time f‖^2+nu.coeff*gradient M (Q (resolve seed M time f)) ≤ ‖f‖^2 := by
  rw [energy]
  exact (real_inner_le_norm (resolve seed M time f) f).trans ((mul_le_mul_of_nonneg_right (norm_bound seed M time f)
    (norm_nonneg f)).trans_eq (pow_two ‖f‖).symm)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem resolve_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    resolve seed M (step.2.clockAdvance+time)=resolve step.1 M time := by
  have same:=congrArg (fun blocks => blocks.2.2.2)
    (NativeWindowHistoryMeanBlocks.blocks_next seed M step generated time nonnegative)
  dsimp only at same
  apply ContinuousLinearMap.ext
  intro f
  apply resolve_unique
  rw [← same]
  exact resolve_equation seed M (step.2.clockAdvance+time) f

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryBathResolvent
