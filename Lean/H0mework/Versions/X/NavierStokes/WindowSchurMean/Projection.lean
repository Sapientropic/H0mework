import H0mework.Versions.X.NavierStokes.WindowHistoryOseen.Equation
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceWhole.Control

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanProjection
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowHistoryOseen (H)
noncomputable section
variable {nu : Viscosity}

def embed : wholePhysical →L[ℝ] H := Lp.constL 2 averageMeasure ℝ

theorem embed_original (v : wholePhysical) : embed v=NativeWindowTraceWholeHistory.constant v := rfl

def mean : H →L[ℝ] wholePhysical := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := wholePhysical) (F := H) embed

theorem mean_original (v : H) : mean v=∫ lag,v lag ∂averageMeasure := by
  apply ext_inner_left ℝ
  intro w
  have paid : Integrable v averageMeasure := (Lp.memLp v).integrable (by norm_num)
  rw [mean,ContinuousLinearMap.adjoint_inner_right,L2.inner_def]
  have read : (∫ lag,inner ℝ (embed w lag) (v lag) ∂averageMeasure)=∫ lag,inner ℝ w (v lag) ∂averageMeasure := by
    apply integral_congr_ae
    filter_upwards [NativeWindowTraceWholeHistory.constant_ae w] with lag actual
    rw [show embed w lag=w from actual]
  rw [read]
  exact (innerSL ℝ w).integral_comp_comm paid

theorem mean_embed (v : wholePhysical) : mean (embed v)=v := by
  rw [mean_original,embed_original,integral_congr_ae (NativeWindowTraceWholeHistory.constant_ae v)]
  simp

theorem embed_pairing (u : wholePhysical) (v : H) : inner ℝ (embed u) v=inner ℝ u (mean v) := by
  rw [mean_original,L2.inner_def]
  have same : (fun lag => inner ℝ (embed u lag) (v lag))=ᵐ[averageMeasure] fun lag => inner ℝ u (v lag) := by
    filter_upwards [NativeWindowTraceWholeHistory.constant_ae u] with lag actual
    rw [show embed u lag=u from actual]
  rw [integral_congr_ae same]
  exact (innerSL ℝ u).integral_comp_comm ((Lp.memLp v).integrable (by norm_num))

theorem embed_inner (u v : wholePhysical) : inner ℝ (embed u) (embed v)=inner ℝ u v := by
  rw [embed_pairing,mean_embed]

theorem embed_norm (v : wholePhysical) : ‖embed v‖=‖v‖ := by
  have same := embed_inner v v
  rw [real_inner_self_eq_norm_sq (x := embed v),real_inner_self_eq_norm_sq (x := v)] at same
  exact (sq_eq_sq₀ (norm_nonneg (embed v)) (norm_nonneg v)).mp same

def projection : H →L[ℝ] H := embed.comp mean

def residual : H →L[ℝ] H := ContinuousLinearMap.id ℝ H-projection

theorem projection_square (v : H) : projection (projection v)=projection v := by
  change embed (mean (embed (mean v)))=embed (mean v)
  rw [mean_embed]

theorem projection_symmetric (u v : H) : inner ℝ (projection u) v=inner ℝ u (projection v) := by
  change inner ℝ (embed (mean u)) v=inner ℝ u (embed (mean v))
  rw [embed_pairing,real_inner_comm (F := H) (embed (mean v)) u,embed_pairing]
  exact real_inner_comm _ _

theorem mean_residual (v : H) : mean (residual v)=0 := by
  change mean (v-embed (mean v))=0
  rw [map_sub,mean_embed,sub_self]

theorem projection_residual (v : H) : projection (residual v)=0 := by
  change embed (mean (residual v))=0
  rw [mean_residual,map_zero]

theorem residual_projection (v : H) : residual (projection v)=0 := by
  change projection v-projection (projection v)=0
  rw [projection_square,sub_self]

theorem residual_symmetric (u v : H) : inner ℝ (residual u) v=inner ℝ u (residual v) := by
  change inner ℝ (u-projection u) v=inner ℝ u (v-projection v)
  rw [inner_sub_left (𝕜 := ℝ) u (projection u) v,inner_sub_right (𝕜 := ℝ) u v (projection v),projection_symmetric]

theorem embed_orthogonal (u : wholePhysical) (v : H) : inner ℝ (embed u) (residual v)=0 := by
  rw [embed_pairing,mean_residual,inner_zero_right]

theorem orthogonal (u v : H) : inner ℝ (projection u) (residual v)=0 := by
  rw [projection_symmetric,projection_residual]
  exact inner_zero_right (𝕜 := ℝ) u

theorem split (v : H) : projection v+residual v=v := by
  change projection v+(v-projection v)=v
  abel

private theorem pythagoras {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y z : E) (sum : x+y=z) (orthogonal : inner ℝ x y=0) : ‖z‖^2=‖x‖^2+‖y‖^2 := by
  rw [← sum,norm_add_sq_real,orthogonal]
  ring

theorem energy_split (v : H) : ‖v‖^2=‖projection v‖^2+‖residual v‖^2 :=
  pythagoras (E := H) (projection v) (residual v) v (split v) (orthogonal v v)

theorem mean_comp (A : wholePhysical →L[ℝ] wholePhysical) (v : H) :
    mean (A.compLpL 2 averageMeasure v)=A (mean v) := by
  rw [mean_original,mean_original,integral_congr_ae (A.coeFn_compLpL v)]
  exact A.integral_comp_comm ((Lp.memLp v).integrable (by norm_num))

theorem comp_embed (A : wholePhysical →L[ℝ] wholePhysical) (v : wholePhysical) :
    A.compLpL 2 averageMeasure (embed v)=embed (A v) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (embed v),NativeWindowTraceWholeHistory.constant_ae v,
    NativeWindowTraceWholeHistory.constant_ae (A v)] with lag first last target
  rw [first,show embed v lag=v from last,show embed (A v) lag=A v from target]

theorem projection_comp (A : wholePhysical →L[ℝ] wholePhysical) (v : H) :
    projection (A.compLpL 2 averageMeasure v)=A.compLpL 2 averageMeasure (projection v) := by
  change embed (mean (A.compLpL 2 averageMeasure v))=A.compLpL 2 averageMeasure (embed (mean v))
  rw [mean_comp,comp_embed]

theorem residual_comp (A : wholePhysical →L[ℝ] wholePhysical) (v : H) :
    residual (A.compLpL 2 averageMeasure v)=A.compLpL 2 averageMeasure (residual v) := by
  change A.compLpL 2 averageMeasure v-projection (A.compLpL 2 averageMeasure v)=A.compLpL 2 averageMeasure (v-projection v)
  exact (congrArg (fun w : H => A.compLpL 2 averageMeasure v-w) (projection_comp A v)).trans
    ((A.compLpL 2 averageMeasure).map_sub v (projection v)).symm

private theorem paired_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (x y z : E) (sum : x+y=z) (first : inner ℝ x (A y)=0) (last : inner ℝ y (A x)=0) :
    inner ℝ z (A z)=inner ℝ x (A x)+inner ℝ y (A y) := by
  rw [← sum]
  simp only [map_add,inner_add_left,inner_add_right,first,last,add_zero,zero_add]

private theorem comp_cross_left (A : wholePhysical →L[ℝ] wholePhysical) (v : H) :
    inner ℝ (projection v) (A.compLpL 2 averageMeasure (residual v))=0 := by
  rw [← residual_comp,orthogonal]

private theorem comp_cross_right (A : wholePhysical →L[ℝ] wholePhysical) (v : H) :
    inner ℝ (residual v) (A.compLpL 2 averageMeasure (projection v))=0 := by
  exact (congrArg (fun w : H => inner ℝ (residual v) w) (projection_comp A v)).symm.trans
    ((real_inner_comm (F := H) (projection (A.compLpL 2 averageMeasure v)) (residual v)).trans
      (orthogonal (A.compLpL 2 averageMeasure v) v))

theorem comp_energy_split (A : wholePhysical →L[ℝ] wholePhysical) (v : H) :
    inner ℝ v (A.compLpL 2 averageMeasure v)=
      inner ℝ (projection v) (A.compLpL 2 averageMeasure (projection v))+
      inner ℝ (residual v) (A.compLpL 2 averageMeasure (residual v)) := by
  simpa only [] using! paired_split (E := H) (A.compLpL 2 averageMeasure) (projection v) (residual v) v (split v)
    (comp_cross_left A v) (comp_cross_right A v)

theorem metric_split (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector) (R : ℕ) (v : H) :
    inner ℝ v (NativeWindowTraceWholeHistory.metricAction seed frame M F R v)=
      inner ℝ (projection v) (NativeWindowTraceWholeHistory.metricAction seed frame M F R (projection v))+
      inner ℝ (residual v) (NativeWindowTraceWholeHistory.metricAction seed frame M F R (residual v)) :=
  comp_energy_split (NativeWindowTraceWholeHistory.metric seed frame M F R) v

theorem source_mean (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    (mean (NativeWindowTraceWholeHistory.history seed time)).1=(NativeForwardWindowSource.source seed time).fst := by
  rw [mean_original,NativeWindowTraceWholeHistory.mean_original]

theorem source_residual (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    residual (NativeWindowTraceWholeHistory.history seed time)=NativeWindowTraceWholeHistory.centered seed time := by
  change NativeWindowTraceWholeHistory.history seed time-embed (mean (NativeWindowTraceWholeHistory.history seed time))=_
  rw [mean_original,embed_original]
  rfl

theorem preparation_residual (seed : GeneratedWholeRestartCurrent nu) :
    residual (NativeWindowTraceWholeHistory.history seed (-2))=0 := by
  rw [NativeWindowTraceWholeHistory.history_preparation]
  change embed (NativeWindowTraceWholeHistory.original seed 0)-embed (mean (embed (NativeWindowTraceWholeHistory.original seed 0)))=0
  rw [mean_embed,sub_self]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanProjection
