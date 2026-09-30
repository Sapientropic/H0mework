import H0mework.Versions.X.NavierStokes.WindowHistoryRecovery.Covariance
import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.Memory
import H0mework.Versions.X.NavierStokes.StressRegeneration.StressEnergy

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCovarianceDynamics
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryOseen (H)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistoryCovarianceRecovery (fiber pairing stress stress_integral)
open NativeCompleteStressCarrier (Space)
open NativeWindowHistoryMeanBlocks (bath)
open NativeWindowHistoryMeanAction (creation)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}
local notation "Q" => NativeWindowHistoryMeanProjection.residual

set_option backward.isDefEq.respectTransparency false in
theorem pairing_embed_left (u : wholePhysical) (v : H) : pairing (embed u) v=fiber u (mean v) := by
  unfold pairing
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  have actual : (fun lag => fiber (embed u lag) (v lag))=ᵐ[averageMeasure] fun lag => fiber u (v lag) := by
    filter_upwards [NativeWindowTraceWholeHistory.constant_ae u] with lag same
    exact congrArg (fun w : wholePhysical => fiber w (v lag)) same
  rw [integral_congr_ae actual,NativeWindowHistoryMeanProjection.mean_original]
  exact (fiber u).integral_comp_comm ((Lp.memLp v).integrable (by norm_num))

private theorem integral_right {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (B : E →L[ℝ] F →L[ℝ] G) (f : ℝ → E) (v : F)
    (regular : Integrable f averageMeasure) :
    (∫lag,B (f lag) v ∂averageMeasure)=B (∫lag,f lag ∂averageMeasure) v :=
  (B.flip v).integral_comp_comm regular

set_option backward.isDefEq.respectTransparency false in
theorem pairing_embed_right (u : H) (v : wholePhysical) : pairing u (embed v)=fiber (mean u) v := by
  unfold pairing
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  have actual : (fun lag => fiber (u lag) (embed v lag))=ᵐ[averageMeasure] fun lag => fiber (u lag) v := by
    filter_upwards [NativeWindowTraceWholeHistory.constant_ae v] with lag same
    exact congrArg (fiber (u lag)) same
  rw [integral_congr_ae actual,NativeWindowHistoryMeanProjection.mean_original]
  exact integral_right fiber u v ((Lp.memLp u).integrable (by norm_num))

private theorem centered_pair {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] E →L[ℝ] F) (h p : E) (q : F)
    (left : B h p=q) (right : B p h=q) (both : B p p=q) : B (h-p) (h-p)=B h h-q := by
  simp only [map_sub,sub_apply,left,right,both]
  abel

set_option backward.isDefEq.respectTransparency false in
theorem residual_stress (h : H) : stress (Q h)=NativeWindowHistoryCovarianceRecovery.residual h := by
  have both:pairing (embed (mean h)) (embed (mean h))=fiber (mean h) (mean h) :=
    (pairing_embed_left (mean h) (embed (mean h))).trans
      (congrArg (fiber (mean h)) (NativeWindowHistoryMeanProjection.mean_embed (mean h)))
  exact centered_pair (E := H) pairing h (embed (mean h)) (fiber (mean h) (mean h))
    (pairing_embed_right h (mean h)) (pairing_embed_left (mean h) h) both

def value (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) : Space :=
  stress (Q (finiteHistory seed t M))

def drive (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) : H :=
  creation seed M t (mean (finiteHistory seed t M))+Q (NativeWindowHistoryOseen.forcingHistory seed M t)

def tensorAction (A : H →L[ℝ] H) (r : H) : Space := pairing (A r) r+pairing r (A r)
def tensorInput (f r : H) : Space := pairing f r+pairing r f

private theorem pair_derivative {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (B : E →L[ℝ] E →L[ℝ] G)
    (x : ℝ → E) (x' : E) (t : ℝ) (actual : HasDerivAt x x' t) :
    HasDerivAt (fun s => B (x s) (x s)) (B x' (x t)+B (x t) x') t := by
  have both:=(B.hasFDerivAt.comp_hasDerivAt t actual).clm_apply actual
  simpa only [Function.comp_apply] using both

private theorem pair_rate {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (B : E →L[ℝ] E →L[ℝ] G) (r b f : E) :
    B (b+f) r+B r (b+f)=(B b r+B r b)+(B f r+B r f) := by
  simp only [map_add,add_apply]
  abel

set_option backward.isDefEq.respectTransparency false in
theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) :
    HasDerivAt (value seed M)
      (tensorAction (bath seed M t) (Q (finiteHistory seed t M))+
        tensorInput (drive seed M t) (Q (finiteHistory seed t M))) t := by
  have actual : HasDerivAt (fun s => Q (finiteHistory seed s M))
      (bath seed M t (Q (finiteHistory seed t M))+drive seed M t) t := by
    simpa only [NativeWindowHistoryCausalMean.residual,NativeWindowHistoryCausalMean.input,drive] using!
      NativeWindowHistoryCausalMean.source_derivative seed M t
  have two:=pair_derivative (E := H) (G := Space) pairing _ _ t actual
  exact two.congr_deriv (pair_rate pairing _ _ _)

open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open NativeWordStressEnergy (kineticRead)

theorem fiber_kinetic (v : wholePhysical) : kineticRead (fiber v v)=‖v‖^2 := by
  rw [NativeWordStressEnergy.kineticRead_apply]
  change -(∑i : Coordinate,(NativeCompleteStressCarrier.read
    (NativeCompleteStressBilinear.mixedCLM (NativeEndpointVelocityCarrier.wholeVelocity v.1)
      (NativeEndpointVelocityCarrier.wholeVelocity v.1)) 0 i i).re)=_
  rw [NativeCompleteStressBilinear.mixedCLM_apply,NativeCompleteStressBilinear.mixed_read]
  change -(∑i : Coordinate,(NativeCofinalFluxPairing.bilinearFlux v.1 v.1 0 i i).re)=_
  rw [NativeCofinalFluxPairing.bilinearFlux_zero_trace v.1 v.2.2,neg_neg]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem kinetic_stress (h : H) : kineticRead (stress h)=‖h‖^2 := by
  have regular:Integrable (fun lag => fiber (h lag) (h lag)) averageMeasure :=
    (fiber.memLp_of_bilin 1 (Lp.memLp h) (Lp.memLp h)).integrable le_rfl
  rw [stress_integral,← kineticRead.integral_comp_comm regular]
  simp only [fiber_kinetic]
  exact (NativeWindowTraceWholeHistory.norm_square h).symm

private theorem quadratic_cross {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (B : E →L[ℝ] E →L[ℝ] G) (K : G →L[ℝ] ℝ)
    (square : ∀r,K (B r r)=‖r‖^2) (f r : E) : K (B f r+B r f)=2*inner ℝ r f := by
  have total:=square (r+f)
  simp only [map_add,add_apply] at total
  have diagonalR:=square r
  have diagonalF:=square f
  have normed:=norm_add_sq_real r f
  rw [map_add]
  linarith only [total,diagonalR,diagonalF,normed]

set_option backward.isDefEq.respectTransparency false in
theorem kinetic_input (f r : H) : kineticRead (tensorInput f r)=2*inner ℝ r f :=
by
  have square (v : H) : kineticRead (pairing v v)=‖v‖^2 := kinetic_stress v
  exact quadratic_cross (E := H) (G := Space) pairing kineticRead square f r

theorem value_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) :
    value seed M t=stress (finiteHistory seed t M)-
      NativeStressTimeAlgebra.quadratic (mean (finiteHistory seed t M)).1 := residual_stress _

theorem value_tendsto (seed : GeneratedWholeRestartCurrent nu) (t : ℝ) :
    Tendsto (fun M => value seed M t) atTop
      (𝓝 ((NativeForwardWindowSource.source seed t).snd-
        NativeStressTimeAlgebra.quadratic (NativeForwardWindowSource.source seed t).fst)) := by
  have actual:=NativeWindowHistoryCovarianceRecovery.residual_continuous.tendsto
    (NativeWindowTraceWholeHistory.history seed t) |>.comp
      (NativeWindowHistoryWholeRecovery.projected_tendsto (NativeWindowTraceWholeHistory.history seed t))
  have curve : (fun M => NativeWindowHistoryCovarianceRecovery.residual
      (NativeWindowTraceWholeHistory.projected M (NativeWindowTraceWholeHistory.history seed t)))=
      (fun M => value seed M t) := by
    funext M
    exact (residual_stress (finiteHistory seed t M)).symm
  simpa only [Function.comp_def,curve,NativeWindowHistoryCovarianceRecovery.source_residual] using actual

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCovarianceDynamics
