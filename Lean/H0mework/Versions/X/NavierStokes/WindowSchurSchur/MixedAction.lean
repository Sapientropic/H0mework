import H0mework.Versions.X.NavierStokes.WindowSchurSchur.AdvectorEnergy
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.CenteredGraph
set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurMixedAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryOseen (H action rateHistory forcingHistory)
open NativeWindowHistorySchurCompletion (completion)
open NativeWindowHistorySchurTemporalControl (temporalResponse)
open NativeWindowHistorySchurAdvectorAction (xAction wAction)
open NativeWindowHistorySchurMomentum (xJoint)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
noncomputable section
variable {nu : Viscosity}

def controlledInput (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  xJoint seed M time+xAction seed M time (temporalResponse seed M time)

theorem temporal_gradient (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    gradient M (temporalResponse seed M time) ≤ NativeWindowHistorySchurTemporalControl.temporalBudget seed horizon/nu.coeff := by
  have source:=NativeWindowHistorySchurTemporalControl.source_temporal_energy seed horizon M time inside
  change ‖temporalResponse seed M time‖^2+nu.coeff*gradient M (temporalResponse seed M time) ≤ _ at source
  apply (le_div_iff₀ nu.coeff_pos).mpr
  nlinarith only [source,sq_nonneg ‖temporalResponse seed M time‖]

private theorem graph_transfer (a d h g epsilon K B T : ℝ) (eps0 : 0 ≤ epsilon) (B0 : 0 ≤ B)
    (paid : a ≤ (epsilon/3)*d+B*g) (graph : d ≤ 3*h+K) (gradient : g ≤ T) :
    a ≤ epsilon*h+((epsilon/3)*K+B*T) := by
  have first:=mul_le_mul_of_nonneg_left graph (by positivity : 0 ≤ epsilon/3)
  have last:=mul_le_mul_of_nonneg_left gradient B0
  nlinarith only [paid,first,last]

private theorem on_temporal (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ B : ℝ,0 ≤ B ∧∀ M ≥ low,∀ time∈Icc 0 horizon,
      ‖xAction seed M time (temporalResponse seed M time)‖^2 ≤
        epsilon*‖laplacianAction nu M (temporalResponse seed M time)‖^2+B*gradient M (temporalResponse seed M time) := by
  obtain ⟨low,B,B0,source⟩:=NativeWindowHistorySchurAdvectorAction.source_graph_bound seed horizon nonnegative epsilon positive
  exact ⟨low,B,B0,fun M above time inside => source M above time inside (temporalResponse seed M time)⟩

theorem source_mixed_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time∈Icc 0 horizon,
      ‖xAction seed M time (temporalResponse seed M time)‖^2 ≤ epsilon*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C := by
  have small : 0 < epsilon/3 := div_pos positive (by norm_num)
  have actionBound:=on_temporal seed horizon nonnegative (epsilon/3) small
  obtain ⟨last,B,B0,source⟩:=actionBound
  obtain ⟨first,K,K0,graph⟩:=NativeWindowHistorySchurCenteredGraph.source_temporal_graph seed horizon nonnegative
  let T:=NativeWindowHistorySchurTemporalControl.temporalBudget seed horizon/nu.coeff
  have T0:0 ≤ T:=div_nonneg (NativeWindowHistorySchurTemporalControl.temporalBudget_nonnegative seed horizon) nu.coeff_pos.le
  refine ⟨max first last,(epsilon/3)*K+B*T,add_nonneg (mul_nonneg (div_nonneg positive.le (by norm_num)) K0) (mul_nonneg B0 T0),
    fun M above time inside => ?_⟩
  exact graph_transfer _ _ _ _ epsilon K B T positive.le B0
    (source M (le_trans (le_max_right _ _) above) time inside)
    (graph M (le_trans (le_max_left _ _) above) time inside) (temporal_gradient seed horizon M time inside)

private theorem sum_square {E : Type*} [SeminormedAddCommGroup E] (u v : E) :
    ‖u+v‖^2 ≤ 2*‖u‖^2+2*‖v‖^2 := by
  have bound:=pow_le_pow_left₀ (norm_nonneg (u+v)) (norm_add_le u v) 2
  nlinarith only [bound,sq_nonneg (‖u‖-‖v‖)]

theorem source_controlled_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time∈Icc 0 horizon,
      ‖controlledInput seed M time‖^2 ≤ epsilon*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C := by
  obtain ⟨first,K,K0,joint⟩:=NativeWindowHistorySchurMomentum.source_joint_bound seed horizon nonnegative (epsilon/4) (by positivity)
  obtain ⟨last,B,B0,mixed⟩:=source_mixed_bound seed horizon nonnegative (epsilon/4) (by positivity)
  refine ⟨max first last,2*K+2*B,by positivity,fun M above time inside => ?_⟩
  have sum:=sum_square (E := H) (xJoint seed M time) (xAction seed M time (temporalResponse seed M time))
  have paid:=joint M (le_trans (le_max_left _ _) above) time inside
  have bound:=mixed M (le_trans (le_max_right _ _) above) time inside
  change ‖xJoint seed M time+xAction seed M time (temporalResponse seed M time)‖^2 ≤ _
  nlinarith only [sum,paid,bound]

private theorem cancel_heat {E : Type*} [AddCommGroup E] [Module ℝ E] (a : ℝ) (l c w : E) :
    ((-a) • l+(c+w))+a • l=c+w := by rw [neg_smul]; abel

private theorem place_heat {E : Type*} [AddCommGroup E] [Module ℝ E] (a : ℝ) (l c w f : E) :
    (c+w-a • l)+f=(-a) • l+c+w+f := by rw [neg_smul]; abel

theorem source_action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    action seed M time (finiteHistory seed time M)+nu.coeff • laplacianAction nu M (finiteHistory seed time M)=
      controlledInput seed M time+wAction seed M time (temporalResponse seed M time) := by
  have original:=congrArg (fun T : H →L[ℝ] H => T (finiteHistory seed time M))
    (NativeWindowHistorySchurMomentum.rawAction_source seed M time)
  change action seed M time (finiteHistory seed time M)=
    (NativeWindowHistoryMeanBlocks.diffusion nu M).compLpL 2 NativeForwardWindowPairingReadout.averageMeasure
      (finiteHistory seed time M)+NativeWindowHistorySchurMomentum.rawNonlinear seed M time at original
  have split:NativeWindowHistorySchurMomentum.rawNonlinear seed M time=
      controlledInput seed M time+wAction seed M time (temporalResponse seed M time) :=
    NativeWindowHistorySchurMomentum.nonlinear_split seed M time
  have paid:=original.trans (congrArg₂ (fun u v : H => u+v)
    (NativeWindowHistorySchurAdvectorEnergy.diffusion_history nu M (finiteHistory seed time M)) split)
  exact (congrArg (fun u : H => u+nu.coeff • laplacianAction nu M (finiteHistory seed time M)) paid).trans
    (cancel_heat (E := H) nu.coeff _ _ _)

theorem source_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    rateHistory seed M time=(-nu.coeff) • laplacianAction nu M (finiteHistory seed time M)+
      controlledInput seed M time+wAction seed M time (temporalResponse seed M time)+forcingHistory seed M time := by
  have paid:=eq_sub_of_add_eq (source_action seed M time)
  have source:=NativeWindowHistoryOseen.source_equation seed M time
  exact source.trans ((congrArg (fun u : H => u+forcingHistory seed M time) paid).trans
    (place_heat (E := H) nu.coeff _ _ _ _))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem controlledInput_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    controlledInput seed M (step.2.clockAdvance+time)=controlledInput step.1 M time := by
  have next:=NativeWindowHistorySchurMomentum.terms_next seed M step generated time nonnegative
  exact congrArg (fun terms : H×H×H => terms.1+terms.2.1) next

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurMixedAction
