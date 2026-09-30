import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.WeightedResidualRate
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.AdvectorEnergy

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredBathSplit
open Set
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H gradient)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
open NativeWindowHistoryMeanProjection (residual)
noncomputable section
variable {nu : Viscosity}

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem source_weighted_bath_split (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (q : H) (centered : residual q=q) :
    2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
      (NativeWindowHistoryMeanBlocks.bath seed M time q)=
        -2*nu.coeff*gradient M q-2*nu.coeff^2*‖laplacianAction nu M q‖^2+
          2*nu.coeff*inner ℝ (laplacianAction nu M q)
            (NativeWindowHistorySchurAdvectorAction.xAction seed M time q+
              NativeWindowHistorySchurAdvectorAction.wAction seed M time q) := by
  have lapCentered : residual (laplacianAction nu M q)=laplacianAction nu M q := by
    exact (NativeWindowHistorySchurCenteredGraph.laplacian_center nu M q).trans
      (congrArg (laplacianAction nu M) centered)
  have bath : NativeWindowHistoryMeanBlocks.bath seed M time q=
      residual (NativeWindowHistoryOseen.action seed M time q) := by
    change residual (NativeWindowHistoryOseen.action seed M time (residual q))=_
    exact congrArg (fun z : H => residual (NativeWindowHistoryOseen.action seed M time z)) centered
  have bathMass : inner ℝ q (NativeWindowHistoryMeanBlocks.bath seed M time q)=
      -nu.coeff*gradient M q :=
    (NativeWindowHistoryBathResolvent.bath_energy seed M time q).trans
      (congrArg (fun z : H => -nu.coeff*gradient M z) centered)
  have bathLap : inner ℝ (laplacianAction nu M q)
      (NativeWindowHistoryMeanBlocks.bath seed M time q)=
        inner ℝ (laplacianAction nu M q)
          (NativeWindowHistoryOseen.action seed M time q) := by
    let z:=laplacianAction nu M q
    let a:=NativeWindowHistoryOseen.action seed M time q
    have first:=congrArg (inner ℝ z) bath
    have sym:=NativeWindowHistoryMeanProjection.residual_symmetric z a
    have last:=congrArg (fun x : H => inner ℝ x a) lapCentered
    exact first.trans (sym.symm.trans last)
  have action:=NativeWindowHistorySchurAdvectorEnergy.source_action_read seed M time q
  rw [action] at bathLap
  simp only [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq] at bathLap
  have heatRead : inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
      (NativeWindowHistoryMeanBlocks.bath seed M time q)=
      inner ℝ q (NativeWindowHistoryMeanBlocks.bath seed M time q)+
        nu.coeff*inner ℝ (laplacianAction nu M q)
          (NativeWindowHistoryMeanBlocks.bath seed M time q) := by
    calc
      _=inner ℝ (NativeWindowHistoryMeanBlocks.bath seed M time q)
          (NativeWindowHistoryJacobianControl.heat nu M q) :=
        real_inner_comm (NativeWindowHistoryMeanBlocks.bath seed M time q)
          (NativeWindowHistoryJacobianControl.heat nu M q)
      _=inner ℝ (NativeWindowHistoryMeanBlocks.bath seed M time q) q+
          nu.coeff*inner ℝ (NativeWindowHistoryMeanBlocks.bath seed M time q)
            (laplacianAction nu M q) :=
        NativeWindowHistoryJacobianControl.form_split nu M _ _
      _=_ := congrArg₂ (fun x y : ℝ => x+nu.coeff*y)
        (real_inner_comm q (NativeWindowHistoryMeanBlocks.bath seed M time q))
        (real_inner_comm (laplacianAction nu M q)
          (NativeWindowHistoryMeanBlocks.bath seed M time q))
  calc
    _=2*(inner ℝ q (NativeWindowHistoryMeanBlocks.bath seed M time q)+
        nu.coeff*inner ℝ (laplacianAction nu M q)
          (NativeWindowHistoryMeanBlocks.bath seed M time q)) :=
      congrArg (fun z : ℝ => 2*z) heatRead
    _=2*(-nu.coeff*gradient M q+nu.coeff*
      (-nu.coeff*‖laplacianAction nu M q‖^2+
        inner ℝ (laplacianAction nu M q)
          (NativeWindowHistorySchurAdvectorAction.xAction seed M time q)+
        inner ℝ (laplacianAction nu M q)
          (NativeWindowHistorySchurAdvectorAction.wAction seed M time q))) :=
      congrArg₂ (fun x y : ℝ => 2*(x+nu.coeff*y)) bathMass bathLap
    _=_ := by rw [inner_add_right]; ring

end
end SaturationMonoid.NavierStokes.NativeCenteredBathSplit
