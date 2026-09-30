import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.EnergyAbsorption
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianControl
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.CenteredGraph

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredCouplingCommutator
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowTraceWholeHistory (H)
open NativeWindowHistoryMeanProjection (embed residual)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
variable {nu : Viscosity}

def creationCommutator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    wholePhysical →L[ℝ] H :=
  (NativeWindowHistoryJacobianControl.heat nu M).comp
    (NativeWindowHistoryMeanAction.creation seed M time)-
      (NativeWindowHistoryMeanAction.creation seed M time).comp
        (NativeWindowHistoryAllOrderPrincipal.weight nu M)

theorem source_coupling_commutator (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (u : wholePhysical) (q : H) :
    inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
        (NativeWindowHistoryMeanBlocks.annihilation seed M time q)+
      inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
        (NativeWindowHistoryMeanAction.creation seed M time u)=
      inner ℝ q (creationCommutator seed M time u) := by
  have green:=NativeWindowHistoryMeanBlocks.coupling_green seed M time
    (NativeWindowHistoryAllOrderPrincipal.weight nu M u) q
  have symmetric:=NativeWindowHistoryJacobianControl.form_symmetric nu M q
    (NativeWindowHistoryMeanAction.creation seed M time u)
  change inner ℝ q (NativeWindowHistoryJacobianControl.heat nu M
    (NativeWindowHistoryMeanAction.creation seed M time u))=
      inner ℝ (NativeWindowHistoryMeanAction.creation seed M time u)
        (NativeWindowHistoryJacobianControl.heat nu M q) at symmetric
  have symmetry : inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
      (NativeWindowHistoryMeanAction.creation seed M time u)=
        inner ℝ q (NativeWindowHistoryJacobianControl.heat nu M
          (NativeWindowHistoryMeanAction.creation seed M time u)) := by
    calc
      _=inner ℝ (NativeWindowHistoryMeanAction.creation seed M time u)
          (NativeWindowHistoryJacobianControl.heat nu M q) :=
        real_inner_comm (NativeWindowHistoryMeanAction.creation seed M time u)
          (NativeWindowHistoryJacobianControl.heat nu M q)
      _=_ := symmetric.symm
  simp only [creationCommutator,sub_apply,ContinuousLinearMap.comp_apply]
  rw [inner_sub_right (𝕜 := ℝ) q]
  have reverse : inner ℝ q (NativeWindowHistoryMeanAction.creation seed M time
      (NativeWindowHistoryAllOrderPrincipal.weight nu M u))=
        inner ℝ (NativeWindowHistoryMeanAction.creation seed M time
          (NativeWindowHistoryAllOrderPrincipal.weight nu M u)) q :=
    real_inner_comm (NativeWindowHistoryMeanAction.creation seed M time
      (NativeWindowHistoryAllOrderPrincipal.weight nu M u)) q
  linarith only [green,symmetry,reverse]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem source_creation_commutator (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (u : wholePhysical) :
    creationCommutator seed M time u=
      nu.coeff • residual
        (laplacianAction nu M (NativeWindowHistoryOseen.action seed M time (embed u))-
          NativeWindowHistoryOseen.action seed M time (laplacianAction nu M (embed u))) := by
  let A:=NativeWindowHistoryOseen.action seed M time
  let L:=laplacianAction nu M
  let Q : H →L[ℝ] H:=NativeWindowHistoryMeanProjection.residual
  let e:=embed
  let F:=laplacianFiber nu M
  have commute (v : H) : L (Q v)=Q (L v) :=
    (NativeWindowHistorySchurCenteredGraph.laplacian_center nu M v).symm
  have embedLap : L (e u)=e (F u) :=
    NativeWindowHistoryMeanProjection.comp_embed (laplacianFiber nu M) u
  have input : e (u+nu.coeff • F u)=e u+nu.coeff • L (e u) := by
    rw [map_add,map_smul,embedLap]
  change (Q (A (e u))+nu.coeff • L (Q (A (e u))))-
      Q (A (e (u+nu.coeff • F u)))=
        nu.coeff • Q (L (A (e u))-A (L (e u)))
  calc
    _=(Q (A (e u))+nu.coeff • Q (L (A (e u))))-
        Q (A (e (u+nu.coeff • F u))) :=
      congrArg (fun z : H => Q (A (e u))+nu.coeff • z-
        Q (A (e (u+nu.coeff • F u)))) (commute (A (e u)))
    _=(Q (A (e u))+nu.coeff • Q (L (A (e u))))-
        Q (A (e u+nu.coeff • L (e u))) :=
      congrArg (fun z : H => Q (A (e u))+nu.coeff • Q (L (A (e u)))-Q (A z)) input
    _=_ := by simp only [map_add,map_smul,map_sub,smul_sub]; abel

end
end SaturationMonoid.NavierStokes.NativeCenteredCouplingCommutator
