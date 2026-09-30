import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.EmptyWork

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredJointCubicGate
open Set
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
noncomputable section
variable {nu : Viscosity}

theorem source_joint_cubic_gate (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃r C : ℝ,0<r ∧0≤C ∧∀M≥low,∀time∈Icc 0 horizon,
      let w:=mean (finiteHistory seed time M)
      (nu.coeff^2/64)*‖laplacianFiber nu M w‖^4+
        nu.coeff^2*‖laplacianFiber nu M w‖^2+
        (3*nu.coeff^2/4)*(∑j : Coordinate,
          ‖laplacianFiber nu M
            (NativeWindowHistoryAllOrderWord.value seed M [j] time)‖^2)+
        r*deriv (NativeCenteredJointAggregate.energy seed M) time+
        (r*nu.coeff^2/2)*(∑j : Coordinate,
          ‖laplacianAction nu M
            (NativeCenteredWeightedResidualRate.centeredWord seed M j time)‖^2)≤
        r*(∑j : Coordinate,
          NativeCenteredJointAggregate.remainingAction seed M time j)+C := by
  obtain ⟨low,r,B,r0,B0,source⟩:=
    NativeCenteredJointAggregate.source_joint_positive_budget seed horizon nonnegative
  let delta:=nu.coeff^2/(64*r)
  have delta0 : 0<delta:=by dsimp only [delta]; positivity [nu.coeff_pos]
  obtain ⟨K,K0,empty⟩:=
    NativeCenteredEmptyWorkPaid.source_empty_work_quartic seed horizon delta delta0
  let C:=B+r*K
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨low,r,C,r0,C0,fun M above time inside => ?_⟩
  have gate:=source M above time inside
  have paid:=empty M time inside
  dsimp only at gate paid ⊢
  have scaled:=mul_le_mul_of_nonneg_left paid r0.le
  have coefficient : r*delta=nu.coeff^2/64 := by
    dsimp only [delta]
    field_simp [r0.ne']
  have scaledRead : r*(delta*‖laplacianFiber nu M (mean (finiteHistory seed time M))‖^4)=
      (nu.coeff^2/64)*‖laplacianFiber nu M (mean (finiteHistory seed time M))‖^4 := by
    rw [← mul_assoc,coefficient]
  rw [mul_add,scaledRead] at scaled
  rw [show NativeWindowHistoryAllOrderWord.value seed M [] time=
    mean (finiteHistory seed time M) from
      NativeWindowHistoryMeanPhysicalJet.include_mean seed M time] at gate
  dsimp only [C]
  nlinarith only [gate,scaled]

end
end SaturationMonoid.NavierStokes.NativeCenteredJointCubicGate
