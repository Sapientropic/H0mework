import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.MeanPrincipal

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredJointMeanPaid
open Set
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H)
noncomputable section
variable {nu : Viscosity}

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem source_joint_first_word_mean_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧∀M≥low,∀time∈Icc 0 horizon,∀j : Coordinate,
      let h:=NativeWindowTraceWholeHistory.finiteHistory seed time M
      let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
      let q:=NativeCenteredWeightedResidualRate.centeredWord seed M j time
      2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
          (NativeWindowHistoryAllOrderWord.retained seed M [j] time)+
        deriv (NativeCenteredWeightedResidualRate.energy seed M j) time+
        (nu.coeff^2/2)*‖NativeWindowHistoryAnnihilationControl.laplacianAction nu M q‖^2≤
        epsilon*‖NativeWindowHistoryAnnihilationControl.laplacianFiber nu M u‖^2+
        2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
          (NativeWindowHistorySpatialWords.fiber M [j]
            (NativeWindowHistoryMeanProjection.mean
              (NativeWindowHistoryOseen.forcingHistory seed M time)))+
        2*inner ℝ q (NativeCenteredCouplingCommutator.creationCommutator seed M time u)+
        2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
          (NativeWindowHistoryMeanProjection.mean
            (NativeWindowHistorySpatialWords.commutator seed M [j] time
              (NativeWindowHistoryMeanProjection.residual h)))+
        2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
          (NativeWindowHistoryMeanProjection.residual
            (NativeWindowHistoryAllOrderCausal.load seed M [j] time))+
        2*nu.coeff*inner ℝ (NativeWindowHistoryAnnihilationControl.laplacianAction nu M q)
          (NativeWindowHistorySchurAdvectorAction.wAction seed M time q)+C := by
  obtain ⟨low,B,B0,joint⟩:=NativeCenteredJointBathPaid.source_joint_first_word_paid
    seed horizon nonnegative
  obtain ⟨K,K0,principal⟩:=NativeCenteredMeanPrincipal.source_mean_principal_uniform
    seed horizon epsilon positive
  refine ⟨low,B+K,add_nonneg B0 K0,fun M above time inside j => ?_⟩
  have rate:=joint M above time inside j
  have paid:=principal M time inside j
  dsimp only at rate paid ⊢
  nlinarith only [rate,paid]

end
end SaturationMonoid.NavierStokes.NativeCenteredJointMeanPaid
