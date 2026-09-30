import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.BathPaid

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredJointBathPaid
open Set
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H)
noncomputable section
variable {nu : Viscosity}

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem source_joint_first_word_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧∀M≥low,∀time∈Icc 0 horizon,∀j : Coordinate,
      let h:=NativeWindowTraceWholeHistory.finiteHistory seed time M
      let w:=NativeWindowHistoryMeanProjection.mean h
      let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
      let q:=NativeCenteredWeightedResidualRate.centeredWord seed M j time
      2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
          (NativeWindowHistoryAllOrderWord.retained seed M [j] time)+
        deriv (NativeCenteredWeightedResidualRate.energy seed M j) time+
        (nu.coeff^2/2)*‖NativeWindowHistoryAnnihilationControl.laplacianAction nu M q‖^2≤
        2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
          (NativeWindowHistorySpatialWords.fiber M [j]
            (NativeWindowHistoryMeanAction.meanOperator seed M time w)-
              NativeWindowHistorySchurAction.effective seed M time u)+
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
  obtain ⟨low,C,C0,bath⟩:=NativeCenteredBathPaid.source_original_q_bath_paid seed horizon nonnegative
  refine ⟨low,C,C0,fun M above time inside j => ?_⟩
  have joint:=NativeCenteredWeightedResidualRate.source_joint_first_word_rate seed M time j
  have paid:=bath M above time inside j
  dsimp only at joint paid ⊢
  dsimp only [NativeCenteredWeightedResidualRate.centeredWord,
    NativeWindowHistorySpatialWords.history] at joint paid ⊢
  nlinarith only [joint,paid]

end
end SaturationMonoid.NavierStokes.NativeCenteredJointBathPaid
