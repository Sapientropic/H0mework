import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.MeanStrainSource
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.JointControl

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanStrainJoint
open Set
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (gradient)
open NativeWindowHistorySpatialWords (history operator)
open NativeWindowHistoryAllOrderCausal (created load)
open NativeWindowHistoryAllOrderJointEnergy (energy mixedLoad)
open NativeWindowHistoryMeanStrainSource (fluctuation)
noncomputable section
variable {nu : Viscosity}

set_option backward.isDefEq.respectTransparency false in
theorem source_first_word_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ M (j : Coordinate) (a : ℝ) (start : a∈Icc 0 horizon)
      (t : ℝ),t∈Ioo a horizon →
      deriv (energy seed M [j] a horizon start.2) t+
        (nu.coeff/4)*gradient M (history seed M [j] t)≤
          C*energy seed M [j] a horizon start.2 t+
          2*inner ℝ (history seed M [j] t)
            (fluctuation seed M j t+operator M [j]
              (NativeWindowHistoryOseen.forcingHistory seed M t))-
          2*inner ℝ (created seed M [j] a horizon start.2 t) (load seed M [j] t) := by
  obtain ⟨A,A0,base⟩:=NativeWindowHistoryAllOrderJointControl.source_generator seed horizon
  obtain ⟨B,B0,paid⟩:=NativeWindowHistoryMeanStrainSource.source_self_load seed horizon
    (nu.coeff/4) (by positivity [nu.coeff_pos])
  refine ⟨A+2*B,by positivity,?_⟩
  intro M j a start t inside
  have time : t∈Icc 0 horizon:=⟨start.1.trans inside.1.le,inside.2.le⟩
  have initial:=base M [j] a start t inside
  rw [NativeWindowHistoryAllOrderJointEnergy.mixedLoad_original seed M [j] a horizon start.2 t
    (Ioo_subset_Icc_self inside)] at initial
  have expanded : 2*inner ℝ
      (history seed M [j] t-created seed M [j] a horizon start.2 t)
      (load seed M [j] t)=
      2*inner ℝ (history seed M [j] t) (load seed M [j] t)-
        2*inner ℝ (created seed M [j] a horizon start.2 t) (load seed M [j] t) := by
    rw [inner_sub_left]
    ring
  rw [expanded] at initial
  have strain:=paid M j t time
  have mass:=NativeWindowHistoryAllOrderJointEnergy.whole_mass seed M [j] a horizon start.2 t
  have scaled:=mul_le_mul_of_nonneg_left mass B0
  nlinarith only [initial,strain,scaled]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanStrainJoint
