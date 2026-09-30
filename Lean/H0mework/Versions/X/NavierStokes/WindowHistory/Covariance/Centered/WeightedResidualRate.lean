import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.ActualExchange
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.Causal

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredWeightedResidualRate
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H)
open NativeWindowHistoryMeanProjection (residual)
noncomputable section
variable {nu : Viscosity}

private theorem quadratic_derivative {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E)
    (symmetric : ∀ x y,inner ℝ x (T y)=inner ℝ y (T x))
    {f : ℝ → E} {d : E} {t : ℝ} (derivative : HasDerivAt f d t) :
    HasDerivAt (fun s => inner ℝ (f s) (T (f s)))
      (2*inner ℝ (T (f t)) d) t := by
  have original:=derivative.inner ℝ (T.hasFDerivAt.comp_hasDerivAt t derivative)
  have read : inner ℝ (f t) (T d)+inner ℝ d (T (f t))=
      2*inner ℝ (T (f t)) d := by
    rw [symmetric (f t) d]
    rw [real_inner_comm (T (f t)) d]
    ring
  change HasDerivAt (fun s => inner ℝ (f s) (T (f s)))
    (inner ℝ (f t) (T d)+inner ℝ d (T (f t))) t at original
  rw [read] at original
  exact original

def centeredWord (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (j : Coordinate) (time : ℝ) : H :=
  residual (NativeWindowHistorySpatialWords.history seed M [j] time)

def energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (j : Coordinate) (time : ℝ) : ℝ :=
  inner ℝ (centeredWord seed M j time)
    (NativeWindowHistoryJacobianControl.heat nu M (centeredWord seed M j time))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem source_energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (j : Coordinate) (time : ℝ) :
    let q:=centeredWord seed M j time
    let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
    HasDerivAt (energy seed M j)
      (2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
          (NativeWindowHistoryMeanBlocks.bath seed M time q)+
        2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
          (NativeWindowHistoryMeanAction.creation seed M time u)+
        2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
          (residual (NativeWindowHistoryAllOrderCausal.load seed M [j] time))) time := by
  intro q u
  let T:=NativeWindowHistoryJacobianControl.heat nu M
  have symmetric (x y : H) : inner ℝ x (T y)=inner ℝ y (T x) :=
    NativeWindowHistoryJacobianControl.form_symmetric nu M x y
  have derivative:=NativeWindowHistoryAllOrderCausal.residual_derivative seed M [j] time
  have original:=quadratic_derivative T symmetric derivative
  change HasDerivAt (energy seed M j)
    (2*inner ℝ (T q) (NativeWindowHistoryMeanBlocks.bath seed M time q+
      NativeWindowHistoryMeanAction.creation seed M time u+
      residual (NativeWindowHistoryAllOrderCausal.load seed M [j] time))) time at original
  convert original using 1
  rw [inner_add_right,inner_add_right]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem source_joint_first_word_rate (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (j : Coordinate) :
    let h:=NativeWindowTraceWholeHistory.finiteHistory seed time M
    let w:=NativeWindowHistoryMeanProjection.mean h
    let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
    let q:=centeredWord seed M j time
    2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
        (NativeWindowHistoryAllOrderWord.retained seed M [j] time)+
      deriv (energy seed M j) time=
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
        (NativeWindowHistoryMeanBlocks.bath seed M time q)+
      2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
        (NativeWindowHistoryMeanProjection.residual
          (NativeWindowHistoryAllOrderCausal.load seed M [j] time)) := by
  intro h w u q
  have derivative:=(source_energy_hasDerivAt seed M j time).deriv
  have actual:=NativeCenteredActualExchange.source_retained_first_word_exchange seed M time j
  dsimp only at actual
  dsimp only [h,w,u,q] at *
  dsimp only [NativeWindowHistorySpatialWords.history,centeredWord] at derivative actual ⊢
  nlinarith only [derivative,actual]

end
end SaturationMonoid.NavierStokes.NativeCenteredWeightedResidualRate
