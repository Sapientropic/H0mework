import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.JointMeanPaid

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredJointAggregate
open Set
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryMeanProjection (mean residual)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {nu : Viscosity}

def remainingAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (time : ℝ) (j : Coordinate) : ℝ :=
  let h:=finiteHistory seed time M
  let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
  let q:=NativeCenteredWeightedResidualRate.centeredWord seed M j time
  2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
    (NativeWindowHistorySpatialWords.fiber M [j]
      (mean (NativeWindowHistoryOseen.forcingHistory seed M time)))+
  2*inner ℝ q (NativeCenteredCouplingCommutator.creationCommutator seed M time u)+
  2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
    (mean (NativeWindowHistorySpatialWords.commutator seed M [j] time (residual h)))+
  2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
    (residual (NativeWindowHistoryAllOrderCausal.load seed M [j] time))+
  2*nu.coeff*inner ℝ (laplacianAction nu M q)
    (NativeWindowHistorySchurAdvectorAction.wAction seed M time q)

private theorem one_sum (F : List Coordinate → ℝ) :
    (∑word : FixedMatterSpatialWordIndex 1,F word.toList)=F []+∑j : Coordinate,F [j] := by
  simp [FixedMatterSpatialWordIndex,FixedMatterSpatialWordIndex.toList,Fintype.sum_sigma,
    Fin.sum_univ_succ]
  let e : (Fin 1 → Coordinate) ≃ Coordinate := {
    toFun := fun f => f 0
    invFun := fun j _ => j
    left_inv := by intro f; funext i; fin_cases i; rfl
    right_inv := by intro j; rfl }
  simpa [Fin.sum_univ_succ] using
    Fintype.sum_equiv e (fun x => F [x 0]) (fun j => F [j]) (by intro; rfl)

theorem work_one_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistoryAllOrderSpatial.work seed M 1 time=
      2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M
        (NativeWindowHistoryAllOrderWord.value seed M [] time))
        (NativeWindowHistoryAllOrderWord.retained seed M [] time)+
      ∑j : Coordinate,2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M
        (NativeWindowHistoryAllOrderWord.value seed M [j] time))
          (NativeWindowHistoryAllOrderWord.retained seed M [j] time) := by
  exact one_sum (fun word =>
    2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M
      (NativeWindowHistoryAllOrderWord.value seed M word time))
      (NativeWindowHistoryAllOrderWord.retained seed M word time))

theorem dissipation_one_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (time : ℝ) :
    NativeWindowHistoryAllOrderSpatial.dissipation seed M 1 time=
      ‖laplacianFiber nu M (mean (finiteHistory seed time M))‖^2+
      ∑j : Coordinate,
        ‖laplacianFiber nu M (NativeWindowHistoryAllOrderWord.value seed M [j] time)‖^2 := by
  have split:=one_sum (fun word =>
    ‖laplacianFiber nu M (NativeWindowHistoryAllOrderWord.value seed M word time)‖^2)
  change NativeWindowHistoryAllOrderSpatial.dissipation seed M 1 time=_ at split
  rw [split]
  have zero : NativeWindowHistoryAllOrderWord.value seed M [] time=
      mean (finiteHistory seed time M) :=
    NativeWindowHistoryMeanPhysicalJet.include_mean seed M time
  rw [zero]

def energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  NativeWindowHistoryAllOrderSpatial.energy seed M 1 time+
    ∑j : Coordinate,NativeCenteredWeightedResidualRate.energy seed M j time

theorem energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (time : ℝ) :
    HasDerivAt (energy seed M)
      (deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time+
        ∑j : Coordinate,deriv (NativeCenteredWeightedResidualRate.energy seed M j) time) time := by
  have first:=NativeWindowHistoryAllOrderSpatial.source_hasDerivAt seed M 1 time
  have first' : HasDerivAt (NativeWindowHistoryAllOrderSpatial.energy seed M 1)
      (deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time) time := by
    rw [first.deriv]
    exact first
  have second : HasDerivAt
      (fun t => ∑j : Coordinate,NativeCenteredWeightedResidualRate.energy seed M j t)
      (∑j : Coordinate,deriv (NativeCenteredWeightedResidualRate.energy seed M j) time) time := by
    have each (j : Coordinate) : HasDerivAt
        (NativeCenteredWeightedResidualRate.energy seed M j)
        (deriv (NativeCenteredWeightedResidualRate.energy seed M j) time) time := by
      have derivative:=NativeCenteredWeightedResidualRate.source_energy_hasDerivAt seed M j time
      rw [derivative.deriv]
      exact derivative
    have raw:=HasDerivAt.sum (u := (Finset.univ : Finset Coordinate)) (fun j _ => each j)
    have read : (∑j : Coordinate,NativeCenteredWeightedResidualRate.energy seed M j)=
        fun t => ∑j : Coordinate,NativeCenteredWeightedResidualRate.energy seed M j t := by
      funext t
      simp only [Finset.sum_apply]
    rw [read] at raw
    exact raw
  have read : energy seed M=
      NativeWindowHistoryAllOrderSpatial.energy seed M 1+
        fun t => ∑j : Coordinate,NativeCenteredWeightedResidualRate.energy seed M j t := by
    funext t
    rfl
  rw [read]
  exact first'.add second

set_option maxHeartbeats 1200000 in
theorem source_joint_positive_budget (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃r C : ℝ,0<r ∧0≤C ∧∀M≥low,∀time∈Icc 0 horizon,
      let w:=mean (finiteHistory seed time M)
      (nu.coeff^2/32)*‖laplacianFiber nu M w‖^4+
        nu.coeff^2*‖laplacianFiber nu M w‖^2+
        (3*nu.coeff^2/4)*(∑j : Coordinate,
          ‖laplacianFiber nu M
            (NativeWindowHistoryAllOrderWord.value seed M [j] time)‖^2)+
        r*deriv (energy seed M) time+
        (r*nu.coeff^2/2)*(∑j : Coordinate,
          ‖laplacianAction nu M
            (NativeCenteredWeightedResidualRate.centeredWord seed M j time)‖^2)≤
        r*(2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M
          (NativeWindowHistoryAllOrderWord.value seed M [] time))
            (NativeWindowHistoryAllOrderWord.retained seed M [] time))+
        r*(∑j : Coordinate,remainingAction seed M time j)+C := by
  obtain ⟨one,r,D,r0,D0,gate⟩:=
    NativeCenteredEnergyAbsorption.source_quartic_dissipation_gate seed horizon
  let epsilon:=nu.coeff^2/(4*r)
  have epsilon0 : 0<epsilon:=by dsimp only [epsilon]; positivity [nu.coeff_pos]
  obtain ⟨two,B,B0,joint⟩:=
    NativeCenteredJointMeanPaid.source_joint_first_word_mean_paid
      seed horizon nonnegative epsilon epsilon0
  let C:=D+3*r*B
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨max one two,r,C,r0,C0,fun M above time inside => ?_⟩
  let w:=mean (finiteHistory seed time M)
  let work (j : Coordinate) :=
    2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M
      (NativeWindowHistoryAllOrderWord.value seed M [j] time))
        (NativeWindowHistoryAllOrderWord.retained seed M [j] time)
  let wcost (j : Coordinate) :=
    ‖laplacianFiber nu M (NativeWindowHistoryAllOrderWord.value seed M [j] time)‖^2
  let qrate (j : Coordinate) :=
    deriv (NativeCenteredWeightedResidualRate.energy seed M j) time
  let qcost (j : Coordinate) :=
    ‖laplacianAction nu M (NativeCenteredWeightedResidualRate.centeredWord seed M j time)‖^2
  let rest (j : Coordinate) := remainingAction seed M time j
  have row (j : Coordinate) :
      work j+qrate j+(nu.coeff^2/2)*qcost j≤
        epsilon*wcost j+rest j+B := by
    have paid:=joint M ((le_max_right _ _).trans above) time inside j
    dsimp only [work,qrate,qcost,wcost,rest,remainingAction]
    convert paid using 1
    ring
  have summed:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate))
    (fun j _ => row j)
  have constant : (∑_j : Coordinate,B)=3*B := by
    simp
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,constant] at summed
  have original:=gate M ((le_max_left _ _).trans above) time inside
  dsimp only at original
  rw [dissipation_one_split,work_one_split] at original
  change (nu.coeff^2/32)*‖laplacianFiber nu M w‖^4+
      nu.coeff^2*(‖laplacianFiber nu M w‖^2+∑j : Coordinate,wcost j)+
      r*deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time≤
        r*(2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M
          (NativeWindowHistoryAllOrderWord.value seed M [] time))
            (NativeWindowHistoryAllOrderWord.retained seed M [] time)+
          ∑j : Coordinate,work j)+D at original
  have scaled:=mul_le_mul_of_nonneg_left summed r0.le
  have coefficient : r*epsilon=nu.coeff^2/4 := by
    dsimp only [epsilon]
    field_simp [r0.ne']
  dsimp only [work,wcost,qrate,qcost,rest,w,C] at *
  have coefficientCost := congrArg (fun x : ℝ =>
    x*(∑j : Coordinate,
      ‖laplacianFiber nu M (NativeWindowHistoryAllOrderWord.value seed M [j] time)‖^2)) coefficient
  rw [mul_assoc] at coefficientCost
  simp only [mul_add] at scaled
  rw [coefficientCost] at scaled
  rw [(energy_hasDerivAt seed M time).deriv]
  nlinarith only [original,scaled]

end
end SaturationMonoid.NavierStokes.NativeCenteredJointAggregate
