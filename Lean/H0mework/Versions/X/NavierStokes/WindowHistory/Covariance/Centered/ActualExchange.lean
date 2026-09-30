import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.FirstWordWeakAction

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredActualExchange
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H)
open NativeWindowHistoryMeanProjection (mean residual)
open NativeWindowHistorySpatialWords (fiber operator commutator)
noncomputable section
variable {nu : Viscosity}

set_option backward.isDefEq.respectTransparency false in
theorem source_annihilation_first_word (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (j : Coordinate) (v : H) :
    fiber M [j] (NativeWindowHistoryMeanBlocks.annihilation seed M time v)=
      NativeWindowHistoryMeanBlocks.annihilation seed M time (operator M [j] v)+
        mean (commutator seed M [j] time (residual v)) := by
  let D:=fiber M [j]
  let d:=operator M [j]
  let A:=NativeWindowHistoryOseen.action seed M time
  let Q:=NativeWindowHistoryMeanProjection.residual
  have meanD (w : H) : D (mean w)=mean (d w) :=
    (NativeWindowHistoryMeanProjection.mean_comp D w).symm
  have commuteQ : d (Q v)=Q (d v) :=
    (NativeWindowHistoryMeanProjection.residual_comp D v).symm
  change D (mean (A (Q v)))=mean (A (Q (d v)))+mean (commutator seed M [j] time (Q v))
  calc
    _=mean (d (A (Q v))) := meanD _
    _=mean (A (d (Q v))+commutator seed M [j] time (Q v)) := by
      congr 1
      simp only [NativeWindowHistorySpatialWords.commutator,sub_apply,ContinuousLinearMap.comp_apply]
      abel
    _=mean (A (Q (d v))+commutator seed M [j] time (Q v)) :=
      congrArg (fun z : H => mean (A z+commutator seed M [j] time (Q v))) commuteQ
    _=_ := map_add mean _ _

set_option backward.isDefEq.respectTransparency false in
theorem source_actual_first_word_exchange (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (j : Coordinate) :
    let h:=NativeWindowTraceWholeHistory.finiteHistory seed time M
    let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
    let q:=residual (operator M [j] h)
    2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
        (fiber M [j] (NativeWindowHistoryMeanResidualLoad.residualLoad seed M time))+
      2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
        (NativeWindowHistoryMeanAction.creation seed M time u)=
      2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
        (fiber M [j] (mean (NativeWindowHistoryOseen.forcingHistory seed M time)))+
      2*inner ℝ q (NativeCenteredCouplingCommutator.creationCommutator seed M time u)+
      2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
        (mean (commutator seed M [j] time (residual h))) := by
  intro h u q
  let D:=fiber M [j]
  let W:=NativeWindowHistoryAllOrderPrincipal.weight nu M u
  let F:=mean (NativeWindowHistoryOseen.forcingHistory seed M time)
  let A:=NativeWindowHistoryMeanBlocks.annihilation seed M time
  let B:=mean (commutator seed M [j] time (residual h))
  have qSq : residual q=q:=NativeWindowHistoryBathResolvent.residual_square _
  have annihilationRead : A (operator M [j] h)=A q := by
    change mean (NativeWindowHistoryOseen.action seed M time (residual (operator M [j] h)))=
      mean (NativeWindowHistoryOseen.action seed M time (residual q))
    exact (congrArg (fun z : H => mean (NativeWindowHistoryOseen.action seed M time z)) qSq).symm
  have split : D (NativeWindowHistoryMeanResidualLoad.residualLoad seed M time)=D F+A q+B := by
    have read:=source_annihilation_first_word seed M time j h
    calc
      _=D (F+A h) := rfl
      _=D F+D (A h) := map_add D F (A h)
      _=D F+(A (operator M [j] h)+B) := congrArg (fun z : NativeWholeResolvent.wholePhysical => D F+z) read
      _=_ := by rw [annihilationRead]; abel
  have paired:=NativeCenteredCouplingCommutator.source_coupling_commutator seed M time u q
  change 2*inner ℝ W (D (NativeWindowHistoryMeanResidualLoad.residualLoad seed M time))+
      2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
        (NativeWindowHistoryMeanAction.creation seed M time u)=
    2*inner ℝ W (D F)+2*inner ℝ q
      (NativeCenteredCouplingCommutator.creationCommutator seed M time u)+2*inner ℝ W B
  calc
    _=2*inner ℝ W (D F+A q+B)+
        2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
          (NativeWindowHistoryMeanAction.creation seed M time u) :=
      congrArg (fun z : NativeWholeResolvent.wholePhysical =>
        2*inner ℝ W z+2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
          (NativeWindowHistoryMeanAction.creation seed M time u)) split
    _=_ := by
      simp only [inner_add_right]
      nlinarith only [paired]

set_option backward.isDefEq.respectTransparency false in
theorem source_retained_first_word_exchange (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (j : Coordinate) :
    let h:=NativeWindowTraceWholeHistory.finiteHistory seed time M
    let w:=mean h
    let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
    let q:=residual (operator M [j] h)
    2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
        (NativeWindowHistoryAllOrderWord.retained seed M [j] time)+
      2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
        (NativeWindowHistoryMeanAction.creation seed M time u)=
      2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
        (fiber M [j] (NativeWindowHistoryMeanAction.meanOperator seed M time w)-
          NativeWindowHistorySchurAction.effective seed M time u)+
      2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
        (fiber M [j] (mean (NativeWindowHistoryOseen.forcingHistory seed M time)))+
      2*inner ℝ q (NativeCenteredCouplingCommutator.creationCommutator seed M time u)+
      2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
        (mean (commutator seed M [j] time (residual h))) := by
  intro h w u q
  let W:=NativeWindowHistoryAllOrderPrincipal.weight nu M u
  let T:=fiber M [j] (NativeWindowHistoryMeanAction.meanOperator seed M time w)-
    NativeWindowHistorySchurAction.effective seed M time u
  let R:=fiber M [j] (NativeWindowHistoryMeanResidualLoad.residualLoad seed M time)
  have split : NativeWindowHistoryAllOrderWord.retained seed M [j] time=T+R := by
    have source:=NativeCenteredWorkResidual.source_retained_original seed M [j] time
    dsimp only at source
    rw [source,map_add]
    dsimp only [T,R]
    abel
  have actual:=source_actual_first_word_exchange seed M time j
  dsimp only at actual
  change 2*inner ℝ W R+2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
    (NativeWindowHistoryMeanAction.creation seed M time u)=_
      at actual
  calc
    _=2*inner ℝ W (T+R)+
        2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
          (NativeWindowHistoryMeanAction.creation seed M time u) :=
      congrArg (fun z : NativeWholeResolvent.wholePhysical =>
        2*inner ℝ W z+2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
          (NativeWindowHistoryMeanAction.creation seed M time u)) split
    _=2*inner ℝ W T+(2*inner ℝ W R+
        2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
          (NativeWindowHistoryMeanAction.creation seed M time u)) := by
      rw [inner_add_right]
      ring
    _=_ := by
      have shifted:=congrArg (fun z : ℝ => 2*inner ℝ W T+z) actual
      convert shifted using 1; ring

end
end SaturationMonoid.NavierStokes.NativeCenteredActualExchange
