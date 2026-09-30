import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.CouplingCommutator
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianSpatial

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredCreationFirstWord
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
variable {nu : Viscosity}

private theorem laplacian_commutator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Coordinate → E →L[ℝ] E) (L A : E →L[ℝ] E)
    (square : ∀v, (∑j : Coordinate,D j (D j v))= -L v) (v : E) :
    L (A v)-A (L v)=
      -(∑j : Coordinate,(D j (((D j).comp A-A.comp (D j)) v)+
        ((D j).comp A-A.comp (D j)) (D j v))) := by
  have first : L (A v)= -(∑j : Coordinate,D j (D j (A v))) := by
    have h:=square (A v)
    exact eq_neg_of_add_eq_zero_left (by rw [h]; abel)
  have last : A (L v)= -A (∑j : Coordinate,D j (D j v)) := by
    have h : L v= -(∑j : Coordinate,D j (D j v)) := by
      simpa only [neg_neg] using (congrArg Neg.neg (square v)).symm
    rw [h,map_neg]
  rw [first,last]
  calc
    _= -(∑j : Coordinate,(D j (D j (A v))-A (D j (D j v)))) := by
      simp only [Finset.sum_sub_distrib,map_sum]
      abel
    _=_ := by
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro j _
      simp only [sub_apply,ContinuousLinearMap.comp_apply,map_sub]
      abel

set_option backward.isDefEq.respectTransparency false in
theorem source_creation_first_word (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (u : NativeWholeResolvent.wholePhysical) :
    NativeCenteredCouplingCommutator.creationCommutator seed M time u=
      -(nu.coeff • NativeWindowHistoryMeanProjection.residual
        (∑j : Coordinate,(
          NativeWindowHistorySpatialWords.operator M [j]
            (NativeWindowHistorySpatialWords.commutator seed M [j] time
              (NativeWindowHistoryMeanProjection.embed u))+
          NativeWindowHistorySpatialWords.commutator seed M [j] time
            (NativeWindowHistorySpatialWords.operator M [j]
              (NativeWindowHistoryMeanProjection.embed u))))) := by
  let D : Coordinate → H →L[ℝ] H:=fun j => NativeWindowHistoryJacobianSpatial.spatial M j
  let A:=NativeWindowHistoryOseen.action seed M time
  let L:=laplacianAction nu M
  have square : ∀v : H,(∑j : Coordinate,D j (D j v))= -L v := by
    intro v
    exact NativeWindowHistoryJacobianSpatial.spatial_square nu M v
  have source:=laplacian_commutator D L A square (NativeWindowHistoryMeanProjection.embed u)
  have original : L (A (NativeWindowHistoryMeanProjection.embed u))-
      A (L (NativeWindowHistoryMeanProjection.embed u))=
      -(∑j : Coordinate,(
        NativeWindowHistorySpatialWords.operator M [j]
          (NativeWindowHistorySpatialWords.commutator seed M [j] time
            (NativeWindowHistoryMeanProjection.embed u))+
        NativeWindowHistorySpatialWords.commutator seed M [j] time
          (NativeWindowHistorySpatialWords.operator M [j]
            (NativeWindowHistoryMeanProjection.embed u)))) := by
    simpa only [D,A,L,NativeWindowHistoryJacobianSpatial.spatial,
      NativeWindowHistorySpatialWords.commutator] using source
  calc
    _=nu.coeff • NativeWindowHistoryMeanProjection.residual
      (L (A (NativeWindowHistoryMeanProjection.embed u))-
        A (L (NativeWindowHistoryMeanProjection.embed u))) :=
      NativeCenteredCouplingCommutator.source_creation_commutator seed M time u
    _=_ := by
      have mapped:=congrArg (fun z : H => nu.coeff • NativeWindowHistoryMeanProjection.residual z) original
      simpa only [map_neg,smul_neg] using mapped

end
end SaturationMonoid.NavierStokes.NativeCenteredCreationFirstWord
