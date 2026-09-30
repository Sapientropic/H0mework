import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.CreationFirstWord

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredFirstWordWeakAction
open Set
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H)
noncomputable section
variable {nu : Viscosity}

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem source_creation_first_word_pair (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (u : NativeWholeResolvent.wholePhysical) (q : H)
    (centered : NativeWindowHistoryMeanProjection.residual q=q) :
    inner ℝ q (NativeCenteredCouplingCommutator.creationCommutator seed M time u)=
      nu.coeff*(∑j : Coordinate,(
        inner ℝ (NativeWindowHistorySpatialWords.operator M [j] q)
          (NativeWindowHistorySpatialWords.commutator seed M [j] time
            (NativeWindowHistoryMeanProjection.embed u))-
        inner ℝ q (NativeWindowHistorySpatialWords.commutator seed M [j] time
          (NativeWindowHistorySpatialWords.operator M [j]
            (NativeWindowHistoryMeanProjection.embed u))))) := by
  let F : Coordinate → H := fun j =>
    NativeWindowHistorySpatialWords.commutator seed M [j] time
      (NativeWindowHistoryMeanProjection.embed u)
  let G : Coordinate → H := fun j =>
    NativeWindowHistorySpatialWords.commutator seed M [j] time
      (NativeWindowHistorySpatialWords.operator M [j]
        (NativeWindowHistoryMeanProjection.embed u))
  have projection (z : H) : inner ℝ q (NativeWindowHistoryMeanProjection.residual z)=
      inner ℝ q z := by
    have sym:=NativeWindowHistoryMeanProjection.residual_symmetric q z
    rw [centered] at sym
    exact sym.symm
  have skew (j : Coordinate) : inner ℝ q
      (NativeWindowHistorySpatialWords.operator M [j] (F j))=
        -inner ℝ (NativeWindowHistorySpatialWords.operator M [j] q) (F j) := by
    have actual:=NativeWindowHistoryJacobianSpatial.spatial_skew M j q (F j)
    change inner ℝ (NativeWindowHistorySpatialWords.operator M [j] q) (F j)=
      -inner ℝ q (NativeWindowHistorySpatialWords.operator M [j] (F j)) at actual
    linarith only [actual]
  rw [NativeCenteredCreationFirstWord.source_creation_first_word]
  simp only [inner_neg_right,real_inner_smul_right,projection,
    inner_sum,inner_add_right,Finset.sum_add_distrib,Finset.mul_sum]
  simp only [F] at skew
  simp_rw [skew]
  simp only [Finset.sum_sub_distrib,Finset.sum_neg_distrib,← Finset.mul_sum]
  ring

theorem source_original_centered_first_word_pair (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (j : Coordinate) :
    let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
    let q:=NativeWindowHistoryMeanProjection.residual
      (NativeWindowHistorySpatialWords.history seed M [j] time)
    inner ℝ q (NativeCenteredCouplingCommutator.creationCommutator seed M time u)=
      nu.coeff*(∑k : Coordinate,(
        inner ℝ (NativeWindowHistorySpatialWords.operator M [k] q)
          (NativeWindowHistorySpatialWords.commutator seed M [k] time
            (NativeWindowHistoryMeanProjection.embed u))-
        inner ℝ q (NativeWindowHistorySpatialWords.commutator seed M [k] time
          (NativeWindowHistorySpatialWords.operator M [k]
            (NativeWindowHistoryMeanProjection.embed u))))) := by
  intro u q
  have centered : NativeWindowHistoryMeanProjection.residual q=q :=
    NativeWindowHistoryBathResolvent.residual_square _
  exact source_creation_first_word_pair seed M time u q centered

theorem source_original_W_first_leg_bound (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    let h:=NativeWindowTraceWholeHistory.finiteHistory seed time M
    let q:=NativeWindowHistoryMeanProjection.residual h
    let l:=NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
      (NativeWindowHistoryMeanProjection.mean h)
    (∑j : Coordinate,inner ℝ (NativeWindowHistorySpatialWords.operator M [j] q)
      (NativeWindowHistorySpatialWords.commutator seed M [j] time
        (NativeWindowHistoryMeanProjection.embed l)))≤
      Real.sqrt (NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon)*
        Real.sqrt (∑j : Coordinate,‖NativeWindowHistorySpatialWords.commutator seed M [j] time
          (NativeWindowHistoryMeanProjection.embed l)‖^2) := by
  intro h q l
  let G:=NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon
  let B : Coordinate → H:=fun j => NativeWindowHistorySpatialWords.commutator seed M [j] time
    (NativeWindowHistoryMeanProjection.embed l)
  have source:=NativeWindowHistoryJacobianSpatial.mass_gradient nu M q
  have residualBound:=NativeWindowHistoryMeanGradient.gradient_residual_le seed M h
  have original:=NativeWindowHistorySchurTemporalControl.source_gradient seed horizon M time inside
  have gradient : (∑j : Coordinate,‖NativeWindowHistorySpatialWords.operator M [j] q‖^2)≤G := by
    change (∑j : Coordinate,‖NativeWindowHistoryJacobianSpatial.spatial M j q‖^2)≤G
    rw [source]
    exact residualBound.trans original
  have first:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate))
    (fun j _ => real_inner_le_norm (NativeWindowHistorySpatialWords.operator M [j] q) (B j))
  have cs:=Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset Coordinate)
    (fun j => ‖NativeWindowHistorySpatialWords.operator M [j] q‖)
    (fun j => ‖B j‖)
  have sqrtGradient:=Real.sqrt_le_sqrt gradient
  have scaled : Real.sqrt (∑j : Coordinate,‖NativeWindowHistorySpatialWords.operator M [j] q‖^2)*
      Real.sqrt (∑j : Coordinate,‖B j‖^2)≤
        Real.sqrt G*Real.sqrt (∑j : Coordinate,‖B j‖^2) :=
    mul_le_mul_of_nonneg_right sqrtGradient (Real.sqrt_nonneg _)
  change (∑j : Coordinate,inner ℝ (NativeWindowHistorySpatialWords.operator M [j] q) (B j))≤
    Real.sqrt G*Real.sqrt (∑j : Coordinate,‖B j‖^2)
  exact first.trans (cs.trans scaled)

end
end SaturationMonoid.NavierStokes.NativeCenteredFirstWordWeakAction
