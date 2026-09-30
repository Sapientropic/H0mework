import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.Potential
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.Spatial

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeCenteredAllWordRate
open Set MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (includeCLM include_norm)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
open PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy (FixedMatterSpatialWordIndex)
noncomputable section
variable {nu : Viscosity}

private theorem included_square (M : ℕ) (v : NativeFiniteActionResolvent.physicalSpace (modes M)) :
    ‖includeCLM (modes M) (modes_closed M) v‖^2=
      NativeFiniteActionResolvent.pairing (modes M) v v := by
  rw [include_norm (modes M) (modes_zero M) (modes_closed M)]
  exact (real_inner_self_eq_norm_sq _).symm

theorem source_curl_first_word (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    let l:=laplacianFiber nu M (mean (finiteHistory seed time M))
    let v:=NativeWholeH1Mixed.restrict M l
    NativeCommonAdvectorAction.curlPair (modes M) v.1 v.1=
      ∑j : Coordinate,‖laplacianFiber nu M
        (NativeWindowHistoryAllOrderWord.value seed M [j] time)‖^2 := by
  intro l v
  rw [← NativeWindowHistoryCreationGeometry.derivative_mass (modes M) (modes_zero M) (modes_closed M) v]
  apply Finset.sum_congr rfl
  intro j _
  have same : laplacianFiber nu M (NativeWindowHistoryAllOrderWord.value seed M [j] time)=
      includeCLM (modes M) (modes_closed M)
        (NativeWindowAugmentedGradient.derivative (modes M) (modes_zero M) (modes_closed M) j v) := by
    change laplacianFiber nu M (NativeWindowHistorySpatialWords.fiber M [j]
      (mean (finiteHistory seed time M)))=_
    rw [← NativeWindowHistoryJacobianSpatial.fiber_commute]
    exact NativeWindowHistoryJacobianSpatial.fiber_original M j l
  rw [same,included_square]

theorem source_curl_le_allWord_one (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    let l:=laplacianFiber nu M (mean (finiteHistory seed time M))
    let v:=NativeWholeH1Mixed.restrict M l
    NativeCommonAdvectorAction.curlPair (modes M) v.1 v.1≤
      NativeWindowHistoryAllOrderSpatial.dissipation seed M 1 time := by
  classical
  intro l v
  let e : Coordinate→FixedMatterSpatialWordIndex 1 := fun j =>
    ⟨⟨1,by decide⟩,fun _ => j⟩
  have toList (j : Coordinate) : (e j).toList=[j] := by rfl
  have injective : Function.Injective e := by
    intro i j equal
    have same : [i]=[j] := by
      simpa only [toList] using congrArg FixedMatterSpatialWordIndex.toList equal
    simpa using same
  let F : FixedMatterSpatialWordIndex 1 → ℝ :=
    fun word => ‖laplacianFiber nu M
      (NativeWindowHistoryAllOrderWord.value seed M word.toList time)‖^2
  have subset : Finset.univ.image e⊆(Finset.univ : Finset (FixedMatterSpatialWordIndex 1)) :=
    Finset.subset_univ _
  have bound := Finset.sum_le_sum_of_subset_of_nonneg subset
    (fun word _ _ => sq_nonneg ‖laplacianFiber nu M
      (NativeWindowHistoryAllOrderWord.value seed M word.toList time)‖)
  have first : (∑j : Coordinate,‖laplacianFiber nu M
      (NativeWindowHistoryAllOrderWord.value seed M [j] time)‖^2)≤
        NativeWindowHistoryAllOrderSpatial.dissipation seed M 1 time := by
    simpa only [F,NativeWindowHistoryAllOrderSpatial.dissipation,
      Finset.sum_image (s:=Finset.univ) injective.injOn,
      toList] using bound
  exact (source_curl_first_word seed M time).trans_le first

theorem source_centeredWCost_allWord_one (seed : GeneratedWholeRestartCurrent nu)
    (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →
      let l:=laplacianFiber nu M (mean (finiteHistory seed time M))
      NativeCenteredCovariance.centeredWCost seed M time≤
        epsilon*NativeWindowHistoryAllOrderSpatial.dissipation seed M 1 time+
          C*‖l‖^2 := by
  obtain ⟨C,C0,form⟩:=NativeCenteredPotential.source_centeredWCost_form_bound
    seed horizon epsilon positive
  refine ⟨C,C0,fun M time inside => ?_⟩
  dsimp only
  let l:=laplacianFiber nu M (mean (finiteHistory seed time M))
  let v:=NativeWholeH1Mixed.restrict M l
  have source:=form M time inside
  dsimp only at source
  have curl:=source_curl_le_allWord_one seed M time
  dsimp only at curl
  have mass : NativeFiniteActionResolvent.pairing (modes M) v v≤‖l‖^2 := by
    change inner ℝ (NativeFiniteActionResolvent.coefficients (modes M) v)
      (NativeFiniteActionResolvent.coefficients (modes M) v)≤‖l‖^2
    rw [real_inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (NativeWholeResolvent.restrict_energy (modes M) (modes_zero M) (modes_closed M) l) 2
  exact source.trans (add_le_add (mul_le_mul_of_nonneg_left curl positive.le)
    (mul_le_mul_of_nonneg_left mass C0))

theorem source_centeredWCost_allWord_rate (seed : GeneratedWholeRestartCurrent nu)
    (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃A C : ℝ,0≤A ∧0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →
      let l:=laplacianFiber nu M (mean (finiteHistory seed time M))
      NativeCenteredCovariance.centeredWCost seed M time+
        (epsilon/nu.coeff^2)*deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time≤
          (epsilon/nu.coeff^2)*
            (A*NativeWindowHistoryAllOrderWord.energy seed M 1 time+
              NativeWindowHistoryAllOrderSpatial.work seed M 1 time)+C*‖l‖^2 := by
  obtain ⟨C,C0,form⟩:=source_centeredWCost_allWord_one seed horizon epsilon positive
  obtain ⟨A,A0,generator⟩:=NativeWindowHistoryAllOrderSpatial.source_generator seed horizon
  refine ⟨A,C,A0,C0,fun M time inside => ?_⟩
  let d:=epsilon/nu.coeff^2
  have d0 : 0≤d:=div_nonneg positive.le (sq_nonneg _)
  have scale : d*nu.coeff^2=epsilon := by
    dsimp only [d]
    field_simp [nu.coeff_pos.ne']
  have scaled:=mul_le_mul_of_nonneg_left (generator M 1 time inside) d0
  let l:=laplacianFiber nu M (mean (finiteHistory seed time M))
  have paid:=form M time inside
  dsimp only at paid
  change NativeCenteredCovariance.centeredWCost seed M time+
    d*deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time≤
      d*(A*NativeWindowHistoryAllOrderWord.energy seed M 1 time+
        NativeWindowHistoryAllOrderSpatial.work seed M 1 time)+C*‖l‖^2
  calc
    _≤epsilon*NativeWindowHistoryAllOrderSpatial.dissipation seed M 1 time+C*‖l‖^2+
        d*deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time :=
      add_le_add_left paid _
    _=d*(deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time+
        nu.coeff^2*NativeWindowHistoryAllOrderSpatial.dissipation seed M 1 time)+C*‖l‖^2 := by
      rw [mul_add,← mul_assoc,scale]
      ring
    _≤_ := add_le_add_left scaled _

end
end SaturationMonoid.NavierStokes.NativeCenteredAllWordRate
