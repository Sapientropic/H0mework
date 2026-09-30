import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.AllWordRate
set_option autoImplicit false
open scoped BigOperators Topology
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
namespace SaturationMonoid.NavierStokes.NativeCenteredWordMass
open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (includeCLM include_norm)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryMeanProjection (mean)
noncomputable section
variable {nu : Viscosity}

private theorem one_sum (F : List (Fin 3) → ℝ) :
    (∑ word : FixedMatterSpatialWordIndex 1,F word.toList)=F []+∑j : Fin 3,F [j] := by
  simp [FixedMatterSpatialWordIndex,FixedMatterSpatialWordIndex.toList,Fintype.sum_sigma,
    Fin.sum_univ_succ]
  let e : (Fin 1 → Fin 3) ≃ Fin 3 := {
    toFun := fun f => f 0
    invFun := fun j _ => j
    left_inv := by intro f; funext i; fin_cases i; rfl
    right_inv := by intro j; rfl }
  simpa [Fin.sum_univ_succ] using
    Fintype.sum_equiv e (fun x => F [x 0]) (fun j => F [j]) (by intro; rfl)

theorem source_word_one_mass (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    let w := mean (finiteHistory seed time M)
    NativeWindowHistoryAllOrderWord.energy seed M 1 time =
      ‖w‖^2+NativeCommonAdvectorAction.curlPair (modes M)
        (NativeWholeH1Mixed.restrict M w).1 (NativeWholeH1Mixed.restrict M w).1 := by
  intro w
  let v:=NativeWholeH1Mixed.restrict M w
  let F : List Coordinate → ℝ := fun word =>
    ‖NativeWindowHistoryAllOrderWord.value seed M word time‖^2
  have zero : F []=‖w‖^2 := by
    have empty : NativeWindowHistoryAllOrderWord.value seed M [] time=w :=
      NativeWindowHistoryMeanPhysicalJet.include_mean seed M time
    exact congrArg (fun z => ‖z‖^2) empty
  have first : (∑j : Coordinate,F [j])=
      NativeCommonAdvectorAction.curlPair (modes M) v.1 v.1 := by
    rw [← NativeWindowHistoryCreationGeometry.derivative_mass
      (modes M) (modes_zero M) (modes_closed M) v]
    apply Finset.sum_congr rfl
    intro j _
    have actual : F [j]=‖NativeWindowHistorySpatialWords.fiber M [j] w‖^2 := rfl
    rw [actual,NativeWindowHistoryJacobianSpatial.fiber_original]
    rw [include_norm (modes M) (modes_zero M) (modes_closed M)]
    exact (real_inner_self_eq_norm_sq _).symm
  calc
    NativeWindowHistoryAllOrderWord.energy seed M 1 time=F []+∑j : Coordinate,F [j] :=
      one_sum F
    _=‖w‖^2+NativeCommonAdvectorAction.curlPair (modes M) v.1 v.1 := by rw [zero,first]

theorem source_word_one_energy_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →
      NativeWindowHistoryAllOrderWord.energy seed M 1 time≤C := by
  let C:=max 0 (NativeForwardWindowJets.budget seed 0^2+
    NativeWindowAugmentedPayment.graphBudget seed 0 horizon)
  refine ⟨C,le_max_left _ _,fun M time inside => ?_⟩
  let w:=mean (finiteHistory seed time M)
  let v:=NativeWindowHistoryMeanGradient.meanValue M (finiteHistory seed time M)
  have mass : ‖w‖≤NativeForwardWindowJets.budget seed 0 := by
    change ‖w.1‖≤_
    rw [NativeWindowHistoryMeanTime.source_mean]
    exact NativeWindowHistoryMeanTime.jet_bound seed M 0 time
  have massSq:=pow_le_pow_left₀ (norm_nonneg _) mass 2
  have gradient:=NativeWindowHistoryMeanGradient.source_mean_budget seed horizon M time inside
  have identity:=source_word_one_mass seed M time
  dsimp only at identity
  change NativeWindowHistoryAllOrderWord.energy seed M 1 time≤C
  rw [identity]
  exact (add_le_add massSq gradient).trans (le_max_right _ _)

end
end SaturationMonoid.NavierStokes.NativeCenteredWordMass
