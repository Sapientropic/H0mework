import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.JointEnergy

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderJointControl
open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeFiniteActionResolvent (physicalSpace pairing)
open NativeWindowTraceWholeHistory (H finiteHistory gradient)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistoryMeanBlocks (annihilation)
open NativeWindowHistoryAllOrderWord (value)
open NativeWindowHistoryAllOrderCausal (created remaining)
open NativeWindowHistoryAllOrderJointEnergy (energy dissipation mixedLoad)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

private theorem rescale (n w p g : ℝ) (positive : 0<n)
    (paid : 2*(-n⁻¹)*w ≤ (-n⁻¹)^2*p+g) : -2*w ≤ n⁻¹*p+n*g := by
  have multiplied:=mul_le_mul_of_nonneg_left paid positive.le
  have first : n*(2*(-n⁻¹)*w)= -2*w := by field_simp
  have last : n*((-n⁻¹)^2*p+g)=n⁻¹*p+n*g := by field_simp
  rwa [first,last] at multiplied

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  nu.coeff⁻¹*NativeWindowHistoryCreationSource.budget seed horizon (nu.coeff^2/2)

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0≤budget seed horizon :=
  mul_nonneg (inv_nonneg.mpr nu.coeff_pos.le)
    (NativeWindowHistoryCreationSource.budget_nonnegative seed horizon (nu.coeff^2/2) (by positivity [nu.coeff_pos]))

theorem annihilation_absorption (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ)
    (t : ℝ) (inside : t∈Icc 0 horizon) (v : physicalSpace (modes M)) (z : H) :
    2*inner ℝ (includeCLM (modes M) (modes_closed M) v) (annihilation seed M t z)≤
      (nu.coeff/2)*gradient M (embed (includeCLM (modes M) (modes_closed M) v))+
        nu.coeff*gradient M z+budget seed horizon*‖includeCLM (modes M) (modes_closed M) v‖^2 := by
  have weak:=NativeWindowHistorySchurWeakPairing.creation_young seed M t v z (-nu.coeff⁻¹)
  have paid:=rescale nu.coeff _ _ _ nu.coeff_pos weak
  have potential:=NativeWindowHistorySchurWeakPairing.source_potential_bound seed horizon (nu.coeff^2/2)
    (by positivity [nu.coeff_pos]) M t inside v
  have pair := (NativePhysicalPairing.include_inner (modes M) (modes_zero M) (modes_closed M) v
    (includeCLM (modes M) (modes_closed M) v)).trans
      (congrArg (pairing (modes M) v) (NativePhysicalPairing.restrict_include (modes M) (modes_zero M) (modes_closed M) v))
  have normed := (real_inner_self_eq_norm_sq (includeCLM (modes M) (modes_closed M) v)).symm.trans pair
  rw [← NativeWindowHistoryMeanGradient.gradient_embed M v,← normed] at potential
  have scaled:=mul_le_mul_of_nonneg_left potential (inv_nonneg.mpr nu.coeff_pos.le)
  have coefficient : nu.coeff⁻¹*(nu.coeff^2/2)=nu.coeff/2 := by field_simp
  have bounded : nu.coeff⁻¹*NativeWindowHistorySchurWeakPairing.potential seed M t v≤
      (nu.coeff/2)*gradient M (embed (includeCLM (modes M) (modes_closed M) v))+
        budget seed horizon*‖includeCLM (modes M) (modes_closed M) v‖^2 := by
    simpa only [mul_add,← mul_assoc,coefficient,budget] using scaled
  have coupled:=NativeWindowHistoryMeanBlocks.coupling_green seed M t
    (includeCLM (modes M) (modes_closed M) v) z
  linarith only [paid,bounded,coupled]

theorem value_controls (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) : ‖value seed M word t‖^2≤energy seed M word a B aB t :=
  (NativeWindowHistoryAllOrderCausalEnergy.source_controls seed M word a B aB t).trans
    (le_add_of_nonneg_right (sq_nonneg _))

set_option backward.isDefEq.respectTransparency false in
theorem source_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M (word : List Coordinate) (a : ℝ) (start : a∈Icc 0 horizon)
      (t : ℝ),t∈Ioo a horizon →
      deriv (energy seed M word a horizon start.2) t+
        (nu.coeff/2)*gradient M (NativeWindowHistorySpatialWords.history seed M word t)≤
          C*energy seed M word a horizon start.2 t+mixedLoad seed M word a horizon start.2 t := by
  refine ⟨budget seed horizon,budget_nonnegative seed horizon,?_⟩
  intro M word a start t inside
  let v:=NativeWindowStageNineWords.word (modes M) (modes_zero M) (modes_closed M) word
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) (mean (finiteHistory seed t M)))
  have original : value seed M word t=includeCLM (modes M) (modes_closed M) v := rfl
  have cross:=annihilation_absorption seed horizon M t ⟨start.1.trans inside.1.le,inside.2.le⟩ v
    (remaining seed M word a horizon start.2 t)
  rw [← original] at cross
  have actual:=((NativeWindowHistoryAllOrderJointEnergy.source_derivative seed M word a horizon start.2 t
    (Ioo_subset_Icc_self inside)).hasDerivAt (Icc_mem_nhds inside.1 inside.2)).deriv
  have lower:=mul_le_mul_of_nonneg_left (value_controls seed M word a horizon start.2 t)
    (budget_nonnegative seed horizon)
  have meanSign:=mul_nonneg nu.coeff_pos.le
    (NativeWindowHistoryMeanGradient.gradient_nonnegative seed M (embed (value seed M word t)))
  have createdSign:=mul_nonneg nu.coeff_pos.le
    (NativeWindowHistoryMeanGradient.gradient_nonnegative seed M
      (NativeWindowHistoryMeanProjection.residual (created seed M word a horizon start.2 t)))
  have reduced : deriv (energy seed M word a horizon start.2) t+
      nu.coeff*dissipation seed M word a horizon start.2 t≤
        budget seed horizon*energy seed M word a horizon start.2 t+mixedLoad seed M word a horizon start.2 t := by
    rw [actual]
    dsimp only [dissipation,NativeWindowHistoryAllOrderCausalEnergy.dissipation]
    nlinarith only [cross,lower,meanSign,createdSign]
  have whole:=mul_le_mul_of_nonneg_left
    (NativeWindowHistoryAllOrderJointEnergy.whole_gradient seed M word a horizon start.2 t (Ioo_subset_Icc_self inside))
    (show 0≤nu.coeff/2 by positivity [nu.coeff_pos])
  nlinarith only [reduced,whole]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderJointControl
