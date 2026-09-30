import H0mework.Versions.X.NavierStokes.WindowSchurMean.ResidualRead

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanResidualCost
open Set MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
noncomputable section
variable {nu : Viscosity}

theorem pair_absorb {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (a : ℝ) (apos : 0<a) :
    inner ℝ u v≤(a/4)*‖u‖^2+a⁻¹*‖v‖^2 := by
  have paired:=real_inner_le_norm u v
  have square:=sq_nonneg ((a/2)*‖u‖-‖v‖)
  have young : a*(‖u‖*‖v‖)≤(a^2/4)*‖u‖^2+‖v‖^2 := by
    nlinarith only [square]
  apply (mul_le_mul_iff_left₀ apos).mp
  calc
    (inner ℝ u v)*a≤(‖u‖*‖v‖)*a := mul_le_mul_of_nonneg_right paired apos.le
    _≤(a^2/4)*‖u‖^2+‖v‖^2 := by simpa only [mul_comm] using young
    _=((a/4)*‖u‖^2+a⁻¹*‖v‖^2)*a := by field_simp

theorem source_mean_residual_cost (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) :
    ∃C : ℝ,0≤C ∧∀M (t : ℝ),t∈Icc 0 horizon →
      (nu.coeff/2)*‖laplacianFiber nu M (mean (finiteHistory seed t M))‖^2≤
        inner ℝ (laplacianFiber nu M (mean (finiteHistory seed t M)))
          (NativeWindowHistoryMeanResidualLoad.residualLoad seed M t)+C := by
  let D:=NativeWindowHistoryMeanResidualLoad.driftBudget seed 0 horizon
  let R:=NativeForwardWindowJets.budget seed 1
  let C:=max 0 ((D+R^2)/nu.coeff)
  refine ⟨C,le_max_left _ _,fun M t inside => ?_⟩
  let h:=finiteHistory seed t M
  let w:=mean h
  let l:=laplacianFiber nu M w
  let rate:=mean (NativeWindowHistoryOseen.rateHistory seed M t)
  let drift:=NativeWindowHistoryMeanDrift.drift seed M t w
  let forcing:=NativeWindowHistoryMeanResidualLoad.residualLoad seed M t
  have equation : rate+nu.coeff • l=drift+forcing :=
    NativeWindowHistoryMeanResidualLoad.source_mean_balance seed M t
  have driftBound : ‖drift‖^2≤D := by
    have paid:=NativeWindowHistoryMeanResidualLoad.source_drift_jet seed 0 horizon M t inside
    rw [NativeWindowHistoryMeanResidualLoad.include_zero] at paid
    exact paid
  have rateBound : ‖rate‖^2≤R^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (NativeWindowHistoryMeanTime.source_rate_bound seed M t) 2
  have first:=pair_absorb l drift nu.coeff nu.coeff_pos
  have second:=pair_absorb l (-rate) nu.coeff nu.coeff_pos
  rw [norm_neg,inner_neg_right] at second
  have tested:=congrArg (inner ℝ l) equation
  rw [inner_add_right (𝕜:=ℝ) (E:=NativeWholeResolvent.wholePhysical) l rate (nu.coeff • l),
    inner_add_right (𝕜:=ℝ) (E:=NativeWholeResolvent.wholePhysical) l drift forcing,
    real_inner_smul_right l l nu.coeff,real_inner_self_eq_norm_sq] at tested
  have inv0 : 0≤nu.coeff⁻¹:=inv_nonneg.mpr nu.coeff_pos.le
  have driftPaid:=mul_le_mul_of_nonneg_left driftBound inv0
  have ratePaid:=mul_le_mul_of_nonneg_left rateBound inv0
  have payment : nu.coeff*‖l‖^2≤
      inner ℝ l forcing+(nu.coeff/2)*‖l‖^2+nu.coeff⁻¹*(D+R^2) := by
    nlinarith only [tested,first,second,driftPaid,ratePaid]
  have final : (nu.coeff/2)*‖l‖^2 ≤ inner ℝ l forcing+(D+R^2)/nu.coeff := by
    have same : nu.coeff⁻¹*(D+R^2)=(D+R^2)/nu.coeff := by ring
    rw [same] at payment
    linarith only [payment]
  exact final.trans (add_le_add_right (le_max_right _ _) _)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanResidualCost
