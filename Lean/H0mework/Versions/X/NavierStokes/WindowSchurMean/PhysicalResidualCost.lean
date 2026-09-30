import H0mework.Versions.X.NavierStokes.WindowSchurMean.ResidualCost

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanPhysicalResidualCost
open Set MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open NativeWholeH1Mixed (modes modes_zero)
open NativeWholeResolvent (wholePhysical)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
noncomputable section
variable {nu : Viscosity}

def stressWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) : ℝ :=
  let l := laplacianFiber nu M (mean (finiteHistory seed t M))
  ∑ k : (modes M).subtype (fun k => k≠0),
    inner ℝ (l.1 k.1) (NativeViewEnergyWork.residualRow seed 0 t k.1)

theorem inner_finite (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ)
    (f : wholePhysical) :
    let l := laplacianFiber nu M (mean (finiteHistory seed t M))
    inner ℝ l f = ∑ k : (modes M).subtype (fun k => k≠0), inner ℝ (l.1 k.1) (f.1 k.1) := by
  intro l
  change inner ℝ l.1 f.1 = _
  rw [lp.inner_eq_tsum]
  calc
    (∑' k,inner ℝ (l.1 k) (f.1 k))=
        ∑ k ∈ (modes M).subtype (fun k => k≠0),inner ℝ (l.1 k) (f.1 k) := by
      apply tsum_eq_sum
      intro k outside
      have absent : k.1∉modes M := by simpa only [Finset.mem_subtype] using outside
      rw [NativeWindowHistoryMeanGraphLimit.laplacian_row,if_neg absent]
      simp
    _=_ := (Finset.sum_coe_sort _ _).symm

theorem square_finite (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) :
    let l := laplacianFiber nu M (mean (finiteHistory seed t M))
    (∑ k : (modes M).subtype (fun k => k≠0),‖l.1 k.1‖^2)=‖l‖^2 := by
  intro l
  have h : inner ℝ l l =
      ∑ k : (modes M).subtype (fun k => k≠0),inner ℝ (l.1 k.1) (l.1 k.1) :=
    inner_finite seed M t l
  simpa only [real_inner_self_eq_norm_sq] using h.symm

theorem source_stress_spatial_cost (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧∀M≥low,∀t∈Icc 0 horizon,
      (nu.coeff/4)*‖laplacianFiber nu M (mean (finiteHistory seed t M))‖^2≤
        stressWork seed M t+C := by
  obtain ⟨B,B0,bound⟩:=NativeWindowHistoryMeanResidualCost.source_mean_residual_cost seed horizon
  obtain ⟨low,error⟩:=NativeWindowHistoryMeanResidualRead.source_physical_error
    seed horizon 1 (by norm_num)
  have inv0 : 0≤nu.coeff⁻¹:=inv_nonneg.mpr nu.coeff_pos.le
  refine ⟨low,B+nu.coeff⁻¹,add_nonneg B0 inv0,fun M above t inside => ?_⟩
  let l:=laplacianFiber nu M (mean (finiteHistory seed t M))
  let f:=NativeWindowHistoryMeanResidualLoad.residualLoad seed M t
  have errorPaid :
      (∑k : (modes M).subtype (fun k => k≠0),
        ‖f.1 k.1-NativeViewEnergyWork.residualRow seed 0 t k.1‖^2)≤1 :=
    error M above t inside
  have term (k : NonzeroIntegerWavevector) :
      inner ℝ (l.1 k) (f.1 k)≤
        inner ℝ (l.1 k) (NativeViewEnergyWork.residualRow seed 0 t k)+
          (nu.coeff/4)*‖l.1 k‖^2+
            nu.coeff⁻¹*‖f.1 k-NativeViewEnergyWork.residualRow seed 0 t k‖^2 := by
    have pair:=NativeWindowHistoryMeanResidualCost.pair_absorb (l.1 k)
      (f.1 k-NativeViewEnergyWork.residualRow seed 0 t k) nu.coeff nu.coeff_pos
    calc
      inner ℝ (l.1 k) (f.1 k)=inner ℝ (l.1 k) (NativeViewEnergyWork.residualRow seed 0 t k)+
          inner ℝ (l.1 k) (f.1 k-NativeViewEnergyWork.residualRow seed 0 t k) := by
        rw [← inner_add_right]
        congr 1
        abel
      _≤_ := by linarith only [pair]
  have sums:=Finset.sum_le_sum
    (s:=(Finset.univ : Finset ((modes M).subtype (fun k => k≠0))))
    (fun k _ => term k.1)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at sums
  have finite : (∑k : (modes M).subtype (fun k => k≠0),‖l.1 k.1‖^2)=‖l‖^2 :=
    square_finite seed M t
  have remaining := mul_le_mul_of_nonneg_left errorPaid inv0
  have tested : inner ℝ l f ≤ stressWork seed M t+(nu.coeff/4)*‖l‖^2+nu.coeff⁻¹ := by
    rw [inner_finite seed M t f,stressWork]
    change (∑k : (modes M).subtype (fun k => k≠0),inner ℝ (l.1 k.1) (f.1 k.1))≤_
    rw [← finite]
    linarith only [sums,remaining]
  have base := bound M t inside
  change (nu.coeff/2)*‖l‖^2 ≤ inner ℝ l f+B at base
  change (nu.coeff/4)*‖l‖^2 ≤ stressWork seed M t+(B+nu.coeff⁻¹)
  linarith only [tested,base]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem stressWork_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (time : ℝ) (nonnegative : 0≤time) :
    stressWork seed M (step.2.clockAdvance+time)=stressWork step.1 M time := by
  unfold stressWork
  rw [NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M]
  simp only [NativeViewEnergyWork.residualRow,NativeZeroHeatWindow.source_zero,
    NativeForwardWindowSource.source_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanPhysicalResidualCost
