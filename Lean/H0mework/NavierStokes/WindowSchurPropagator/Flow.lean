import H0mework.NavierStokes.WindowHistoryOseen.Action

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryPropagator
open Set Filter MeasureTheory
open PhysicsCore.StageNineDiracMatterGalerkinEvolution
noncomputable section

section Linear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private def generator (A : E →L[ℝ] E) : (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E :=
  ContinuousLinearMap.compL ℝ E E E A

omit [CompleteSpace E] in
private theorem generator_continuous (A : ℝ → E →L[ℝ] E) (continuous : Continuous A) :
    Continuous (fun t => generator (A t)) := (ContinuousLinearMap.compL ℝ E E E).continuous.comp continuous

def matrix (A : ℝ → E →L[ℝ] E) (continuous : Continuous A) (a b : ℝ) (ab : a ≤ b) : ℝ → E →L[ℝ] E :=
  (exists_galerkinLinearCoefficientCurve_on_Icc (fun t => generator (A t)) (generator_continuous A continuous)
    (ContinuousLinearMap.id ℝ E) a b ab).choose

theorem matrix_initial (A : ℝ → E →L[ℝ] E) (continuous : Continuous A) (a b : ℝ) (ab : a ≤ b) :
    matrix A continuous a b ab a=ContinuousLinearMap.id ℝ E :=
  (exists_galerkinLinearCoefficientCurve_on_Icc (fun t => generator (A t)) (generator_continuous A continuous)
    (ContinuousLinearMap.id ℝ E) a b ab).choose_spec.1

theorem matrix_derivative (A : ℝ → E →L[ℝ] E) (continuous : Continuous A) (a b : ℝ) (ab : a ≤ b)
    (t : ℝ) (inside : t ∈ Icc a b) : HasDerivWithinAt (matrix A continuous a b ab)
      ((A t).comp (matrix A continuous a b ab t)) (Icc a b) t :=
  (exists_galerkinLinearCoefficientCurve_on_Icc (fun t => generator (A t)) (generator_continuous A continuous)
    (ContinuousLinearMap.id ℝ E) a b ab).choose_spec.2 t inside

theorem matrix_continuous (A : ℝ → E →L[ℝ] E) (continuous : Continuous A) (a b : ℝ) (ab : a ≤ b) :
    ContinuousOn (matrix A continuous a b ab) (Icc a b) := fun t ht =>
  (matrix_derivative A continuous a b ab t ht).continuousWithinAt

theorem applied_derivative (A : ℝ → E →L[ℝ] E) (continuous : Continuous A) (a b : ℝ) (ab : a ≤ b)
    (v : E) (t : ℝ) (inside : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => matrix A continuous a b ab s v)
      (A t (matrix A continuous a b ab t v)) (Icc a b) t := by
  simpa only [ContinuousLinearMap.comp_apply,map_zero,add_zero] using (matrix_derivative A continuous a b ab t inside).clm_apply (hasDerivWithinAt_const t (Icc a b) v)

theorem applied_original (A : ℝ → E →L[ℝ] E) (continuous : Continuous A) (a b : ℝ) (ab : a ≤ b)
    (v : E) (path : ℝ → E) (initial : path a=v)
    (evolution : ∀ t ∈ Icc a b,HasDerivWithinAt path (A t (path t)) (Icc a b) t) :
    EqOn (fun t => matrix A continuous a b ab t v) path (Icc a b) := by
  apply galerkinLinearCoefficientCurve_eqOn_Icc A continuous _ path v a b ab
  · rw [matrix_initial]; rfl
  · exact initial
  · exact applied_derivative A continuous a b ab v
  · exact evolution
end Linear

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H action adjoint action_continuous adjoint_continuous)
variable {nu : Viscosity}

def forward (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a ≤ b) : ℝ → H →L[ℝ] H :=
  matrix (E := H) (action seed M) (action_continuous seed M) a b ab

def backwardFlow (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a ≤ b) : ℝ → H →L[ℝ] H :=
  matrix (E := H) (fun t => -adjoint seed M t) (adjoint_continuous seed M).neg a b ab

theorem forward_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a ≤ b)
    (initial : H) (t : ℝ) (inside : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => forward seed M a b ab s initial)
      (action seed M t (forward seed M a b ab t initial)) (Icc a b) t :=
  applied_derivative (E := H) _ _ a b ab initial t inside

theorem backwardFlow_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a ≤ b)
    (initial : H) (t : ℝ) (inside : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => backwardFlow seed M a b ab s initial)
      (-adjoint seed M t (backwardFlow seed M a b ab t initial)) (Icc a b) t :=
  applied_derivative (E := H) _ _ a b ab initial t inside

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryPropagator
