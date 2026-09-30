import H0mework.Versions.X.NavierStokes.WindowSchurMean.EffectiveGraph

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderPrincipal
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_norm)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistorySchurAction (effective feedback)
open NativeWindowHistoryMeanDrift (drift)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
open NativeFiniteActionResolvent (physicalSpace pairing coefficients)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
variable {nu : Viscosity}

private theorem young (x y a : ℝ) (positive : 0 < a) :
    2*x*y ≤ a*x^2+y^2/a := by
  have cancel : a*(y^2/a)=y^2 := mul_div_cancel₀ _ positive.ne'
  apply (mul_le_mul_iff_left₀ positive).mp
  nlinarith only [sq_nonneg (a*x-y),cancel]

private theorem pair_square {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x+y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have bound := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith only [bound,sq_nonneg (‖x‖-‖y‖)]

def lower (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    wholePhysical →L[ℝ] wholePhysical := effective seed M time+nu.coeff • laplacianFiber nu M

theorem lower_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (u : wholePhysical) :
    lower seed M time u=drift seed M time u+feedback seed M time u := by
  have equation := NativeWindowMeanEffectiveGraph.load_split seed M time u
  unfold NativeWindowMeanEffectiveGraph.load at equation
  change effective seed M time u+nu.coeff • laplacianFiber nu M u=_
  rw [equation]
  abel

theorem source_lower_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ)
    (positive : 0 < epsilon) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ time∈Icc 0 horizon,∀ v : physicalSpace (modes M),
      ‖lower seed M time (includeCLM (modes M) (modes_closed M) v)‖^2 ≤
        epsilon*‖laplacianFiber nu M (includeCLM (modes M) (modes_closed M) v)‖^2+
          C*‖coefficients (modes M) v‖^2 := by
  obtain ⟨B,B0,feedbackPaid⟩ := NativeWindowHistoryAdjointSpatialFeedback.source_feedback_bound seed horizon
  let delta := epsilon/4
  have delta0 : 0 < delta := div_pos positive (by norm_num)
  let D := NativeWindowHistoryCreationSource.budget seed horizon delta
  have D0 : 0 ≤ D := NativeWindowHistoryCreationSource.budget_nonnegative seed horizon delta delta0
  let A := D+B*nu.coeff
  let C := 2*B+2*A^2/epsilon
  have C0 : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,C0,fun M time inside v => ?_⟩
  let u := includeCLM (modes M) (modes_closed M) v
  let L := ‖laplacianFiber nu M u‖
  let m := ‖u‖
  have grad : NativeCommonAdvectorAction.curlPair (modes M) v.1 v.1=
      inner ℝ u (laplacianFiber nu M u) := by
    rw [NativeWindowMetricGraphHistory.fiber_gradient]
    simp only [u,NativePhysicalPairing.restrict_include]
  have mass : ‖coefficients (modes M) v‖=m := (include_norm (modes M) (modes_zero M) (modes_closed M) v).symm
  have energy : NativeWindowHistoryHeatDual.energy nu M v=m^2+nu.coeff*inner ℝ u (laplacianFiber nu M u) := by
    rw [NativeWindowHistoryHeatDual.energy,mass,grad]
  have gradient := real_inner_le_norm u (laplacianFiber nu M u)
  have driftPaid := NativeWindowHistoryMeanDrift.source_drift_bound seed horizon delta delta0 M time inside v
  have graph : pairing (modes M)
      (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v)
      (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v)=L^2 := by
    have self := real_inner_self_eq_norm_sq (coefficients (modes M)
      (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v))
    change pairing (modes M) _ _ = _ at self
    rw [self]
    dsimp only [L,u]
    rw [NativeWindowMetricGraphHistory.laplacian_norm,NativePhysicalPairing.restrict_include]
  rw [graph,grad] at driftPaid
  have reaction := feedbackPaid M time inside v
  rw [energy] at reaction
  have driftGradient := mul_le_mul_of_nonneg_left gradient D0
  have feedbackGradient := mul_le_mul_of_nonneg_left gradient (mul_nonneg B0 nu.coeff_pos.le)
  have both := pair_square (drift seed M time u) (feedback seed M time u)
  have mixed := young L (A*m) (epsilon/2) (by positivity)
  have mixed' : 2*A*m*L ≤ (epsilon/2)*L^2+(2*A^2/epsilon)*m^2 := by
    convert mixed using 1 <;> ring
  rw [lower_original,mass]
  change _≤epsilon*L^2+C*m^2
  dsimp only [C,A,delta,D] at *
  nlinarith only [both,driftPaid,reaction,driftGradient,feedbackGradient,mixed']


def weight (nu : Viscosity) (M : ℕ) : wholePhysical →L[ℝ] wholePhysical :=
  ContinuousLinearMap.id ℝ wholePhysical+nu.coeff • laplacianFiber nu M

private theorem right_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (l r : E) (a : ℝ) : inner ℝ l (r-a • l)=inner ℝ l r-a*‖l‖^2 := by
  rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]

private theorem left_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u l r : E) (a : ℝ) : inner ℝ (u+a • l) r=inner ℝ u r+a*inner ℝ l r := by
  rw [inner_add_left,real_inner_smul_left]

theorem source_principal_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ time∈Icc 0 horizon,∀ v : physicalSpace (modes M),
      2*inner ℝ (weight nu M (includeCLM (modes M) (modes_closed M) v))
        (effective seed M time (includeCLM (modes M) (modes_closed M) v)) ≤
          -nu.coeff^2*‖laplacianFiber nu M (includeCLM (modes M) (modes_closed M) v)‖^2+
            C*‖coefficients (modes M) v‖^2 := by
  have viscosity := nu.coeff_pos
  obtain ⟨B,B0,bounded⟩ := source_lower_bound seed horizon (nu.coeff^2/4) (by positivity)
  refine ⟨2*B,by positivity,fun M time inside v => ?_⟩
  let u := includeCLM (modes M) (modes_closed M) v
  let l := laplacianFiber nu M u
  let r := lower seed M time u
  have mass : inner ℝ u (effective seed M time u) ≤ 0 := by
    rw [NativeWindowHistorySchurAction.effective_energy]
    have g := NativeWindowHistoryMeanGradient.gradient_nonnegative seed M
      (NativeWindowHistoryMeanProjection.embed u)
    have c := NativeWindowHistorySchurAction.cost_nonnegative seed M time u
    nlinarith only [g,c,nu.coeff_pos]
  have split : effective seed M time u=r-nu.coeff • l := by
    change effective seed M time u=(effective seed M time u+nu.coeff • l)-nu.coeff • l
    abel
  have graph : inner ℝ l (effective seed M time u)=inner ℝ l r-nu.coeff*‖l‖^2 := by
    rw [split]
    exact right_pair (E := wholePhysical) l r nu.coeff
  have cauchy := real_inner_le_norm l r
  have small := young ‖l‖ ‖r‖ (nu.coeff/2) (by positivity)
  have paid := bounded M time inside v
  have result : 2*inner ℝ l (effective seed M time u) ≤
      -nu.coeff*‖l‖^2+(2*B/nu.coeff)*‖coefficients (modes M) v‖^2 := by
    have scaled := div_le_div_of_nonneg_right paid (show 0≤nu.coeff/2 by positivity)
    have normalized : ((nu.coeff^2/4)*‖l‖^2+B*‖coefficients (modes M) v‖^2)/(nu.coeff/2)=
        (nu.coeff/2)*‖l‖^2+(2*B/nu.coeff)*‖coefficients (modes M) v‖^2 := by
      field_simp; ring
    rw [normalized] at scaled
    change ‖r‖^2/(nu.coeff/2) ≤ _ at scaled
    nlinarith only [graph,cauchy,small,scaled]
  have final := mul_le_mul_of_nonneg_left result nu.coeff_pos.le
  have cancel : nu.coeff*(2*B/nu.coeff)=2*B := mul_div_cancel₀ _ nu.coeff_pos.ne'
  change 2*inner ℝ (u+nu.coeff • l) (effective seed M time u) ≤ _
  rw [left_pair (E := wholePhysical)]
  nlinarith only [mass,final,cancel]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem lower_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    lower seed M (step.2.clockAdvance+time)=lower step.1 M time := by
  have original := NativeWindowHistorySchurAction.action_next seed M step generated time nonnegative
  exact congrArg (fun A : wholePhysical →L[ℝ] wholePhysical => A+nu.coeff • laplacianFiber nu M)
    (congrArg Prod.fst original)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderPrincipal
