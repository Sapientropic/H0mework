import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.Word
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.Principal
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.Test

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderSpatial
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_norm)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistorySchurAction (effective)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
open NativeWindowHistoryAllOrderWord (value retained)
open NativeWindowHistoryAllOrderPrincipal (weight)
open PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy (FixedMatterSpatialWordIndex)
noncomputable section
variable {nu : Viscosity}

private theorem weighted_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) (symmetric : ∀ x y,inner ℝ (L x) y=inner ℝ x (L y))
    (a : ℝ) (u v : E) : inner ℝ (u+a • L u) v=inner ℝ u (v+a • L v) := by
  rw [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,symmetric]

theorem weight_symmetric (nu : Viscosity) (M : ℕ) (u v : wholePhysical) :
    inner ℝ (weight nu M u) v=inner ℝ u (weight nu M v) :=
  weighted_symmetric (E := wholePhysical) (laplacianFiber nu M)
    (NativeWindowHistoryDynamicTest.laplacian_symmetric nu M) nu.coeff u v

private theorem quadratic_derivative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (symmetric : ∀ x y,inner ℝ (T x) y=inner ℝ x (T y))
    {f : ℝ → E} {d : E} {t : ℝ} (derivative : HasDerivAt f d t) :
    HasDerivAt (fun s => inner ℝ (f s) (T (f s))) (2*inner ℝ (T (f t)) d) t := by
  have original := derivative.inner ℝ (T.hasFDerivAt.comp_hasDerivAt t derivative)
  have read : inner ℝ (f t) (T d)+inner ℝ d ((T ∘ f) t)=2*inner ℝ (T (f t)) d := by
    change inner ℝ (f t) (T d)+inner ℝ d (T (f t))=_
    rw [← symmetric,real_inner_comm d (T (f t))]
    ring
  rw [read] at original
  exact original

def energy (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : ℝ :=
  ∑ word : FixedMatterSpatialWordIndex order,
    inner ℝ (value seed M word.toList time) (weight nu M (value seed M word.toList time))

def dissipation (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : ℝ :=
  ∑ word : FixedMatterSpatialWordIndex order,‖laplacianFiber nu M (value seed M word.toList time)‖^2

def work (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : ℝ :=
  ∑ word : FixedMatterSpatialWordIndex order,
    2*inner ℝ (weight nu M (value seed M word.toList time)) (retained seed M word.toList time)

def principalWork (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : ℝ :=
  ∑ word : FixedMatterSpatialWordIndex order,
    2*inner ℝ (weight nu M (value seed M word.toList time)) (effective seed M time (value seed M word.toList time))

theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    HasDerivAt (energy seed M order) (principalWork seed M order time+work seed M order time) time := by
  have each (word : FixedMatterSpatialWordIndex order) := quadratic_derivative
    (weight nu M) (weight_symmetric nu M) (NativeWindowHistoryAllOrderWord.value_hasDerivAt seed M word.toList time)
  have all := HasDerivAt.sum (u := Finset.univ) fun word _ => each word
  simpa only [energy,principalWork,work,inner_add_right,mul_add,Finset.sum_add_distrib,
    Finset.sum_fn] using! all

theorem source_principal_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0≤C ∧∀ M order,∀ time∈Icc 0 horizon,
      principalWork seed M order time≤-nu.coeff^2*dissipation seed M order time+
        C*NativeWindowHistoryAllOrderWord.energy seed M order time := by
  obtain ⟨C,C0,paid⟩ := NativeWindowHistoryAllOrderPrincipal.source_principal_bound seed horizon
  refine ⟨C,C0,fun M order time inside => ?_⟩
  have each (word : FixedMatterSpatialWordIndex order) :
      2*inner ℝ (weight nu M (value seed M word.toList time))
        (effective seed M time (value seed M word.toList time)) ≤
          -nu.coeff^2*‖laplacianFiber nu M (value seed M word.toList time)‖^2+
            C*‖value seed M word.toList time‖^2 := by
    let v := NativeWindowStageNineWords.word (modes M) (modes_zero M) (modes_closed M) word.toList
      (restrictCLM (modes M) (modes_zero M) (modes_closed M)
        (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)))
    have actual : value seed M word.toList time=includeCLM (modes M) (modes_closed M) v := rfl
    rw [actual,include_norm (modes M) (modes_zero M)]
    exact paid M time inside v
  exact (Finset.sum_le_sum fun word _ => each word).trans_eq
    (by simp only [dissipation,NativeWindowHistoryAllOrderWord.energy,Finset.sum_add_distrib,← Finset.mul_sum])

theorem source_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0≤C ∧∀ M order,∀ time∈Icc 0 horizon,
      deriv (energy seed M order) time+nu.coeff^2*dissipation seed M order time ≤
        C*NativeWindowHistoryAllOrderWord.energy seed M order time+work seed M order time := by
  obtain ⟨C,C0,paid⟩ := source_principal_bound seed horizon
  refine ⟨C,C0,fun M order time inside => ?_⟩
  rw [(source_hasDerivAt seed M order time).deriv]
  linarith only [paid M order time inside]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem source_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0≤time) :
    (energy seed M order (step.2.clockAdvance+time),
      dissipation seed M order (step.2.clockAdvance+time),work seed M order (step.2.clockAdvance+time))=
      (energy step.1 M order time,dissipation step.1 M order time,work step.1 M order time) := by
  simp only [energy,dissipation,work,
    NativeWindowHistoryAllOrderWord.value_next seed M _ step generated time nonnegative,
    NativeWindowHistoryAllOrderWord.retained_next seed M _ step generated time nonnegative]

theorem principalWork_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0≤time) :
    principalWork seed M order (step.2.clockAdvance+time)=principalWork step.1 M order time := by
  have same : effective seed M (step.2.clockAdvance+time)=effective step.1 M time :=
    congrArg Prod.fst (NativeWindowHistorySchurAction.action_next seed M step generated time nonnegative)
  simp only [principalWork,NativeWindowHistoryAllOrderWord.value_next seed M _ step generated time nonnegative,same]

theorem sourceRate_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0≤time) :
    deriv (energy seed M order) (step.2.clockAdvance+time)=deriv (energy step.1 M order) time := by
  rw [(source_hasDerivAt seed M order _).deriv,(source_hasDerivAt step.1 M order time).deriv,
    principalWork_next seed M order step generated time nonnegative]
  exact congrArg (fun x : ℝ×ℝ×ℝ => principalWork step.1 M order time+x.2.2)
    (source_next seed M order step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderSpatial
