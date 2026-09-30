import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.Flow
import H0mework.Versions.X.NavierStokes.WindowHistoryCreation.Mean
import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.Memory

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCausalBudget
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistoryCausalBath (kernel)
open NativeWholeResolvent (wholePhysical)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (includeCLM)
open NativeFiniteActionResolvent (physicalSpace pairing)
open NativeCommonAdvectorAction (curlPair)
open NativeWindowOperatorGreen (laplacian)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

def effect (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a ≤ B) (s b : ℝ) (u v : wholePhysical) : ℝ :=
  inner ℝ (creation seed M s v) (kernel seed M a B aB s b (creation seed M b u))

theorem effect_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a ≤ B) (b : ℝ) (inside : b∈Icc a B)
    (s : ℝ) (sample : s∈Icc a b) (u v : wholePhysical) :
    |effect seed M a B aB s b u v|≤‖creation seed M s v‖*‖creation seed M b u‖ := by
  exact (abs_real_inner_le_norm (creation seed M s v)
    (kernel seed M a B aB s b (creation seed M b u))).trans
      (mul_le_mul_of_nonneg_left
        (NativeWindowHistoryCausalBath.kernel_contracts seed M a B aB b inside (creation seed M b u) s sample)
        (norm_nonneg _))

theorem source_kernel_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ)
    (nonnegative : 0≤horizon) (positive : 0<epsilon) :
    ∃ C : ℝ,0≤C ∧ ∀ M,∀ b∈Icc 0 horizon,∀ s∈Icc 0 b,
      ∀ u v : physicalSpace (modes M),
      2*|effect seed M 0 horizon nonnegative s b
        (includeCLM (modes M) (modes_closed M) u) (includeCLM (modes M) (modes_closed M) v)|≤
        epsilon*(pairing (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu u)
          (laplacian (modes M) (modes_zero M) (modes_closed M) nu u)+
          pairing (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu v)
            (laplacian (modes M) (modes_zero M) (modes_closed M) nu v))+
          C*(curlPair (modes M) u.1 u.1+curlPair (modes M) v.1 v.1) := by
  let C := NativeWindowHistoryCreationSource.budget seed horizon epsilon
  refine ⟨C,NativeWindowHistoryCreationSource.budget_nonnegative seed horizon epsilon positive,?_⟩
  intro M b inside s sample u v
  have first := NativeWindowHistoryCreationSource.source_creation_bound seed horizon epsilon positive M b inside u
  have second := NativeWindowHistoryCreationSource.source_creation_bound seed horizon epsilon positive M s
    ⟨sample.1,sample.2.trans inside.2⟩ v
  have coupled := effect_bound seed M 0 horizon nonnegative b inside s sample
    (includeCLM (modes M) (modes_closed M) u) (includeCLM (modes M) (modes_closed M) v)
  have product := sq_nonneg (‖creation seed M s (includeCLM (modes M) (modes_closed M) v)‖-
    ‖creation seed M b (includeCLM (modes M) (modes_closed M) u)‖)
  dsimp only [C]
  nlinarith only [first,second,coupled,product]

def createdMemory (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (b : ℝ) : ℝ :=
  ∫ s in a..b,effect seed M a B aB s b
    (mean (finiteHistory seed b M)) (mean (finiteHistory seed s M))

theorem source_created_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (nonnegative : 0≤horizon) :
    ∃ C : ℝ,0≤C ∧ ∀ M (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,
      |createdMemory seed M a horizon start.2 b|≤C := by
  obtain ⟨D,D0,paid⟩ := NativeWindowHistoryCreationMean.source seed horizon
  refine ⟨D*horizon,mul_nonneg D0 nonnegative,?_⟩
  intro M a start b inside
  have point (s : ℝ) (hs : s∈uIoc a b) :
      ‖effect seed M a horizon start.2 s b
        (mean (finiteHistory seed b M)) (mean (finiteHistory seed s M))‖≤D := by
    rw [uIoc_of_le inside.1] at hs
    have atEnd := paid M b ⟨start.1.trans inside.1,inside.2⟩
    have atSample := paid M s ⟨start.1.trans hs.1.le,hs.2.trans inside.2⟩
    have coupled := effect_bound seed M a horizon start.2 b inside s ⟨hs.1.le,hs.2⟩
      (mean (finiteHistory seed b M)) (mean (finiteHistory seed s M))
    have product := sq_nonneg (‖creation seed M s (mean (finiteHistory seed s M))‖-
      ‖creation seed M b (mean (finiteHistory seed b M))‖)
    rw [Real.norm_eq_abs]
    nlinarith only [atEnd,atSample,coupled,product]
  have integrated := intervalIntegral.norm_integral_le_of_norm_le_const point
  rw [abs_of_nonneg (sub_nonneg.mpr inside.1),Real.norm_eq_abs] at integrated
  exact integrated.trans (mul_le_mul_of_nonneg_left (by linarith [start.1,inside.2] : b-a≤horizon) D0)

theorem complete_memory (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (a B : ℝ) (aB : a≤B) (b : ℝ) (inside : b∈Icc a B) :
    NativeWindowHistoryCausalMean.memory seed M a B aB b (mean (finiteHistory seed b M))=
      createdMemory seed M a B aB b+
        ∫ t in a..b,inner ℝ (NativeWindowHistoryMeanProjection.residual (NativeWindowHistoryOseen.forcingHistory seed M t))
          (kernel seed M a B aB t b (creation seed M b (mean (finiteHistory seed b M)))) :=
  NativeWindowHistoryCausalMean.memory_decomposition seed M a B aB b inside _

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem effect_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a) (b : ℝ) (inside : b∈Icc a B)
    (s : ℝ) (sample : s∈Icc a b) (u v : wholePhysical) :
    effect seed M (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _)
      (step.2.clockAdvance+s) (step.2.clockAdvance+b) u v=
        effect step.1 M a B aB s b u v := by
  simp only [effect,NativeWindowHistoryMeanBlocks.creation_next seed M step generated s (a0.trans sample.1),
    NativeWindowHistoryMeanBlocks.creation_next seed M step generated b (a0.trans inside.1),
    NativeWindowHistoryCausalBath.kernel_next seed M step generated a B aB a0 b inside s sample]

theorem createdMemory_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a) (b : ℝ) (inside : b∈Icc a B) :
    createdMemory seed M (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _)
      (step.2.clockAdvance+b)=createdMemory step.1 M a B aB b := by
  unfold createdMemory
  rw [← intervalIntegral.integral_comp_add_left _ step.2.clockAdvance]
  apply intervalIntegral.integral_congr
  intro s hs
  have sample : s∈Icc a b := by simpa only [uIcc_of_le inside.1] using hs
  have before := congrArg mean
    (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated b (a0.trans inside.1) M)
  have after := congrArg mean
    (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated s (a0.trans sample.1) M)
  have reads := congrArg₂ (fun u v : wholePhysical => effect seed M
    (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _)
      (step.2.clockAdvance+s) (step.2.clockAdvance+b) u v) before after
  exact reads.trans (effect_next seed M step generated a B aB a0 b inside s sample _ _)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCausalBudget
