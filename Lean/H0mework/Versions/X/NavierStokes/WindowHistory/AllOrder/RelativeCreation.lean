import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.RelativeCreation
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.JointLoad

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderRelativeCreation
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H gradient)
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (includeCLM)
open NativeFiniteActionResolvent (physicalSpace)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistoryAllOrderWord (value)
open NativeWindowHistoryAllOrderCausal (created)
open NativeWindowHistorySpatialWords (history)
open NativeWindowHistoryAllOrderJointEnergy (energy)
open NativeWindowHistoryCausalPassivity (creationResponse)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

def physicalValue (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (t : ℝ) :
    physicalSpace (modes M) := restrictCLM (modes M) (modes_zero M) (modes_closed M) (value seed M word t)

theorem include_value (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (t : ℝ) :
    includeCLM (modes M) (modes_closed M) (physicalValue seed M word t)=value seed M word t := by
  change includeCLM (modes M) (modes_closed M)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M)
      (includeCLM (modes M) (modes_closed M) _))=_
  rw [NativePhysicalPairing.restrict_include]
  rfl

theorem physical_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) :
    Continuous (physicalValue seed M word) :=
  (restrictCLM (modes M) (modes_zero M) (modes_closed M)).continuous.comp
    (NativeWindowHistoryAllOrderCausal.value_continuous seed M word)

theorem mean_gradient (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (t : ℝ) :
    gradient M (embed (value seed M word t))≤gradient M (history seed M word t) := by
  rw [NativeWindowHistoryAllOrderWord.value_original]
  exact NativeWindowHistoryMeanGradient.gradient_projection_le seed M _

private theorem response_curve (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (v w : ℝ → wholePhysical) (vc : Continuous v) (wc : Continuous w) (same : v=w)
    (a B : ℝ) (aB : a≤B) : creationResponse seed M v vc a B aB=creationResponse seed M w wc a B aB := by
  subst w
  rfl

theorem response_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) :
    creationResponse seed M (fun t => includeCLM (modes M) (modes_closed M) (physicalValue seed M word t))
      ((includeCLM (modes M) (modes_closed M)).continuous.comp (physical_continuous seed M word)) a B aB=
        created seed M word a B aB :=
  response_curve seed M _ _ _ (NativeWindowHistoryAllOrderCausal.value_continuous seed M word)
    (funext (include_value seed M word)) a B aB

theorem source_potential (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃ C : ℝ,0≤C ∧ ∀ M word a B (aB : a≤B) t,t∈Icc 0 horizon →
      NativeWindowHistorySchurWeakPairing.potential seed M t (physicalValue seed M word t)≤
        epsilon*gradient M (history seed M word t)+C*energy seed M word a B aB t := by
  obtain ⟨C,C0,paid⟩:=NativeWindowHistoryCausalRelativeCreation.source_potential seed horizon epsilon positive
  refine ⟨C,C0,fun M word a B aB t inside => ?_⟩
  have source:=paid M t inside (physicalValue seed M word t)
  rw [include_value] at source
  exact source.trans (add_le_add
    (mul_le_mul_of_nonneg_left (mean_gradient seed M word t) positive.le)
    (mul_le_mul_of_nonneg_left (NativeWindowHistoryAllOrderJointControl.value_controls seed M word a B aB t) C0))

set_option backward.isDefEq.respectTransparency false in
theorem source_energy (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃ C : ℝ,0≤C ∧ ∀ M (word : List Coordinate) (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,
      ‖created seed M word a horizon start.2 b‖^2+
        nu.coeff*(∫t in a..b,gradient M (created seed M word a horizon start.2 t))≤
          epsilon*(∫t in a..b,gradient M (history seed M word t))+
            C*(∫t in a..b,energy seed M word a horizon start.2 t) := by
  obtain ⟨C,C0,paid⟩:=NativeWindowHistoryCausalRelativeCreation.source_energy seed horizon epsilon positive
  refine ⟨C,C0,fun M word a start b inside => ?_⟩
  have source:=paid M (physicalValue seed M word) (physical_continuous seed M word) a start b inside
  dsimp only at source
  rw [response_original] at source
  simp only [include_value] at source
  have yc := (NativeWindowHistoryAllOrderCausal.value_continuous seed M word)
  have input := ((NativeWindowHistoryCausalDissipation.gradient_continuous nu M).comp (embed.continuous.comp yc)).intervalIntegrable (μ := volume) a b
  have whole := ((NativeWindowHistoryCausalDissipation.gradient_continuous nu M).comp
    (NativeWindowHistoryAllOrderCreatedLoadBudget.history_continuous seed M word)).intervalIntegrable (μ := volume) a b
  have em := ((NativeWindowHistoryAllOrderJointLoad.energy_continuous seed M word a horizon start.2).mono
    (Icc_subset_Icc le_rfl inside.2)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have grad := intervalIntegral.integral_mono_on inside.1 input whole (fun t _ => mean_gradient seed M word t)
  have mass := intervalIntegral.integral_mono_on inside.1 ((yc.norm.pow 2).intervalIntegrable (μ := volume) a b) em
    (fun t _ => NativeWindowHistoryAllOrderJointControl.value_controls seed M word a horizon start.2 t)
  exact source.trans (add_le_add (mul_le_mul_of_nonneg_left grad positive.le) (mul_le_mul_of_nonneg_left mass C0))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderRelativeCreation
