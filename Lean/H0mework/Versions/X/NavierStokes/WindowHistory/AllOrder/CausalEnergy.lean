import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.Causal
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.Physical

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderCausalEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowTraceWholeHistory (H gradient)
open NativeWindowHistoryAllOrderWord (value)
open NativeWindowHistoryMeanProjection (embed)
open NativeWindowHistoryMeanAction (meanOperator creation)
open NativeWindowHistoryMeanBlocks (bath annihilation)
open NativeWindowHistoryAllOrderCausal (created remaining remainder)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
local notation "Q" => NativeWindowHistoryMeanProjection.residual
variable {nu : Viscosity}

def energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) : ℝ :=
  ‖value seed M word t‖^2+‖created seed M word a B aB t‖^2

def dissipation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) : ℝ :=
  gradient M (embed (value seed M word t))+gradient M (Q (created seed M word a B aB t))

def work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) : ℝ :=
  2*inner ℝ (value seed M word t) (remainder seed M word a B aB t)

set_option backward.isDefEq.respectTransparency false in
theorem source_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) (inside : t∈Icc a B) :
    HasDerivWithinAt (energy seed M word a B aB)
      (-2*nu.coeff*dissipation seed M word a B aB t+work seed M word a B aB t) (Icc a B) t := by
  have vd : HasDerivWithinAt (value seed M word)
      (meanOperator seed M t (value seed M word t)+annihilation seed M t (created seed M word a B aB t)+
        remainder seed M word a B aB t) (Icc a B) t :=
    (NativeWindowHistoryAllOrderCausal.source_derivative seed M word a B aB t).hasDerivWithinAt
  have rd := NativeWindowHistoryAllOrderCausal.created_derivative seed M word a B aB t inside
  have raw := (HasDerivWithinAt.norm_sq (F := wholePhysical) vd).add
    (HasDerivWithinAt.norm_sq (F := H) rd)
  have cross := NativeWindowHistoryMeanBlocks.coupling_green seed M t
    (value seed M word t) (created seed M word a B aB t)
  apply raw.congr_deriv
  simp only [inner_add_right,NativeWindowHistorySchurAction.mean_energy,
    NativeWindowHistoryBathResolvent.bath_energy]
  have swapped := real_inner_comm (created seed M word a B aB t) (creation seed M t (value seed M word t))
  dsimp only [dissipation,work]
  linarith only [cross,swapped]

theorem source_controls (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) :
    ‖value seed M word t‖^2≤energy seed M word a B aB t :=
  le_add_of_nonneg_right (sq_nonneg _)

theorem physical_controls (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) :
    ‖NativeWindowHistoryAllOrderPhysical.field seed M word t‖^2≤energy seed M word a B aB t := by
  rw [NativeWindowHistoryAllOrderPhysical.field,NativeWindowHistoryAllOrderPhysical.read_norm]
  exact source_controls seed M word a B aB t

theorem created_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) : created seed M word a B aB a=0 :=
  NativeWindowHistoryCausalPassivity.bathResponse_initial seed M _ _ a B aB

theorem energy_initial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) : energy seed M word a B aB a=‖value seed M word a‖^2 := by
  rw [energy,created_initial,norm_zero,zero_pow (by decide),add_zero]

theorem remaining_prepared (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (B : ℝ) (horizon : -2≤B) : remaining seed M word (-2) B horizon (-2)=0 := by
  have centered : Q (NativeWindowHistorySpatialWords.history seed M word (-2))=0 :=
    (NativeWindowHistoryMeanProjection.residual_comp (NativeWindowHistorySpatialWords.fiber M word)
      (NativeWindowTraceWholeHistory.finiteHistory seed (-2) M)).trans
        ((congrArg (NativeWindowHistorySpatialWords.operator M word)
          (NativeWindowHistoryMeanBlocks.source_initial seed M)).trans (map_zero _))
  exact (congrArg₂ (fun x y : H => x-y) centered (created_initial seed M word (-2) B horizon)).trans (sub_self _)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem source_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a) (t : ℝ) (inside : t∈Icc a B) :
    (energy seed M word (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _)
      (step.2.clockAdvance+t),
    dissipation seed M word (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _)
      (step.2.clockAdvance+t),
    work seed M word (step.2.clockAdvance+a) (step.2.clockAdvance+B) (add_le_add_right aB _)
      (step.2.clockAdvance+t))=
    (energy step.1 M word a B aB t,dissipation step.1 M word a B aB t,work step.1 M word a B aB t) := by
  simp only [energy,dissipation,work,
    NativeWindowHistoryAllOrderWord.value_next seed M word step generated t (a0.trans inside.1),
    NativeWindowHistoryAllOrderCausal.created_next seed M word step generated a B aB a0 t inside,
    NativeWindowHistoryAllOrderCausal.remainder_next seed M word step generated a B aB a0 t inside]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderCausalEnergy
