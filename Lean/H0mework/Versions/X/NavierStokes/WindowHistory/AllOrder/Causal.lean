import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.Word
import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.ResponseNext

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderCausal
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowTraceWholeHistory (H finiteHistory gradient)
open NativeWindowHistorySpatialWords (history operator commutator)
open NativeWindowHistoryAllOrderWord (value)
open NativeWindowHistoryOseen (action forcingHistory)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistoryMeanAction (creation meanOperator)
open NativeWindowHistoryMeanBlocks (annihilation bath)
open NativeWindowHistoryCausalPassivity (creationResponse)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local notation "Q" => NativeWindowHistoryMeanProjection.residual
variable {nu : Viscosity}

def load (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (t : ℝ) : H :=
  commutator seed M word t (finiteHistory seed t M)+operator M word (forcingHistory seed M t)

theorem value_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) :
    Continuous (value seed M word) := continuous_iff_continuousAt.mpr
  (fun t => (NativeWindowHistoryAllOrderWord.value_hasDerivAt seed M word t).continuousAt)

private theorem mapped_triple {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (x y z : E) :
    L (x+y+z)=L x+L (y+z) := by rw [map_add,map_add,map_add]; abel

private theorem reorder {E : Type*} [AddCommGroup E] (x y z : E) : x+y+z=y+x+z := by abel

set_option backward.isDefEq.respectTransparency false in
theorem mean_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (t : ℝ) :
    HasDerivAt (value seed M word)
      (meanOperator seed M t (value seed M word t)+annihilation seed M t (history seed M word t)+
        mean (load seed M word t)) t := by
  have raw := mean.hasFDerivAt.comp_hasDerivAt (F := H) (E := wholePhysical) t
    (NativeWindowHistorySpatialWords.source_action seed M word t)
  have values := congrArg (meanOperator seed M t)
    (NativeWindowHistoryAllOrderWord.value_original seed M word t).symm
  have principal := (NativeWindowHistoryMeanBlocks.mean_action_split seed M t (history seed M word t)).trans
    (congrArg (fun v : wholePhysical => v+annihilation seed M t (history seed M word t)) values)
  have read := (mapped_triple (E := H) (F := wholePhysical) mean
    (action seed M t (history seed M word t))
    (commutator seed M word t (finiteHistory seed t M)) (operator M word (forcingHistory seed M t))).trans
      (congrArg (fun v : wholePhysical => v+mean (load seed M word t)) principal)
  apply (raw.congr_deriv read).congr_of_eventuallyEq
  exact Eventually.of_forall fun s => NativeWindowHistoryAllOrderWord.value_original seed M word s

set_option backward.isDefEq.respectTransparency false in
theorem residual_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate) (t : ℝ) :
    HasDerivAt (fun s => Q (history seed M word s))
      (bath seed M t (Q (history seed M word t))+creation seed M t (value seed M word t)+
        Q (load seed M word t)) t := by
  have raw := (Q).hasFDerivAt.comp_hasDerivAt (E := H) (F := H) t
    (NativeWindowHistorySpatialWords.source_action seed M word t)
  have values := congrArg (creation seed M t)
    (NativeWindowHistoryAllOrderWord.value_original seed M word t).symm
  have baths := (NativeWindowHistoryBathResolvent.bath_residual seed M t (history seed M word t)).symm
  have principal := (NativeWindowHistoryMeanBlocks.residual_action_split seed M t (history seed M word t)).trans
    (congrArg₂ (fun v w : H => v+w) values baths)
  have read := (mapped_triple (E := H) (F := H) Q
    (action seed M t (history seed M word t))
    (commutator seed M word t (finiteHistory seed t M)) (operator M word (forcingHistory seed M t))).trans
      (congrArg (fun v : H => v+Q (load seed M word t)) principal)
  exact raw.congr_deriv (read.trans (reorder (E := H) _ _ _))

def created (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) : ℝ → H :=
  creationResponse seed M (value seed M word) (value_continuous seed M word) a B aB

def remaining (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) : H :=
  Q (history seed M word t)-created seed M word a B aB t

theorem created_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) (inside : t∈Icc a B) :
    HasDerivWithinAt (created seed M word a B aB)
      (bath seed M t (created seed M word a B aB t)+creation seed M t (value seed M word t)) (Icc a B) t :=
  NativeWindowHistoryCausalPassivity.bathResponse_derivative seed M _ _ a B aB t inside

private theorem subtract_drive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (x y c f : E) : (A x+c+f)-(A y+c)=A (x-y)+f := by
  rw [map_sub]
  abel

set_option backward.isDefEq.respectTransparency false in
theorem remaining_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) (inside : t∈Icc a B) :
    HasDerivWithinAt (remaining seed M word a B aB)
      (bath seed M t (remaining seed M word a B aB t)+Q (load seed M word t)) (Icc a B) t := by
  have raw := (residual_derivative seed M word t).hasDerivWithinAt.sub
    (created_derivative seed M word a B aB t inside)
  exact raw.congr_deriv (subtract_drive (E := H) (bath seed M t) _ _ _ _)

def remainder (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) : wholePhysical :=
  annihilation seed M t (remaining seed M word a B aB t)+mean (load seed M word t)

private theorem split_response {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) (x y : E) (u f : F) :
    u+A x+f=u+A y+(A (x-y)+f) := by rw [map_sub]; abel

set_option backward.isDefEq.respectTransparency false in
theorem source_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a≤B) (t : ℝ) :
    HasDerivAt (value seed M word)
      (meanOperator seed M t (value seed M word t)+annihilation seed M t (created seed M word a B aB t)+
        remainder seed M word a B aB t) t := by
  have centered : annihilation seed M t (Q (history seed M word t))=
      annihilation seed M t (history seed M word t) := by
    simp only [annihilation,ContinuousLinearMap.comp_apply,NativeWindowHistoryBathResolvent.residual_square]
  apply (mean_derivative seed M word t).congr_deriv
  have first := congrArg (fun v : wholePhysical => meanOperator seed M t (value seed M word t)+v+
    mean (load seed M word t)) centered.symm
  exact first.trans (split_response (E := H) (F := wholePhysical) (annihilation seed M t) _ _ _ _)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem created_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a) (t : ℝ) (inside : t∈Icc a B) :
    created seed M word (step.2.clockAdvance+a) (step.2.clockAdvance+B)
      (add_le_add_right aB _) (step.2.clockAdvance+t)=created step.1 M word a B aB t :=
  NativeWindowHistoryCausalResponseNext.creationResponse_next seed M step generated
    (value seed M word) (value step.1 M word) (value_continuous seed M word)
    (value_continuous step.1 M word) a B aB a0
    (fun s hs => NativeWindowHistoryAllOrderWord.value_next seed M word step generated s (a0.trans hs.1)) inside

set_option backward.isDefEq.respectTransparency false in
theorem load_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (t : ℝ) (nonnegative : 0≤t) :
    load seed M word (step.2.clockAdvance+t)=load step.1 M word t := by
  have op : action seed M (step.2.clockAdvance+t)=action step.1 M t :=
    congrArg Prod.fst (NativeWindowHistoryOseen.whole_next seed M step generated t nonnegative)
  have h := NativeWindowTraceWholeHistory.finiteHistory_next seed step generated t nonnegative M
  have f := NativeWindowHistoryOseen.forcingHistory_next seed M step generated t nonnegative
  have bracket : NativeWindowHistorySpatialWords.commutator seed M word (step.2.clockAdvance+t)=
      NativeWindowHistorySpatialWords.commutator step.1 M word t :=
    congrArg (fun A : H →L[ℝ] H => (operator M word).comp A-A.comp (operator M word)) op
  exact congrArg₂ (fun x y : H => x+y)
    (congrArg₂ (fun (A : H →L[ℝ] H) (v : H) => A v) bracket h)
    (congrArg (operator M word) f)

theorem remaining_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a) (t : ℝ) (inside : t∈Icc a B) :
    remaining seed M word (step.2.clockAdvance+a) (step.2.clockAdvance+B)
      (add_le_add_right aB _) (step.2.clockAdvance+t)=remaining step.1 M word a B aB t :=
  congrArg₂ (fun x y : H => Q x-y)
    (NativeWindowHistorySpatialWords.history_next seed M word step generated t (a0.trans inside.1))
    (created_next seed M word step generated a B aB a0 t inside)

theorem remainder_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (a B : ℝ) (aB : a≤B) (a0 : 0≤a) (t : ℝ) (inside : t∈Icc a B) :
    remainder seed M word (step.2.clockAdvance+a) (step.2.clockAdvance+B)
      (add_le_add_right aB _) (step.2.clockAdvance+t)=remainder step.1 M word a B aB t := by
  have op := congrArg (fun blocks => blocks.2.2.1)
    (NativeWindowHistoryMeanBlocks.blocks_next seed M step generated t (a0.trans inside.1))
  exact congrArg₂ (fun x y : wholePhysical => x+y)
    (congrArg₂ (fun (A : H →L[ℝ] wholePhysical) (x : H) => A x) op
      (remaining_next seed M word step generated a B aB a0 t inside))
    (congrArg mean (load_next seed M word step generated t (a0.trans inside.1)))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderCausal
