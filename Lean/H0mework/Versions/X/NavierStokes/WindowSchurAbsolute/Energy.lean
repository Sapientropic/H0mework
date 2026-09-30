import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.Bridge
import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.Gradient

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowAbsoluteTimeSource (H history rate)
open NativeWindowAbsoluteTimeBridge (finiteHistory finiteRate absoluteAction sampleDerivative)
open NativeWindowAbsoluteTimeGradient (spatial)
noncomputable section
variable {nu : Viscosity}

def word (M : ℕ) : Fin 4 → H →L[ℝ] H := Fin.cases
  ((NativeWindowTraceWholeHistory.projection M).compLpL 2 volume) (spatial M)

private theorem lp_project {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D P : E →L[ℝ] E) (same : ∀ u,D (P u)=D u) (v : Lp E 2 (volume : Measure ℝ)) :
    D.compLpL 2 volume (P.compLpL 2 volume v)=D.compLpL 2 volume v := by
  apply Lp.ext
  filter_upwards [D.coeFn_compLpL (P.compLpL 2 volume v),P.coeFn_compLpL v,D.coeFn_compLpL v]
    with sample first middle last
  rw [first,middle,last]
  exact same (v sample)

theorem word_project (M : ℕ) (direction : Fin 4) (v : H) :
    word M direction ((NativeWindowTraceWholeHistory.projection M).compLpL 2 volume v)=word M direction v := by
  have point (j : Fin 4) (u : wholePhysical) :
      (Fin.cases (motive := fun _ => wholePhysical →L[ℝ] wholePhysical) (NativeWindowTraceWholeHistory.projection M)
        (fun i => NativeWindowHistorySpatialWords.fiber M [i]) j)
        (NativeWindowTraceWholeHistory.projection M u)=
      (Fin.cases (motive := fun _ => wholePhysical →L[ℝ] wholePhysical) (NativeWindowTraceWholeHistory.projection M)
        (fun i => NativeWindowHistorySpatialWords.fiber M [i]) j) u := by
    refine Fin.cases ?_ (fun i => ?_) j <;>
      simp only [Fin.cases_zero,Fin.cases_succ,NativeWindowTraceWholeHistory.projection,
        NativeWindowHistorySpatialWords.fiber,NativeWindowHistoryOseen.lift,
        ContinuousLinearMap.comp_apply,NativePhysicalPairing.restrict_include]
  let D : wholePhysical →L[ℝ] wholePhysical:=Fin.cases (NativeWindowTraceWholeHistory.projection M)
    (fun i => NativeWindowHistorySpatialWords.fiber M [i]) direction
  have same : word M direction=D.compLpL 2 volume := by cases direction using Fin.cases <;> rfl
  rw [same]
  exact lp_project (E := wholePhysical) D (NativeWindowTraceWholeHistory.projection M)
    (point direction) v

def value (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (direction : Fin 4) : H :=
  word M direction (history seed time)

def tangent (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (direction : Fin 4) : H :=
  word M direction (rate seed time)

def commutator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (direction : Fin 4) : H →L[ℝ] H :=
  (word M direction).comp (absoluteAction seed M time)-(absoluteAction seed M time).comp (word M direction)

def actionRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (direction : Fin 4) : H :=
  absoluteAction seed M time (value seed M time direction)+
    commutator seed M time direction (finiteHistory seed M time)+
    word M direction (NativeWindowAbsoluteTimeIsometry.map wholePhysical time
      (NativeWindowHistoryOseen.forcingHistory seed M time))-
    word M direction (sampleDerivative seed M time)

private theorem linear_action {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D A : E →L[ℝ] E) (v f s : E) :
    D (A v+f-s)=A (D v)+(D.comp A-A.comp D) v+D f-D s := by
  rw [map_sub,map_add]
  simp only [sub_apply,ContinuousLinearMap.comp_apply]
  abel

theorem source_action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (direction : Fin 4) :
    tangent seed M time direction=actionRate seed M time direction := by
  have equation:=congrArg (fun v : H => word M direction v)
    (NativeWindowAbsoluteTimeBridge.source_equation seed M time)
  simp only [map_add,map_sub] at equation
  have left : word M direction (finiteRate seed M time)=tangent seed M time direction :=
    word_project M direction (rate seed time)
  have state : word M direction (finiteHistory seed M time)=value seed M time direction :=
    word_project M direction (history seed time)
  have algebra:=linear_action (E := H) (word M direction) (absoluteAction seed M time)
    (finiteHistory seed M time)
    (NativeWindowAbsoluteTimeIsometry.map wholePhysical time (NativeWindowHistoryOseen.forcingHistory seed M time))
    (sampleDerivative seed M time)
  simp only [map_add,map_sub,state] at algebra
  exact (left.symm.trans equation).trans algebra

theorem value_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (direction : Fin 4) :
    HasDerivAt (fun t => value seed M t direction) (actionRate seed M time direction) time := by
  rw [← source_action]
  exact (word M direction).hasFDerivAt.comp_hasDerivAt (E := H) (F := H) time
    (NativeWindowAbsoluteTimeSource.source_hasDerivAt seed time)

def energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  ∑ direction,‖value seed M time direction‖^2

def power (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  ∑ direction,2*inner ℝ (value seed M time direction) (actionRate seed M time direction)

theorem energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (energy seed M) (power seed M time) time := by
  simpa only [energy,power,Finset.sum_apply] using!
    HasDerivAt.sum (u := Finset.univ) (fun direction _ =>
      HasDerivAt.norm_sq (F := H) (value_hasDerivAt seed M time direction))

private theorem lp_contract {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (contract : ∀ u,‖P u‖ ≤ ‖u‖) (v : Lp E 2 (volume : Measure ℝ)) :
    ‖P.compLpL 2 volume v‖ ≤ ‖v‖ := by
  have point : ‖P‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun u => by simpa only [one_mul] using contract u)
  have lifted:‖P.compLpL 2 (volume : Measure ℝ)‖ ≤ 1:=P.norm_compLpL_le.trans point
  exact ((P.compLpL 2 volume).le_opNorm v).trans
    ((mul_le_mul_of_nonneg_right lifted (norm_nonneg v)).trans_eq (one_mul _))

private theorem projection_bound (M : ℕ) (v : H) :
    ‖(NativeWindowTraceWholeHistory.projection M).compLpL 2 volume v‖ ≤ ‖v‖ :=
  lp_contract (E := wholePhysical) (NativeWindowTraceWholeHistory.projection M)
    (NativeWindowHistoryWholeRecovery.projection_norm M) v

theorem source_first_jet_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧∀ M direction,∀ time∈Icc 0 horizon,
      ‖value seed M time direction‖^2+‖tangent seed M time direction‖^2 ≤ C := by
  obtain ⟨A,bounded⟩:=NativeWindowKernelHalfDensity.compact.exists_bound_of_continuous NativeWindowKernelHalfDensity.continuous
  obtain ⟨B,B0,paid⟩:=NativeWindowAbsoluteTimeGradient.source_rate_spatial_bound seed horizon
  let K:=(A^2/nu.coeff)*NativeWindowHistoryCrossBudget.energyBudget seed horizon
  let L:=NativeUnifiedCompleteSource.budget seed
  let R:=NativeWindowAbsoluteTimeSource.rateBudget seed
  refine ⟨L^2+R^2+max 0 K+B,by positivity,fun M direction time inside => ?_⟩
  refine Fin.cases ?_ (fun j => ?_) direction
  · have mass : ‖value seed M time 0‖ ≤ L := by
      apply (projection_bound M (history seed time)).trans
      rw [← NativeWindowAbsoluteTimeBridge.source_map]
      exact ((NativeWindowAbsoluteTimeIsometry.map wholePhysical time).norm_map _).trans_le
        (NativeWindowTraceWholeHistory.history_bound seed time)
    have differential : ‖tangent seed M time 0‖ ≤ R :=
      (projection_bound M (rate seed time)).trans (NativeWindowAbsoluteTimeSource.source_rate_bound seed time)
    have first:=pow_le_pow_left₀ (norm_nonneg (value seed M time 0)) mass 2
    have last:=pow_le_pow_left₀ (norm_nonneg (tangent seed M time 0)) differential 2
    linarith [le_max_left (0:ℝ) K]
  · have first:=NativeWindowAbsoluteTimeGradient.source_field_bound NativeWindowKernelHalfDensity.rootKernel
      (NativeWindowKernelHalfDensity.root_memLp 2) NativeWindowAbsoluteTimeSource.root_zero_outside A bounded
      seed horizon M j time inside
    have last:=paid M j time inside
    change ‖value seed M time j.succ‖^2 ≤ K at first
    change ‖tangent seed M time j.succ‖^2 ≤ B at last
    nlinarith [le_max_right (0:ℝ) K,sq_nonneg L,sq_nonneg R]

private theorem pairing_bound (u v : H) : |2*inner ℝ u v| ≤ ‖u‖^2+‖v‖^2 := by
  have pair:=abs_real_inner_le_norm u v
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

theorem source_energy_power_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ time∈Icc 0 horizon,
      energy seed M time ≤ C ∧ |power seed M time| ≤ C := by
  obtain ⟨C,C0,paid⟩:=source_first_jet_bound seed horizon
  refine ⟨4*C,mul_nonneg (by norm_num) C0,fun M time inside => ⟨?_,?_⟩⟩
  · have each (j : Fin 4) : ‖value seed M time j‖^2 ≤ C := by
      linarith [paid M j time inside,sq_nonneg ‖tangent seed M time j‖]
    simpa only [energy,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun j _ => each j)
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    have each (j : Fin 4) : |2*inner ℝ (value seed M time j) (actionRate seed M time j)| ≤ C := by
      rw [← source_action]
      exact (pairing_bound _ _).trans (paid M j time inside)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun j _ => each j)

private theorem clock_natural {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : E →L[ℝ] E) (advance : ℝ) (v : Lp E 2 (volume : Measure ℝ)) :
    D.compLpL 2 volume (NativeWindowAbsoluteTimeIsometry.clock E advance v)=
      NativeWindowAbsoluteTimeIsometry.clock E advance (D.compLpL 2 volume v) := by
  have preserves : MeasurePreserving (fun s : ℝ => s-advance) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-advance)
  have shifted:=preserves.quasiMeasurePreserving.ae (D.coeFn_compLpL v)
  apply Lp.ext
  filter_upwards [D.coeFn_compLpL (NativeWindowAbsoluteTimeIsometry.clock E advance v),
    NativeWindowAbsoluteTimeIsometry.clock_ae E advance v,
    NativeWindowAbsoluteTimeIsometry.clock_ae E advance (D.compLpL 2 volume v),shifted]
    with s first middle last original
  rw [first,middle,last,original]

theorem word_clock (M : ℕ) (direction : Fin 4) (advance : ℝ) (v : H) :
    word M direction (NativeWindowAbsoluteTimeIsometry.clock wholePhysical advance v)=
      NativeWindowAbsoluteTimeIsometry.clock wholePhysical advance (word M direction v) := by
  cases direction using Fin.cases <;> exact clock_natural (E := wholePhysical) _ advance v

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem value_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (direction : Fin 4) : value seed M (step.2.clockAdvance+time) direction=
      NativeWindowAbsoluteTimeIsometry.clock wholePhysical step.2.clockAdvance (value step.1 M time direction) := by
  rw [value,NativeWindowAbsoluteTimeBridge.source_next seed step generated time nonnegative,word_clock]
  rfl

theorem actionRate_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (direction : Fin 4) : actionRate seed M (step.2.clockAdvance+time) direction=
      NativeWindowAbsoluteTimeIsometry.clock wholePhysical step.2.clockAdvance (actionRate step.1 M time direction) := by
  rw [← source_action,← source_action,tangent,
    NativeWindowAbsoluteTimeBridge.rate_next seed step generated time nonnegative,word_clock]
  rfl

theorem energy_power_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    energy seed M (step.2.clockAdvance+time)=energy step.1 M time ∧
      power seed M (step.2.clockAdvance+time)=power step.1 M time := by
  simp only [energy,power,value_next seed M step generated time nonnegative,
    actionRate_next seed M step generated time nonnegative,
    (NativeWindowAbsoluteTimeIsometry.clock wholePhysical step.2.clockAdvance).norm_map,
    LinearIsometry.inner_map_map (𝕜 := ℝ) (E := H) (E' := H)
      (NativeWindowAbsoluteTimeIsometry.clock wholePhysical step.2.clockAdvance),and_self]

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeEnergy
