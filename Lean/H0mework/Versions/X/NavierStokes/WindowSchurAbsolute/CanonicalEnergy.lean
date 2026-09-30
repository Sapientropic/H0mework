import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.PhysicalMatter
import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.ActionWork

set_option autoImplicit false
open scoped BigOperators Matrix Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeCanonicalEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
open NativeWindowAbsoluteTimeFourier (Fiber Space realize)
open NativeWindowAbsoluteTimeSource (H history rate)
open NativeWindowAbsoluteTimePhysicalMatter (background backgroundRate coefficient timeCoefficient spaceCoefficient)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeRecoveryTimeCanonical (matterProgram)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance spaceSeminormed : SeminormedAddCommGroup Space := (inferInstance : NormedAddCommGroup Space).toSeminormedAddCommGroup
local instance historySeminormed : SeminormedAddCommGroup H := (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

section Program
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def program (b : E) (u : Coordinate → E) := matterProgram (fun _ => b) (fun _ => u) 0

theorem program_pairing (a b : E) (u v : Coordinate → E) :
    (∑ spin : Fin 4,∑ color : Fin 2,inner ℂ (program a u spin color) (program b v spin color))=
      2*inner ℂ a b+(1/8:ℂ)*(∑ i : Coordinate,inner ℂ (u i) (v i)) := by
  simp [program,matterProgram,Fin.sum_univ_four,Fin.sum_univ_two,Fin.sum_univ_three]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem program_mass (b : E) (u : Coordinate → E) :
    (∑ spin : Fin 4,∑ color : Fin 2,‖program b u spin color‖^2)=
      2*‖b‖^2+(1/8:ℝ)*(∑ i : Coordinate,‖u i‖^2) := by
  have paired:=congrArg Complex.re (program_pairing b b u u)
  simpa [inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow] using paired


theorem program_hasDerivAt {b : ℝ → E} {db : E} {u : ℝ → Coordinate → E} {du : Coordinate → E} {time : ℝ}
    (base : HasDerivAt b db time) (velocity : ∀ i,HasDerivAt (fun t => u t i) (du i) time) :
    HasDerivAt (fun t => program (b t) (u t)) (program db du) time := by
  apply hasDerivAt_pi.mpr
  intro spin
  apply hasDerivAt_pi.mpr
  intro color
  fin_cases spin <;> fin_cases color
  all_goals simp only [program,matterProgram]
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact base.add ((velocity 2).const_smul (1/4 : ℂ))
  · exact ((velocity 0).sub ((velocity 1).const_smul Complex.I)).const_smul (1/4 : ℂ)
  · exact ((velocity 0).add ((velocity 1).const_smul Complex.I)).const_smul (1/4 : ℂ)
  · exact base.sub ((velocity 2).const_smul (1/4 : ℂ))


def massForm (matrix : PhysicsCore.DiracCliffordRepresentation.DiracMatrix)
    (u v : Fin 4 → Fin 2 → E) : ℝ :=
  (∑ spin : Fin 4,∑ color : Fin 2,inner ℂ (u spin color)
    (NativeRecoveryTimeCanonical.gamma matrix v spin color)).re

theorem mass_identity (u : Fin 4 → Fin 2 → E) :
    massForm 1 u u=∑ spin : Fin 4,∑ color : Fin 2,‖u spin color‖^2 := by
  have acted : NativeRecoveryTimeCanonical.gamma 1 u=u := by
    funext spin color
    simp [NativeRecoveryTimeCanonical.gamma,Matrix.one_apply]
  rw [massForm,acted]
  simp [inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow]

theorem normalized_mass (velocity : PhysicalSpace) (u : Fin 4 → Fin 2 → E) :
    massForm (NativeCanonicalFriedrichsPrincipal.normalized velocity 0) u u=
      ∑ spin : Fin 4,∑ color : Fin 2,‖u spin color‖^2 := by
  rw [NativeCanonicalFriedrichsPrincipal.normalized_time,mass_identity]

end Program

def base (time : ℝ) : Space :=
  (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) (ContinuousMap.const Torus (background time))

def baseRate (time : ℝ) : Space :=
  (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) (ContinuousMap.const Torus (backgroundRate time))

theorem base_constant (time : ℝ) : base time=Lp.constL 2 (volume : Measure Torus) ℂ (background time) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure Torus) (ContinuousMap.const Torus (background time)),
    Lp.coeFn_const (p := 2) (μ := (volume : Measure Torus)) (background time)] with x first last
  exact first.trans last.symm

theorem baseRate_constant (time : ℝ) : baseRate time=Lp.constL 2 (volume : Measure Torus) ℂ (backgroundRate time) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure Torus) (ContinuousMap.const Torus (backgroundRate time)),
    Lp.coeFn_const (p := 2) (μ := (volume : Measure Torus)) (backgroundRate time)] with x first last
  exact first.trans last.symm

theorem base_hasDerivAt (time : ℝ) : HasDerivAt base (baseRate time) time := by
  have actual:=((Lp.constL 2 (volume : Measure Torus) ℂ : Fiber →L[ℂ] Space).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (E := Space) (F := Fiber) time (NativeWindowAbsoluteTimePhysicalMatter.background_hasDerivAt time)
  simpa only [← baseRate_constant,← base_constant,Function.comp_def] using! actual

theorem background_mass (time : ℝ) : ‖background time‖^2=1 := by
  rw [NativeWindowAbsoluteTimeIsometry.norm_square]
  calc
    _ = ∫ s : ℝ,NativeWindowKernelHalfDensity.rootKernel (time-s)^2 := by
      apply integral_congr_ae
      filter_upwards [NativeWindowAbsoluteTimePhysicalMatter.background_ae time] with s read
      rw [read,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    _ = ∫ s : ℝ,NativeWindowKernelHalfDensity.rootKernel s^2 :=
      integral_sub_left_eq_self (fun s : ℝ => NativeWindowKernelHalfDensity.rootKernel s^2) volume time
    _ = 1 := NativeWindowKernelHalfDensity.root_mass

theorem base_mass (time : ℝ) : ‖base time‖^2=1 := by
  rw [base_constant]
  change ‖Lp.const 2 (volume : Measure Torus) (background time)‖^2=1
  rw [Lp.norm_const 2 (volume : Measure Torus) (background time) (by norm_num)]
  simpa using background_mass time

theorem base_power (time : ℝ) : 2*inner ℝ (base time) (baseRate time)=0 := by
  have actual:=(base_hasDerivAt time).norm_sq
  rw [funext base_mass] at actual
  exact actual.unique (hasDerivAt_const time (1:ℝ))

def value (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (word : Fin 4) : Fin 4 → Fin 2 → Space :=
  Fin.cases (fun spin color => coefficient seed M time spin color)
    (fun j spin color => spaceCoefficient seed M time j spin color) word

def baseWord (time : ℝ) : Fin 4 → Space := Fin.cases (base time) (fun _ => 0)

private theorem realize_project (M : ℕ) (i : Coordinate) (v : H) :
    realize (modes M) i ((NativeWindowTraceWholeHistory.projection M).compLpL 2 volume v)=realize (modes M) i v :=
  congrArg (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) (NativeWindowAbsoluteTimeFourier.field_project M i v)

theorem value_program (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (word : Fin 4) :
    value seed M time word=program (baseWord time word)
      (fun i => realize (modes M) i (NativeWindowAbsoluteTimeEnergy.value seed M time word)) := by
  cases word using Fin.cases with
  | zero =>
    funext spin color
    simp only [value,baseWord,Fin.cases_zero,NativeWindowAbsoluteTimeEnergy.value,NativeWindowAbsoluteTimeEnergy.word,
      realize_project,coefficient,NativeWindowAbsoluteTimePhysicalMatter.matter,map_add,map_smul,map_sum]
    fin_cases spin <;> fin_cases color <;>
      simp [program,matterProgram,base,NativeWindowAbsoluteTimePhysicalMatter.baseWeight,
        NativeRecoveryTimeCanonicalWrite.matterMatrix,Fin.sum_univ_three,NativeWindowAbsoluteTimeFourier.realize,
        NativeWindowAbsoluteTimeFourier.physical] <;> module
  | succ j =>
    funext spin color
    simp only [value,baseWord,Fin.cases_succ,spaceCoefficient,NativeWindowAbsoluteTimePhysicalMatter.spatial,map_sum,map_smul]
    fin_cases spin <;> fin_cases color <;>
      simp [program,matterProgram,NativeRecoveryTimeCanonicalWrite.matterMatrix,Fin.sum_univ_three,
        NativeWindowAbsoluteTimeEnergy.value,NativeWindowAbsoluteTimeEnergy.word,
        NativeWindowAbsoluteTimeFourier.realize,NativeWindowAbsoluteTimeFourier.physical] <;> module


def baseWordRate (time : ℝ) : Fin 4 → Space := Fin.cases (baseRate time) (fun _ => 0)

def tangent (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (word : Fin 4) : Fin 4 → Fin 2 → Space :=
  program (baseWordRate time word)
    (fun i => realize (modes M) i (NativeWindowAbsoluteTimeEnergy.actionRate seed M time word))

theorem value_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (word : Fin 4) :
    HasDerivAt (fun t => value seed M t word) (tangent seed M time word) time := by
  have baseD : HasDerivAt (fun t => baseWord t word) (baseWordRate time word) time := by
    cases word using Fin.cases
    · exact base_hasDerivAt time
    · exact hasDerivAt_const time 0
  have rows (i : Coordinate) := (realize (modes M) i).hasFDerivAt.comp_hasDerivAt (E := Space) (F := H) time
    (NativeWindowAbsoluteTimeEnergy.value_hasDerivAt seed M time word)
  simpa only [Function.comp_apply,← value_program,tangent] using! program_hasDerivAt baseD rows

private theorem project_word (M : ℕ) (word : Fin 4) (v : H) :
    (NativeWindowTraceWholeHistory.projection M).compLpL 2 volume (NativeWindowAbsoluteTimeEnergy.word M word v)=
      NativeWindowAbsoluteTimeEnergy.word M word v := by
  let D : NativeWholeResolvent.wholePhysical →L[ℝ] NativeWholeResolvent.wholePhysical :=
    Fin.cases (NativeWindowTraceWholeHistory.projection M) (fun j => NativeWindowHistorySpatialWords.fiber M [j]) word
  have represent : NativeWindowAbsoluteTimeEnergy.word M word=D.compLpL 2 volume := by cases word using Fin.cases <;> rfl
  have projected (u : NativeWholeResolvent.wholePhysical) : NativeWindowTraceWholeHistory.projection M (D u)=D u := by
    cases word using Fin.cases <;>
      simp only [D,Fin.cases_zero,Fin.cases_succ,NativeWindowTraceWholeHistory.projection,
        NativeWindowHistorySpatialWords.fiber,NativeWindowHistoryOseen.lift,ContinuousLinearMap.comp_apply,
        NativePhysicalPairing.restrict_include]
  rw [represent]
  apply Lp.ext
  filter_upwards [(NativeWindowTraceWholeHistory.projection M).coeFn_compLpL (D.compLpL 2 volume v),D.coeFn_compLpL v]
    with s first last
  exact first.trans ((congrArg (NativeWindowTraceWholeHistory.projection M) last).trans
    ((projected (v s)).trans last.symm))

def energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  ∑ word : Fin 4,∑ spin : Fin 4,∑ color : Fin 2,‖value seed M time word spin color‖^2

theorem source_normalized_mass (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) :
    energy seed M time=∑ word : Fin 4,massForm
      (NativeCanonicalFriedrichsPrincipal.normalized (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x) 0)
      (value seed M time word) (value seed M time word) := by
  simp only [normalized_mass,energy]

def power (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  ∑ word : Fin 4,∑ spin : Fin 4,∑ color : Fin 2,2*inner ℝ (value seed M time word spin color) (tangent seed M time word spin color)

theorem energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (energy seed M) (power seed M time) time := by
  have each (word : Fin 4) (spin : Fin 4) (color : Fin 2) :=
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp (value_hasDerivAt seed M time word) spin) color).norm_sq
  simpa only [energy,power,Finset.sum_apply] using!
    HasDerivAt.sum (u := Finset.univ) (fun word _ => HasDerivAt.sum (u := Finset.univ)
      (fun spin _ => HasDerivAt.sum (u := Finset.univ) (fun color _ => each word spin color)))

theorem energy_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    energy seed M time=2+(1/8:ℝ)*NativeWindowAbsoluteTimeEnergy.energy seed M time := by
  have each (word : Fin 4) : (∑ spin : Fin 4,∑ color : Fin 2,‖value seed M time word spin color‖^2)=
      2*‖baseWord time word‖^2+(1/8:ℝ)*‖NativeWindowAbsoluteTimeEnergy.value seed M time word‖^2 := by
    rw [value_program,program_mass,NativeWindowAbsoluteTimeFourier.physical_mass_exact,
      NativeWindowAbsoluteTimeEnergy.value,project_word]
  have bases : (∑ word : Fin 4,2*‖baseWord time word‖^2)=2 := by
    simp [Fin.sum_univ_succ,baseWord,base_mass]
  simp only [energy,each,Finset.sum_add_distrib,← Finset.mul_sum,bases]
  rfl

theorem power_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    power seed M time=(1/8:ℝ)*NativeWindowAbsoluteTimeEnergy.power seed M time := by
  have actual:=energy_hasDerivAt seed M time
  rw [funext (energy_original seed M)] at actual
  exact actual.unique (((NativeWindowAbsoluteTimeEnergy.energy_hasDerivAt seed M time).const_mul (1/8:ℝ)).const_add 2)

theorem native_power (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    power seed M time=(1/8:ℝ)*NativeWindowAbsoluteTimeActionWork.originalPower seed M time := by
  rw [power_original,NativeWindowAbsoluteTimeActionWork.power_original]

theorem source_energy_power_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0≤C ∧∀ M,∀ time∈Icc 0 horizon,
      energy seed M time≤C ∧ |power seed M time|≤C := by
  obtain ⟨B,B0,paid⟩:=NativeWindowAbsoluteTimeEnergy.source_energy_power_bound seed horizon
  refine ⟨2+B/8,by positivity,fun M time inside => ?_⟩
  have original:=paid M time inside
  rw [energy_original,power_original,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/8)]
  constructor <;> linarith

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem energy_power_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    energy seed M (step.2.clockAdvance+time)=energy step.1 M time ∧ power seed M (step.2.clockAdvance+time)=power step.1 M time := by
  obtain ⟨first,last⟩:=NativeWindowAbsoluteTimeEnergy.energy_power_next seed M step generated time nonnegative
  simp only [energy_original,power_original,first,last,and_self]

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeCanonicalEnergy
