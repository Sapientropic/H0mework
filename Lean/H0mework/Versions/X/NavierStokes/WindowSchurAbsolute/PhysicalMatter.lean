import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.Fourier
import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.GNS
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.Complete
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.CompleteDensityForm

set_option autoImplicit false
open scoped BigOperators Matrix Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimePhysicalMatter
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus ScalarSequence)
open NativeWholeH1Mixed (modes)
open NativeWindowAbsoluteTimeSource (H history rate)
open NativeWindowAbsoluteTimeFourier (Fiber Space field realize)
open NativeRecoveryTimeCanonicalWrite (matterMatrix)
open PhysicsCore.DiracCliffordRepresentation PhysicsCore.DiracExteriorMatterAction PhysicsCore.StageNineHolonomicField
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance fiberSeminormed : SeminormedAddCommGroup Fiber := (inferInstance : NormedAddCommGroup Fiber).toSeminormedAddCommGroup
local instance spaceSeminormed : SeminormedAddCommGroup Space := (inferInstance : NormedAddCommGroup Space).toSeminormedAddCommGroup
local instance historySeminormed : SeminormedAddCommGroup H := (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

abbrev Spinor := Fin 4 → Fin 2 → Fiber
abbrev WholeMatter := MatterCoordinateIndex → Fiber

def baseRead : NativeWindowAbsoluteTimeGNS.Scalar →L[ℝ] Fiber :=
  (lp.evalCLM ℝ (fun _ : IntegerWavevector => ℂ) 2 0).compLpL 2 (volume : Measure ℝ)

def background (time : ℝ) : Fiber := baseRead (NativeWindowAbsoluteTimeGNS.background 0 time)
def backgroundRate (time : ℝ) : Fiber := baseRead (NativeWindowAbsoluteTimeGNS.backgroundRate 0 time)

theorem background_hasDerivAt (time : ℝ) : HasDerivAt background (backgroundRate time) time :=
  baseRead.hasFDerivAt.comp_hasDerivAt (E := Fiber) (F := NativeWindowAbsoluteTimeGNS.Scalar) time
    (NativeWindowAbsoluteTimeGNS.background_hasDerivAt 0 time)

theorem background_ae (time : ℝ) : background time=ᵐ[volume]
    fun s => (NativeWindowKernelHalfDensity.rootKernel (time-s) : ℂ) := by
  filter_upwards [(lp.evalCLM ℝ (fun _ : IntegerWavevector => ℂ) 2 0).coeFn_compLpL
    (NativeWindowAbsoluteTimeGNS.background 0 time),
    NativeWindowAbsoluteTimeCarrier.field_ae NativeWindowKernelHalfDensity.rootKernel
      (NativeWindowKernelHalfDensity.root_memLp 2) (fun _ => (lp.single 2 (0 : IntegerWavevector) (1 : ℂ) : ScalarSequence))
      (memLp_top_const _) time] with s read original
  change background time s=_ at read
  change NativeWindowAbsoluteTimeGNS.background 0 time s=_ at original
  rw [read,original,map_smul]
  change NativeWindowKernelHalfDensity.rootKernel (time-s) • (lp.single 2 (0 : IntegerWavevector) (1 : ℂ) : ScalarSequence) 0=_
  simp

def baseWeight : Fin 4 → Fin 2 → ℂ := !![0,0;0,0;1,0;0,1]

def matter (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (spin : Fin 4) (color : Fin 2) : C(Torus,Fiber) :=
  baseWeight spin color • ContinuousMap.const Torus (background time)+
    ∑ i : Coordinate,matterMatrix spin color i • field (modes M) i (history seed time)

def temporal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (spin : Fin 4) (color : Fin 2) : C(Torus,Fiber) :=
  baseWeight spin color • ContinuousMap.const Torus (backgroundRate time)+
    ∑ i : Coordinate,matterMatrix spin color i • field (modes M) i (rate seed time)

def spatial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate)
    (spin : Fin 4) (color : Fin 2) : C(Torus,Fiber) :=
  ∑ i : Coordinate,matterMatrix spin color i •
    field (modes M) i (NativeWindowAbsoluteTimeGradient.spatial M j (history seed time))

def coefficient (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (spin : Fin 4) (color : Fin 2) : Space := (ContinuousMap.toLp 2 volume ℂ) (matter seed M time spin color)

def timeCoefficient (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (spin : Fin 4) (color : Fin 2) : Space := (ContinuousMap.toLp 2 volume ℂ) (temporal seed M time spin color)

def spaceCoefficient (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate)
    (spin : Fin 4) (color : Fin 2) : Space := (ContinuousMap.toLp 2 volume ℂ) (spatial seed M time j spin color)

theorem coefficient_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (spin : Fin 4) (color : Fin 2) :
    coefficient seed M time spin color=ᵐ[volume] matter seed M time spin color :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume _

private theorem constant_physical (v : Fiber) :
    (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) (ContinuousMap.const Torus v)=Lp.constL 2 volume ℂ v := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure Torus) (ContinuousMap.const Torus v),
    Lp.coeFn_const (p := 2) (μ := (volume : Measure Torus)) v] with x first last
  exact first.trans last.symm

theorem coefficient_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (spin : Fin 4) (color : Fin 2) :
    HasDerivAt (fun t => coefficient seed M t spin color) (timeCoefficient seed M time spin color) time := by
  have base:=((Lp.constL 2 (volume : Measure Torus) ℂ : Fiber →L[ℂ] Space).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (E := Space) (F := Fiber) time (background_hasDerivAt time)
  have each (i : Coordinate) := (NativeWindowAbsoluteTimeFourier.source_hasDerivAt seed (modes M) i time).const_smul (matterMatrix spin color i)
  have combined := (base.const_smul (baseWeight spin color)).add (HasDerivAt.sum (u := Finset.univ) (fun i _ => each i))
  convert combined using 1
  · funext t
    simp only [coefficient,matter,map_add,map_sum,map_smul,constant_physical,
      Pi.add_apply,Pi.smul_apply,Finset.sum_apply,Function.comp_apply]
    rfl
  · simp only [timeCoefficient,temporal,map_add,map_sum,map_smul,constant_physical]
    rfl

theorem matter_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus)
    (spin : Fin 4) (color : Fin 2) :
    HasDerivAt (fun t => matter seed M t spin color x) (temporal seed M time spin color x) time := by
  have each (i : Coordinate) : HasDerivAt (fun t => field (modes M) i (history seed t) x)
      (field (modes M) i (rate seed time) x) time := by
    simp only [NativeWindowAbsoluteTimeFourier.field_evaluation]
    exact ((NativeWindowAbsoluteTimeFourier.evaluation (modes M) i x).compLpL 2 (volume : Measure ℝ)).hasFDerivAt.comp_hasDerivAt
      (E := Fiber) (F := H) time (NativeWindowAbsoluteTimeSource.source_hasDerivAt seed time)
  have combined := ((background_hasDerivAt time).const_smul (baseWeight spin color)).add
    (HasDerivAt.sum (u := Finset.univ) (fun i _ => (each i).const_smul (matterMatrix spin color i)))
  convert combined using 1
  · funext t
    simp only [matter,ContinuousMap.add_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
      ContinuousMap.const_apply,Finset.sum_apply,Pi.smul_apply,Pi.add_apply]
  · rfl

theorem ordinary_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate)
    (x : Torus) (spin : Fin 4) (color : Fin 2) :
    HasDerivAt (fun z : ℝ => matter seed M time spin color (x+NativePhysicalTranslation.displacement j z))
      (spatial seed M time j spin color x) 0 := by
  have each (i : Coordinate) := (NativeWindowAbsoluteTimeFourier.field_hasDerivAt M i j (history seed time) x).const_smul (matterMatrix spin color i)
  have combined := (HasDerivAt.sum (u := Finset.univ) (fun i _ => each i)).const_add
    (baseWeight spin color • background time)
  simpa only [matter,spatial,ContinuousMap.add_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    ContinuousMap.const_apply,Finset.sum_apply,Pi.smul_apply,Pi.add_apply] using combined


def translatedMatter (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate)
    (spin : Fin 4) (color : Fin 2) (z : ℝ) : C(Torus,Fiber) :=
  (matter seed M time spin color).comp
    ⟨fun x => x+NativePhysicalTranslation.displacement j z,continuous_id.add continuous_const⟩

theorem ordinary_strong (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate)
    (spin : Fin 4) (color : Fin 2) :
    HasDerivAt (fun z => (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ)
      (translatedMatter seed M time j spin color z)) (spaceCoefficient seed M time j spin color) 0 := by
  have each (i : Coordinate) :=
    (NativeWindowAbsoluteTimeFourier.polynomial_spatial_strong (modes M)
      (fun k => NativeWindowAbsoluteTimeFourier.row k i (history seed time)) j).const_smul (matterMatrix spin color i)
  have combined := (HasDerivAt.sum (u := Finset.univ) (fun i _ => each i)).const_add
    (baseWeight spin color • ContinuousMap.const Torus (background time))
  have actual : HasDerivAt (translatedMatter seed M time j spin color) (spatial seed M time j spin color) 0 := by
    convert combined using 1
    · funext z
      apply ContinuousMap.ext
      intro x
      simp only [translatedMatter,matter,ContinuousMap.comp_apply,ContinuousMap.coe_mk,ContinuousMap.add_apply,
        ContinuousMap.sum_apply,ContinuousMap.smul_apply,ContinuousMap.const_apply,Finset.sum_apply,Pi.smul_apply,
        NativeWindowAbsoluteTimeFourier.translatedPolynomial,NativeWindowAbsoluteTimeFourier.field]
    · apply ContinuousMap.ext
      intro x
      simp only [spatial,ContinuousMap.sum_apply,ContinuousMap.smul_apply]
      exact Finset.sum_congr rfl fun i _ => congrArg (fun v : Fiber => matterMatrix spin color i • v)
        (NativeWindowAbsoluteTimeFourier.field_spatial M i j (history seed time) x)
  exact ((ContinuousMap.toLp 2 (volume : Measure Torus) ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (E := Space) (F := C(Torus,Fiber)) 0 actual

def extension (A : Module.End ℂ DiracExteriorMatterCarrier) (v : Spinor) : WholeMatter :=
  fun index => ∑ spin : Fin 4,∑ color : Fin 2,
    (matterCoordinateEquiv (A (NativeWindowStageTenWholeFirstJet.materialBasis spin color)) index) • v spin color

def lower (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) : Module.End ℂ DiracExteriorMatterCarrier :=
  ∑ direction : Fin 4,(diracMatrixMatterAction (NativeCanonicalFriedrichsPrincipal.matrix velocity direction)).comp
    (NativeBalancedMaterialJet.connectionOperator velocity jet direction)

def firstJet (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) : Fin 4 → Spinor :=
  Fin.cases (fun spin color => temporal seed M time spin color x)
    (fun j spin color => spatial seed M time j spin color x)

def densitizedAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time) (x : Torus) : WholeMatter :=
  (∑ direction : Fin 4,extension (diracMatrixMatterAction
    (NativeCanonicalFriedrichsPrincipal.matrix (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x) direction))
      (firstJet seed M time x direction))+
    extension (lower (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)
      (NativeWindowStageTenWholeFirstJet.sourceJet seed time valid x)) (fun spin color => matter seed M time spin color x)

def normalizedAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time) (x : Torus) : WholeMatter :=
  (∑ direction : Fin 4,extension (diracMatrixMatterAction
    (NativeCanonicalFriedrichsPrincipal.normalized (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x) direction))
      (firstJet seed M time x direction))+
    extension (NativeCanonicalFriedrichsAction.lower (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)
      (NativeWindowStageTenWholeFirstJet.sourceJet seed time valid x)) (fun spin color => matter seed M time spin color x)

theorem extension_smul (a : ℂ) (A : Module.End ℂ DiracExteriorMatterCarrier) (v : Spinor) :
    extension (a • A) v=a • extension A v := by
  have coord (u : DiracExteriorMatterCarrier) (index : MatterCoordinateIndex) :
      matterCoordinateEquiv (a • u) index=a*matterCoordinateEquiv u index :=
    congrArg (fun z : MatterCoordinateCarrier => z index) (matterCoordinateEquiv.map_smul a u)
  funext index
  simp only [extension,LinearMap.smul_apply,coord,Pi.smul_apply,Finset.smul_sum,smul_smul]

private theorem dirac_smul (a : ℂ) (A : DiracMatrix) :
    diracMatrixMatterAction (a • A)=a • diracMatrixMatterAction A := by
  apply LinearMap.ext
  intro v
  exact PhysicsCore.StageNineP286GaugeConnectionVariationDensity.diracMatrixMatterAction_smul_matrix a A v

theorem lower_normalized (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    (NativeCanonicalFluidCoframe.density velocity : ℂ) • lower velocity jet=NativeCanonicalFriedrichsAction.lower velocity jet := by
  simp only [lower,NativeCanonicalFriedrichsAction.lower,Finset.smul_sum,NativeCanonicalFriedrichsPrincipal.normalized,
    dirac_smul,LinearMap.smul_comp]

theorem action_normalized (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time) (x : Torus) :
    (NativeCanonicalFluidCoframe.density (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x) : ℂ) •
      densitizedAction seed M time valid x=normalizedAction seed M time valid x := by
  simp only [densitizedAction,normalizedAction,smul_add,Finset.smul_sum,← extension_smul,lower_normalized,
    NativeCanonicalFriedrichsPrincipal.normalized,
    dirac_smul]


open NativeWindowGreenTestForm (Test SpinFiber decode)

def support (M : ℕ) : Finset IntegerWavevector := insert 0 (modes M)

def coefficientRow (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (k : IntegerWavevector) : SpinFiber Fiber :=
  WithLp.toLp 2 fun entry : Fin 4 × Fin 2 =>
    (if k=0 then baseWeight entry.1 entry.2 • background time else 0)+
    if k∈modes M then ∑ i : Coordinate,matterMatrix entry.1 entry.2 i • NativeWindowAbsoluteTimeFourier.row k i (history seed time) else 0

def sourceTest (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : Test (SpinFiber Fiber) :=
  ∑ k∈support M,lp.single 2 k ((Real.sqrt (NativeCompleteStressCarrier.weight k))⁻¹ • coefficientRow seed M time k)

theorem sourceTest_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (k : IntegerWavevector) :
    decode (sourceTest seed M time) k=if k∈support M then coefficientRow seed M time k else 0 := by
  classical
  change Real.sqrt (NativeCompleteStressCarrier.weight k) • (sourceTest seed M time) k=_
  simp only [sourceTest,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]
  split_ifs with inside
  · rw [smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr (NativeCompleteStressCarrier.weight_pos k)).ne',one_smul]
  · exact smul_zero _

theorem physicalTest_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) :
    NativeWindowGreenSourceForm.physicalTest (support M) (sourceTest seed M time) x=
      WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => matter seed M time entry.1 entry.2 x) := by
  have read : (∑ k∈support M,UnitAddTorus.mFourier k x • decode (sourceTest seed M time) k)=
      ∑ k∈support M,UnitAddTorus.mFourier k x • coefficientRow seed M time k :=
    Finset.sum_congr rfl fun k inside => by rw [sourceTest_read,if_pos inside]
  refine read.trans ?_
  apply PiLp.ext
  intro entry
  simp only [support,Finset.sum_insert (NativeWholeH1Mixed.modes_zero M),WithLp.ofLp_add,WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,
    Pi.add_apply,Pi.smul_apply,coefficientRow,ite_true,if_neg (NativeWholeH1Mixed.modes_zero M),add_zero,
    UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,one_smul]
  have row (k : IntegerWavevector) (inside : k∈modes M) :
      (if k=0 then baseWeight entry.1 entry.2 • background time else 0)+
        (if k∈modes M then ∑ i : Coordinate,matterMatrix entry.1 entry.2 i • NativeWindowAbsoluteTimeFourier.row k i (history seed time) else 0)=
      ∑ i : Coordinate,matterMatrix entry.1 entry.2 i • NativeWindowAbsoluteTimeFourier.row k i (history seed time) := by
    have nonzero : k≠0 := fun equal => NativeWholeH1Mixed.modes_zero M (equal ▸ inside)
    simp only [if_neg nonzero,if_pos inside,zero_add]
  change _=baseWeight entry.1 entry.2 • background time+
    ∑ i : Coordinate,matterMatrix entry.1 entry.2 i •
      (∑ k∈modes M,UnitAddTorus.mFourier k x • NativeWindowAbsoluteTimeFourier.row k i (history seed time))
  congr 1
  calc
    _ = ∑ k∈modes M,UnitAddTorus.mFourier k x •
        (∑ i : Coordinate,matterMatrix entry.1 entry.2 i • NativeWindowAbsoluteTimeFourier.row k i (history seed time)) :=
      Finset.sum_congr rfl fun k inside => congrArg (fun z : Fiber => UnitAddTorus.mFourier k x • z) (row k inside)
    _ = _ := by
      simp only [Finset.smul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _


theorem physical_remainder (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time horizon : ℝ)
    (valid : -1 < time) (before : time≤horizon) :
    ‖∑ direction : Fin 4,∫ x : Torus,NativeWindowGreenCompleteForm.physicalCoefficient seed time valid direction x*
      inner ℂ (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => matter seed M time entry.1 entry.2 x))
        (NativeWindowGreenCompleteForm.operator direction
          (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => matter seed M time entry.1 entry.2 x)))‖≤
      nu.coeff*((2*Real.pi)^2*NativeWindowGreenTestForm.gradient
        (NativeWindowGreenSourceForm.project (support M) (sourceTest seed M time)))+
      NativeWindowGreenCompleteForm.formBudget seed horizon*‖decode
        (NativeWindowGreenSourceForm.project (support M) (sourceTest seed M time))‖^2 := by
  simpa only [physicalTest_original] using! NativeWindowGreenCompleteForm.physical_remainder_bound
    seed time horizon valid before (support M) (sourceTest seed M time)

theorem complete_density_payment (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) :
    ∃ C : ℝ,0≤C ∧∀ M,∀ time : Icc (0 : ℝ) horizon,
      ‖NativeWindowCompleteDensityForm.remainder seed order time (by linarith [time.property.1])
        (sourceTest seed M time)‖≤nu.coeff*((2*Real.pi)^2*NativeWindowGreenTestForm.gradient (sourceTest seed M time))+
          C*‖decode (sourceTest seed M time)‖^2 := by
  obtain ⟨C,C0,paid⟩:=NativeWindowCompleteDensityForm.exists_uniform_bound seed order horizon
  exact ⟨C,C0,fun M time => paid time Fiber (sourceTest seed M time)⟩

def rawTemporal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) : Spinor :=
  fun spin color => baseWeight spin color • backgroundRate time+
    ∑ i : Coordinate,matterMatrix spin color i •
      (field (modes M) i (NativeWindowAbsoluteTimeBridge.absoluteAction seed M time
        (NativeWindowAbsoluteTimeBridge.finiteHistory seed M time)) x+
       field (modes M) i (NativeWindowAbsoluteTimeIsometry.map NativeWholeResolvent.wholePhysical time
        (NativeWindowHistoryOseen.forcingHistory seed M time)) x-
       field (modes M) i (NativeWindowAbsoluteTimeBridge.sampleDerivative seed M time) x)

theorem rawTemporal_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) :
    rawTemporal seed M time x=fun spin color => temporal seed M time spin color x := by
  have rows : (fun i : Coordinate => field (modes M) i (rate seed time) x)=
      fun i => field (modes M) i (NativeWindowAbsoluteTimeBridge.absoluteAction seed M time
        (NativeWindowAbsoluteTimeBridge.finiteHistory seed M time)) x+
       field (modes M) i (NativeWindowAbsoluteTimeIsometry.map NativeWholeResolvent.wholePhysical time
        (NativeWindowHistoryOseen.forcingHistory seed M time)) x-
       field (modes M) i (NativeWindowAbsoluteTimeBridge.sampleDerivative seed M time) x :=
    funext fun i => NativeWindowAbsoluteTimeFourier.source_action seed M i time x
  funext spin color
  exact (congrArg (fun c : Coordinate → Fiber => baseWeight spin color • backgroundRate time+
    ∑ i : Coordinate,matterMatrix spin color i • c i) rows).symm

-- The coframe uses the original mean velocity; all same-sample raw action and full forcing stay in this source.
def sourceForcing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time) (x : Torus) : WholeMatter :=
  (∑ direction : Fin 4,extension (diracMatrixMatterAction
    (NativeCanonicalFriedrichsPrincipal.matrix (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x) direction))
      (Fin.cases (rawTemporal seed M time x) (fun j spin color => spatial seed M time j spin color x) direction))+
    extension (lower (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)
      (NativeWindowStageTenWholeFirstJet.sourceJet seed time valid x)) (fun spin color => matter seed M time spin color x)

theorem actual_source_action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time) (x : Torus) :
    densitizedAction seed M time valid x=sourceForcing seed M time valid x := by
  simp only [densitizedAction,sourceForcing,firstJet,rawTemporal_original]

def retainedSpatial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time) (x : Torus) : WholeMatter :=
  (∑ j : Coordinate,extension (diracMatrixMatterAction (diracFrameEvolutionPrincipal j.succ))
    (fun spin color => spatial seed M time j spin color x))+
    extension (lower (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)
      (NativeWindowStageTenWholeFirstJet.sourceJet seed time valid x)) (fun spin color => matter seed M time spin color x)

private theorem matrix_time (v : PhysicalSpace) :
    diracMatrixMatterAction (NativeCanonicalFriedrichsPrincipal.matrix v 0)=
      ((NativeCanonicalFluidCoframe.density v)⁻¹ : ℂ) • (LinearMap.id : Module.End ℂ DiracExteriorMatterCarrier) := by
  have unit : diracMatrixMatterAction (1 : DiracMatrix)=LinearMap.id := by
    apply LinearMap.ext
    intro value
    funext spin
    simp [diracMatrixMatterAction,Matrix.one_apply]
  rw [NativeCanonicalFriedrichsPrincipal.mass]
  change diracMatrixMatterAction ((((NativeCanonicalFluidCoframe.density v)⁻¹ : ℝ) : ℂ) • (1 : DiracMatrix))=_
  rw [dirac_smul,unit,Complex.ofReal_inv]

theorem full_forcing_slot (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 ≤ time) (x : Torus) :
    sourceForcing seed M time valid x=
      ((NativeCanonicalFluidCoframe.density (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x))⁻¹ : ℂ) •
        extension LinearMap.id (fun spin color => temporal seed M time spin color x)+retainedSpatial seed M time valid x := by
  simp only [sourceForcing,retainedSpatial,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,
    rawTemporal_original,matrix_time,NativeCanonicalFriedrichsPrincipal.spatial,extension_smul]
  abel

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimePhysicalMatter
