import H0mework.Versions.X.NavierStokes.WindowSourceGreen.MassForm
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.MassSource
import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.CanonicalAction

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteMassChangedRead
open Set Filter MeasureTheory UnitAddTorus
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
open NativeWholeH1Mixed (modes)
open NativeWindowAbsoluteTimeSource (H history rate)
open NativeWindowAbsoluteTimeFourier (Fiber Space row field realize)
open NativeWindowAbsoluteTimeGradient (spatial)
open NativeWindowGreenProduct (ComplexSpace)
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

def rowMass (M : ℕ) (v : H) : ℝ := ∑ i : Coordinate,∑ k∈modes M,‖row k i v‖^2
def rowGradient (M : ℕ) (v : H) : ℝ := ∑ i : Coordinate,∑ k∈modes M,integerWaveNormSq k*‖row k i v‖^2
def dirichlet (M : ℕ) (v : H) : ℝ := ∑ j : Coordinate,∑ i : Coordinate,‖realize (modes M) i (spatial M j v)‖^2

theorem row_mass_le (M : ℕ) (v : H) : rowMass M v≤‖v‖^2 := by
  simpa only [rowMass,NativeWindowAbsoluteTimeFourier.physical_square] using
    NativeWindowAbsoluteTimeFourier.physical_mass (modes M) v

theorem gradient_nonnegative (M : ℕ) (v : H) : 0≤rowGradient M v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun k _ => mul_nonneg (integerWaveNormSq_nonneg k) (sq_nonneg _)

theorem dirichlet_original (M : ℕ) (v : H) : dirichlet M v=(2*Real.pi)^2*rowGradient M v := by
  change (∑ j : Coordinate,∑ i : Coordinate,‖NativeWindowAbsoluteTimeFourier.physical (modes M) i (spatial M j v)‖^2)=_
  simp only [NativeWindowAbsoluteTimeFourier.physical_square]
  rw [Finset.sum_comm]
  simp only [rowGradient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k inside
  simp only [NativeWindowAbsoluteTimeFourier.row_spatial M _ k inside,norm_smul,mul_pow,
    NativePhysicalGradient.multiplier_norm_sq,← Finset.sum_mul,← Finset.mul_sum,integerWaveNormSq]
  ring

theorem dirichlet_le (M : ℕ) (v : H) : dirichlet M v≤∑ j : Coordinate,‖spatial M j v‖^2 :=
  Finset.sum_le_sum fun j _ => NativeWindowAbsoluteTimeFourier.physical_mass (modes M) (spatial M j v)

theorem canonical_pair (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) (x : Torus) :
    (∑ spin : Fin 4,∑ color : Fin 2,inner ℂ
      (NativeWindowAbsoluteTimePhysicalMatter.spatial seed M time j spin color x)
      (NativeWindowAbsoluteTimePhysicalMatter.temporal seed M time spin color x))=
        (1/8:ℂ)*(∑ i : Coordinate,inner ℂ (field (modes M) i (spatial M j (history seed time)) x)
          (field (modes M) i (rate seed time) x)) := by
  have actual:=NativeWindowAbsoluteTimeCanonicalEnergy.program_pairing (0 : Fiber)
    (NativeWindowAbsoluteTimePhysicalMatter.backgroundRate time)
    (fun i => field (modes M) i (spatial M j (history seed time)) x)
    (fun i => field (modes M) i (rate seed time) x)
  have first : (fun spin color => NativeWindowAbsoluteTimePhysicalMatter.spatial seed M time j spin color x)=
      NativeWindowAbsoluteTimeCanonicalEnergy.program (0 : Fiber)
        (fun i => field (modes M) i (spatial M j (history seed time)) x) := by
    funext spin color
    fin_cases spin <;> fin_cases color <;>
      simp [NativeWindowAbsoluteTimePhysicalMatter.spatial,NativeWindowAbsoluteTimeCanonicalEnergy.program,
        NativeRecoveryTimeCanonical.matterProgram,NativeRecoveryTimeCanonicalWrite.matterMatrix,Fin.sum_univ_three] <;> module
  have last : (fun spin color => NativeWindowAbsoluteTimePhysicalMatter.temporal seed M time spin color x)=
      NativeWindowAbsoluteTimeCanonicalEnergy.program (NativeWindowAbsoluteTimePhysicalMatter.backgroundRate time)
        (fun i => field (modes M) i (rate seed time) x) := by
    funext spin color
    fin_cases spin <;> fin_cases color <;>
      simp [NativeWindowAbsoluteTimePhysicalMatter.temporal,NativeWindowAbsoluteTimePhysicalMatter.baseWeight,
        NativeWindowAbsoluteTimeCanonicalEnergy.program,NativeRecoveryTimeCanonical.matterProgram,
        NativeRecoveryTimeCanonicalWrite.matterMatrix,Fin.sum_univ_three] <;> module
  simp only [funext_iff] at first last
  simp_rw [first,last]
  simpa only [inner_zero_left,mul_zero,zero_add] using actual


def work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) (f : Torus → ℂ) : ℂ :=
  ∫ x : Torus,f x*(∑ spin : Fin 4,∑ color : Fin 2,inner ℂ
    (NativeWindowAbsoluteTimePhysicalMatter.spatial seed M time j spin color x)
    (NativeWindowAbsoluteTimePhysicalMatter.temporal seed M time spin color x))

theorem work_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate)
    (f : Torus → ℂ) (regular : Integrable f) :
    work seed M time j f=(1/8:ℂ)*∑ i : Coordinate,∫ x : Torus,f x*
      inner ℂ (field (modes M) i (spatial M j (history seed time)) x) (field (modes M) i (rate seed time) x) := by
  have paid (i : Coordinate) : Integrable (fun x : Torus => f x*
      inner ℂ (field (modes M) i (spatial M j (history seed time)) x) (field (modes M) i (rate seed time) x)) := by
    let b : C(Torus,ℂ) := ⟨_,(field (modes M) i (spatial M j (history seed time))).continuous.inner
      (field (modes M) i (rate seed time)).continuous⟩
    exact regular.mul_bdd b.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun x => b.norm_coe_le_norm x)
  simp only [work,canonical_pair,← mul_assoc]
  simp_rw [show ∀ x : Torus,f x*(1/8:ℂ)*(∑ i : Coordinate,inner ℂ
    (field (modes M) i (spatial M j (history seed time)) x) (field (modes M) i (rate seed time) x))=
      (1/8:ℂ)*(∑ i : Coordinate,f x*inner ℂ
        (field (modes M) i (spatial M j (history seed time)) x) (field (modes M) i (rate seed time) x)) by
          intro x; rw [← Finset.mul_sum]; ring]
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => paid i)]

theorem field_mixed_bound (M : ℕ) (u v : H) (f : Torus → ℂ) (regular : Integrable f)
    (c : ComplexSpace) (read : ∀ k,c k=mFourierCoeff f k) (B : ℝ) (bound : ‖c‖≤B)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ‖∑ i : Coordinate,∫ x : Torus,f x*inner ℂ (field (modes M) i u x) (field (modes M) i v x)‖≤
      epsilon*(rowGradient M u+rowGradient M v)+NativeWindowAbsoluteMassForm.cap B epsilon*(rowMass M u+rowMass M v) := by
  apply (norm_sum_le _ _).trans
  have paid (i : Coordinate):=NativeWindowAbsoluteMassForm.mixed_absorption f regular c read (modes M)
    (fun k => row k i u) (fun k => row k i v) B bound epsilon positive
  have summed:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) (fun i _ => paid i)
  simpa only [mul_add,Finset.sum_add_distrib,← Finset.mul_sum,rowGradient,rowMass,field] using! summed

theorem scaled_norm (z : ℂ) : ‖(1/8:ℂ)*z‖=(1/8:ℝ)*‖z‖ := by
  rw [norm_mul]
  congr 1
  norm_num

theorem mixed_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate)
    (f : Torus → ℂ) (regular : Integrable f) (c : ComplexSpace) (read : ∀ k,c k=mFourierCoeff f k)
    (B : ℝ) (bound : ‖c‖≤B) (epsilon : ℝ) (positive : 0<epsilon) :
    ‖work seed M time j f‖≤(1/8:ℝ)*(epsilon*(rowGradient M (spatial M j (history seed time))+rowGradient M (rate seed time))+
      NativeWindowAbsoluteMassForm.cap B epsilon*(rowMass M (spatial M j (history seed time))+rowMass M (rate seed time))) := by
  have paid:=field_mixed_bound M (spatial M j (history seed time)) (rate seed time) f regular c read B bound epsilon positive
  have scaled:=mul_le_mul_of_nonneg_left paid (by norm_num : (0:ℝ)≤1/8)
  rw [work_original seed M time j f regular,scaled_norm]
  exact scaled

def secondCost (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) : ℝ :=
  dirichlet M (spatial M j (history seed time))

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (horizon B epsilon : ℝ) (positive : 0<epsilon) :
    ∃ C : ℝ,0≤C ∧∀ M,∀ time∈Icc 0 horizon,∀ j,∀ f : Torus → ℂ,∀ _regular : Integrable f,
      ∀ c : ComplexSpace,∀ _read : ∀ k,c k=mFourierCoeff f k,∀ _bound : ‖c‖≤B,
        ‖work seed M time j f‖≤epsilon*secondCost seed M time j+C := by
  obtain ⟨L,L0,first⟩:=NativeWindowAbsoluteTimeEnergy.source_first_jet_bound seed horizon
  let R:=NativeWindowAbsoluteTimeSource.rateBudget seed
  let delta:=8*epsilon*(2*Real.pi)^2
  have delta0:0<delta:=by dsimp only [delta]; positivity
  let K:=NativeWindowAbsoluteMassForm.cap B delta
  have K0:0≤K:=by dsimp only [K,NativeWindowAbsoluteMassForm.cap]; positivity
  refine ⟨3*epsilon*L+(1/8:ℝ)*K*(L+R^2),by positivity,fun M time inside j f regular c read bound => ?_⟩
  have massU:rowMass M (spatial M j (history seed time))≤L := by
    apply (row_mass_le _ _).trans
    have paid:=first M j.succ time inside
    change ‖spatial M j (history seed time)‖^2+‖spatial M j (rate seed time)‖^2≤L at paid
    linarith [sq_nonneg ‖spatial M j (rate seed time)‖]
  have massV:rowMass M (rate seed time)≤R^2 := (row_mass_le _ _).trans
    (pow_le_pow_left₀ (norm_nonneg _) (NativeWindowAbsoluteTimeSource.source_rate_bound seed time) 2)
  have gradientV:(2*Real.pi)^2*rowGradient M (rate seed time)≤3*L := by
    rw [← dirichlet_original]
    apply (dirichlet_le _ _).trans
    have each (d : Coordinate):‖spatial M d (rate seed time)‖^2≤L := by
      have paid:=first M d.succ time inside
      change ‖spatial M d (history seed time)‖^2+‖spatial M d (rate seed time)‖^2≤L at paid
      linarith [sq_nonneg ‖spatial M d (history seed time)‖]
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) (fun d _ => each d)
  have paid:=mixed_bound seed M time j f regular c read B bound delta delta0
  have lower:=mul_le_mul_of_nonneg_left (add_le_add massU massV) K0
  have gradient:=mul_le_mul_of_nonneg_left gradientV positive.le
  dsimp only [secondCost] at *
  rw [dirichlet_original]
  dsimp only [delta] at paid
  change _≤(1/8:ℝ)*(8*epsilon*(2*Real.pi)^2*(_+_)+K*(_+_)) at paid
  nlinarith only [paid,lower,gradient]

theorem source_scalar_bound (seed : GeneratedWholeRestartCurrent nu) (horizon B epsilon : ℝ) (positive : 0<epsilon) :
    ∃ C : ℝ,0≤C ∧∀ M,∀ time∈Icc 0 horizon,∀ j,∀ f : Lp ℂ 2 (volume : Measure Torus),
      ‖f‖≤B → ‖work seed M time j f‖≤epsilon*secondCost seed M time j+C := by
  obtain ⟨C,C0,paid⟩:=source_bound seed horizon B epsilon positive
  refine ⟨C,C0,fun M time inside j f bound => ?_⟩
  exact paid M time inside j f ((Lp.memLp f).integrable (by norm_num : (1:ℝ≥0∞)≤2))
    (NativeWindowAbsoluteMassForm.coefficients f) (NativeWindowAbsoluteMassForm.coefficients_read f)
    ((NativeWindowAbsoluteMassForm.coefficients_norm f).trans_le bound)

theorem work_congr_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate)
    {f g : Torus → ℂ} (same : f=ᵐ[volume] g) : work seed M time j f=work seed M time j g := by
  apply integral_congr_ae
  filter_upwards [same] with x actual
  rw [actual]

theorem physical_spatial_derivative (M : ℕ) (i j : Coordinate) (v : H) :
    HasDerivAt (fun z => NativeWindowAbsoluteTimeCanonicalAction.shift j z (realize (modes M) i v))
      (realize (modes M) i (spatial M j v)) 0 := by
  have actual:=((ContinuousMap.toLp 2 (volume : Measure Torus) ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (E := Space) (F := C(Torus,Fiber)) 0
    (NativeWindowAbsoluteTimeFourier.polynomial_spatial_strong (modes M) (fun k => row k i v) j)
  have derivative : NativeWindowAbsoluteTimeFourier.polynomial (modes M)
      (fun k => NativePhysicalGradient.multiplier k j • row k i v)=field (modes M) i (spatial M j v) :=
    ContinuousMap.ext fun x => (NativeWindowAbsoluteTimeFourier.field_spatial M i j v x).symm
  rw [derivative] at actual
  change HasDerivAt (fun z => NativeWindowAbsoluteTimeCanonicalAction.shift j z
    ((ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) (field (modes M) i v)))
      ((ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) (field (modes M) i (spatial M j v))) 0
  simpa only [NativeWindowAbsoluteTimeCanonicalAction.shift_field,field,
    NativeWindowAbsoluteTimeFourier.translatedPolynomial] using! actual

private theorem program_map (L : Space →L[ℂ] Space) (b : Space) (u : Coordinate → Space) (spin : Fin 4) (color : Fin 2) :
    L (NativeWindowAbsoluteTimeCanonicalEnergy.program b u spin color)=
      NativeWindowAbsoluteTimeCanonicalEnergy.program (L b) (fun i => L (u i)) spin color := by
  fin_cases spin <;> fin_cases color <;>
    simp [NativeWindowAbsoluteTimeCanonicalEnergy.program,NativeRecoveryTimeCanonical.matterProgram]

def secondValue (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j d : Coordinate) : Fin 4 → Fin 2 → Space :=
  NativeWindowAbsoluteTimeCanonicalEnergy.program 0
    (fun i => realize (modes M) i (spatial M d (spatial M j (history seed time))))

theorem second_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j d : Coordinate)
    (spin : Fin 4) (color : Fin 2) :
    HasDerivAt (fun z => NativeWindowAbsoluteTimeCanonicalAction.shift d z
      (NativeWindowAbsoluteTimePhysicalMatter.spaceCoefficient seed M time j spin color))
        (secondValue seed M time j d spin color) 0 := by
  have whole:=NativeWindowAbsoluteTimeCanonicalEnergy.program_hasDerivAt (hasDerivAt_const (0:ℝ) (0:Space))
    (fun i => physical_spatial_derivative M i d (spatial M j (history seed time)))
  have one:=hasDerivAt_pi.mp (hasDerivAt_pi.mp whole spin) color
  have original:=congrFun (congrFun (NativeWindowAbsoluteTimeCanonicalEnergy.value_program seed M time j.succ) spin) color
  change NativeWindowAbsoluteTimePhysicalMatter.spaceCoefficient seed M time j spin color=
    NativeWindowAbsoluteTimeCanonicalEnergy.program 0
      (fun i => realize (modes M) i (spatial M j (history seed time))) spin color at original
  apply one.congr_of_eventuallyEq
  filter_upwards with z
  have actual:=program_map (NativeWindowAbsoluteTimeCanonicalAction.shift d z).toContinuousLinearMap 0
    (fun i => realize (modes M) i (spatial M j (history seed time))) spin color
  have same:=congrArg (fun a : Space => NativeWindowAbsoluteTimeCanonicalAction.shift d z a) original
  exact same.trans (by simpa only [map_zero] using! actual)

def canonicalSecondCost (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) : ℝ :=
  ∑ d : Coordinate,∑ spin : Fin 4,∑ color : Fin 2,‖secondValue seed M time j d spin color‖^2

theorem canonical_second_cost (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) :
    canonicalSecondCost seed M time j=(1/8:ℝ)*secondCost seed M time j := by
  simp only [canonicalSecondCost,secondValue,NativeWindowAbsoluteTimeCanonicalEnergy.program_mass,
    norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_add,← Finset.mul_sum,secondCost,dirichlet]

theorem source_canonical_bound (seed : GeneratedWholeRestartCurrent nu) (horizon B epsilon : ℝ) (positive : 0<epsilon) :
    ∃ C : ℝ,0≤C ∧∀ M,∀ time∈Icc 0 horizon,∀ j,∀ f : Lp ℂ 2 (volume : Measure Torus),
      ‖f‖≤B → ‖work seed M time j f‖≤epsilon*canonicalSecondCost seed M time j+C := by
  obtain ⟨C,C0,paid⟩:=source_scalar_bound seed horizon B (epsilon/8) (by positivity)
  refine ⟨C,C0,fun M time inside j f bound => ?_⟩
  rw [canonical_second_cost]
  convert paid M time inside j f bound using 1
  ring

theorem clock_inner (advance : ℝ) (u v : Fiber) :
    inner ℂ (NativeWindowAbsoluteTimeIsometry.clock ℂ advance u) (NativeWindowAbsoluteTimeIsometry.clock ℂ advance v)=inner ℂ u v := by
  let clock : Fiber →ₗᵢ[ℂ] Fiber := Lp.compMeasurePreservingₗᵢ ℂ (fun s : ℝ => s-advance)
    (by simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-advance))
  exact clock.inner_map_map u v

theorem row_clock (advance : ℝ) (k : IntegerWavevector) (i : Coordinate) (v : H) :
    row k i (NativeWindowAbsoluteTimeIsometry.clock NativeWholeResolvent.wholePhysical advance v)=
      NativeWindowAbsoluteTimeIsometry.clock ℂ advance (row k i v) := by
  have preserves : MeasurePreserving (fun s : ℝ => s-advance) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-advance)
  have shifted:=preserves.quasiMeasurePreserving.ae ((NativeWindowAbsoluteTimeFourier.rowMap k i).coeFn_compLpL v)
  apply Lp.ext
  filter_upwards [(NativeWindowAbsoluteTimeFourier.rowMap k i).coeFn_compLpL
      (NativeWindowAbsoluteTimeIsometry.clock NativeWholeResolvent.wholePhysical advance v),
    NativeWindowAbsoluteTimeIsometry.clock_ae NativeWholeResolvent.wholePhysical advance v,
    NativeWindowAbsoluteTimeIsometry.clock_ae ℂ advance (row k i v),shifted] with s first middle last actual
  change row k i (NativeWindowAbsoluteTimeIsometry.clock NativeWholeResolvent.wholePhysical advance v) s=_ at first
  change row k i v (s-advance)=_ at actual
  rw [first,middle,last,actual]

theorem gradient_clock (M : ℕ) (advance : ℝ) (v : H) :
    rowGradient M (NativeWindowAbsoluteTimeIsometry.clock NativeWholeResolvent.wholePhysical advance v)=rowGradient M v := by
  simp only [rowGradient,row_clock,LinearIsometry.norm_map]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem work_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (j : Coordinate) (f : Torus → ℂ) :
    work seed M (step.2.clockAdvance+time) j f=work step.1 M time j f := by
  apply integral_congr_ae
  filter_upwards with x
  rw [canonical_pair,canonical_pair]
  congr 2
  apply Finset.sum_congr rfl
  intro i _

  have first:=congrArg (fun v : H => field (modes M) i v x)
    (NativeWindowAbsoluteTimeEnergy.value_next seed M step generated time nonnegative j.succ)
  change field (modes M) i (spatial M j (history seed (step.2.clockAdvance+time))) x=_ at first
  rw [NativeWindowAbsoluteTimeFourier.field_clock] at first
  simp only [NativeWindowAbsoluteTimeEnergy.value,NativeWindowAbsoluteTimeEnergy.word,Fin.cases_succ] at first
  have last:=NativeWindowAbsoluteTimeFourier.rate_next seed step generated time nonnegative (modes M) i x
  exact (congrArg₂ (fun u v : Fiber => inner ℂ u v) first last).trans (clock_inner _ _ _)

theorem second_cost_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (j : Coordinate) : canonicalSecondCost seed M (step.2.clockAdvance+time) j=canonicalSecondCost step.1 M time j := by
  have source:=congrArg (rowGradient M) (NativeWindowAbsoluteTimeEnergy.value_next seed M step generated time nonnegative j.succ)
  rw [gradient_clock] at source
  simp only [NativeWindowAbsoluteTimeEnergy.value,NativeWindowAbsoluteTimeEnergy.word,Fin.cases_succ] at source
  simpa only [canonical_second_cost,secondCost,dirichlet_original] using
    congrArg (fun a : ℝ => (1/8:ℝ)*((2*Real.pi)^2*a)) source

def complexJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    Lp ℂ 2 (volume : Measure Torus) := Complex.ofRealCLM.compLpL 2 volume (NativeWindowMassSource.jet seed time valid j)

theorem complex_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    complexJet seed time valid j=ᵐ[volume] fun x => (NativeWindowMassSource.pointJet seed time valid j x : ℂ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (NativeWindowMassSource.jet seed time valid j),
    NativeWindowMassSource.jet_ae seed time valid j] with x lifted actual
  change complexJet seed time valid j x=_ at lifted
  rw [lifted,actual]
  rfl

theorem complex_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (valid : -1<time) (before : time≤horizon) (j : Coordinate) :
    ‖complexJet seed time valid j‖≤NativeWindowMeanSpatialJet.budget seed horizon/8 := by
  have bound : ‖complexJet seed time valid j‖≤‖NativeWindowMassSource.jet seed time valid j‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL (NativeWindowMassSource.jet seed time valid j)] with x lifted
    change complexJet seed time valid j x=_ at lifted
    rw [lifted]
    simp only [Complex.ofRealCLM_apply,Complex.norm_real,le_refl]
  exact bound.trans (NativeWindowMassSource.jet_bound seed time horizon valid before j)

def massWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) (j : Coordinate) : ℂ :=
  work seed M time j (complexJet seed time valid j)

theorem mass_work_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) (j : Coordinate) :
    massWork seed M time valid j=∫ x : Torus,(NativeWindowMassSource.pointJet seed time valid j x : ℂ)*
      (∑ spin : Fin 4,∑ color : Fin 2,inner ℂ
        (NativeWindowAbsoluteTimePhysicalMatter.spatial seed M time j spin color x)
        (NativeWindowAbsoluteTimeCanonicalAction.net seed M time valid.le x spin color)) := by
  have actual:=work_congr_ae seed M time j (complex_ae seed time valid j)
  change massWork seed M time valid j=_ at actual
  exact actual.trans (by
    apply integral_congr_ae
    filter_upwards with x
    simp only [NativeWindowAbsoluteTimeCanonicalAction.net_original])

theorem source_changed_read (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃ C : ℝ,0≤C ∧∀ M,∀ time : Icc (0:ℝ) horizon,∀ j,
      HasDerivAt (fun z => NativeWindowMassSource.translate j z (NativeWindowMassSource.field seed time))
        (NativeWindowMassSource.weakJet seed time (by linarith [time.property.1]) j) 0 ∧
      ‖massWork seed M time (by linarith [time.property.1]) j‖≤epsilon*canonicalSecondCost seed M time j+C := by
  obtain ⟨C,C0,paid⟩:=source_canonical_bound seed horizon (NativeWindowMeanSpatialJet.budget seed horizon/8) epsilon positive
  refine ⟨C,C0,fun M time j => ⟨NativeWindowMassSource.hasDerivAt seed time (by linarith [time.property.1]) j,?_⟩⟩
  exact paid M time time.property j (complexJet seed time (by linarith [time.property.1]) j)
    (complex_bound seed time horizon (by linarith [time.property.1]) time.property.2 j)

theorem mass_work_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (j : Coordinate) :
    massWork seed M (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) j=
      massWork step.1 M time (by linarith) j := by
  have scalar:=congrArg (Complex.ofRealCLM.compLpL 2 (volume : Measure Torus))
    (NativeWindowMassSource.jet_next seed step generated time nonnegative j)
  exact (congrArg (fun f : Lp ℂ 2 (volume : Measure Torus) => work seed M (step.2.clockAdvance+time) j f) scalar).trans
    (work_next seed M step generated time nonnegative j _)


end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteMassChangedRead
