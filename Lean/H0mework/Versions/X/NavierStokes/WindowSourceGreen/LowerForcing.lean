import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerSource
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerReadback
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerPhysicalBudget

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMotherForcingSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
open NativeWindowAbsoluteTimeFourier (Fiber Space field realize)
open NativeWindowAbsoluteTimeSource (H history rate)
open NativeWindowAbsoluteTimePhysicalMatter (matter temporal spatial backgroundRate firstJet)
open NativeWindowAbsoluteTimeCanonicalEnergy (program)
open NativeWindowGreenTestForm (SpinFiber)
open NativeWindowAbsoluteLowerBound (Full)
open PhysicsCore DiracExteriorMatterAction StageNineHolonomicField DiracCliffordRepresentation
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance fiberSeminormed : SeminormedAddCommGroup Fiber := (inferInstance : NormedAddCommGroup Fiber).toSeminormedAddCommGroup
local instance spaceSeminormed : SeminormedAddCommGroup Space := (inferInstance : NormedAddCommGroup Space).toSeminormedAddCommGroup
variable {nu : Viscosity}

def jet (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (d : Fin 4) : C(Torus,SpinFiber Fiber) where
  toFun x := WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => firstJet seed M time x d entry.1 entry.2)
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro entry
    exact Fin.cases (temporal seed M time entry.1 entry.2).continuous
      (fun j => (spatial seed M time j entry.1 entry.2).continuous) d

private theorem toLp_square (f : C(Torus,Fiber)) :
    ‖(ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) f‖^2=∫ x : Torus,‖f x‖^2 := by
  rw [NativeWindowHilbertHalfProduct.lp_square]
  exact integral_congr_ae ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure Torus) f).fun_comp (fun v => ‖v‖^2))

theorem jet_mass (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (d : Fin 4) :
    (∫ x : Torus,‖jet seed M time d x‖^2)=
      Fin.cases (∑ spin : Fin 4,∑ color : Fin 2,‖NativeWindowAbsoluteTimePhysicalMatter.timeCoefficient seed M time spin color‖^2)
        (fun j => ∑ spin : Fin 4,∑ color : Fin 2,‖NativeWindowAbsoluteTimePhysicalMatter.spaceCoefficient seed M time j spin color‖^2) d := by
  have regular (entry : Fin 4 × Fin 2) : Integrable
      (fun x : Torus => ‖firstJet seed M time x d entry.1 entry.2‖^2) := by
    have continuous:Continuous (fun x : Torus => firstJet seed M time x d entry.1 entry.2) :=
      Fin.cases (temporal seed M time entry.1 entry.2).continuous
        (fun j => (spatial seed M time j entry.1 entry.2).continuous) d
    exact (ContinuousMap.memLp volume ℂ ⟨_,continuous⟩ : MemLp _ 2 _).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  simp only [jet,ContinuousMap.coe_mk,PiLp.norm_sq_eq_of_L2]
  rw [integral_finsetSum _ (fun entry _ => regular entry),Fintype.sum_prod_type]
  refine Fin.cases ?_ (fun j => ?_) d
  · simp only [firstJet,Fin.cases_zero,NativeWindowAbsoluteTimePhysicalMatter.timeCoefficient,toLp_square]
  · simp only [firstJet,Fin.cases_succ,NativeWindowAbsoluteTimePhysicalMatter.spaceCoefficient,toLp_square]

def backgroundBudget : ℝ := ‖NativeWindowAbsoluteTimePhysicalMatter.baseRead‖*
  (‖(NativeWindowKernelHalfDensity.derivative_memLp 2).toLp (deriv NativeWindowKernelHalfDensity.rootKernel)‖*
    ‖(memLp_top_const (lp.single 2 (0 : IntegerWavevector) (1 : ℂ) : NativePhysicalFourier.ScalarSequence)
      (μ := (volume : Measure ℝ))).toLp (fun _ : ℝ => (lp.single 2 (0 : IntegerWavevector) (1 : ℂ) : NativePhysicalFourier.ScalarSequence))‖)

theorem background_bound (time : ℝ) : ‖backgroundRate time‖ ≤ backgroundBudget := by
  apply (NativeWindowAbsoluteTimePhysicalMatter.baseRead.le_opNorm (NativeWindowAbsoluteTimeGNS.backgroundRate 0 time)).trans
  exact mul_le_mul_of_nonneg_left (NativeWindowAbsoluteTimeCarrier.field_norm_bound
    (deriv NativeWindowKernelHalfDensity.rootKernel) (NativeWindowKernelHalfDensity.derivative_memLp 2)
    (fun _ => (lp.single 2 (0 : IntegerWavevector) (1 : ℂ) : NativePhysicalFourier.ScalarSequence))
    (memLp_top_const _) time) (norm_nonneg NativeWindowAbsoluteTimePhysicalMatter.baseRead)

theorem temporal_program (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    (fun spin color => NativeWindowAbsoluteTimePhysicalMatter.timeCoefficient seed M time spin color)=
      program (NativeWindowAbsoluteTimeCanonicalEnergy.baseRate time)
        (fun i => realize (NativeWholeH1Mixed.modes M) i (rate seed time)) := by
  funext spin color
  fin_cases spin <;> fin_cases color <;>
    simp [NativeWindowAbsoluteTimePhysicalMatter.timeCoefficient,temporal,NativeWindowAbsoluteTimePhysicalMatter.baseWeight,
      program,NativeRecoveryTimeCanonical.matterProgram,NativeRecoveryTimeCanonicalWrite.matterMatrix,Fin.sum_univ_three,
      NativeWindowAbsoluteTimeCanonicalEnergy.baseRate,realize,NativeWindowAbsoluteTimeFourier.physical] <;> module

theorem temporal_mass (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    (∑ spin : Fin 4,∑ color : Fin 2,‖NativeWindowAbsoluteTimePhysicalMatter.timeCoefficient seed M time spin color‖^2)=
      2*‖NativeWindowAbsoluteTimeCanonicalEnergy.baseRate time‖^2+
        (1/8:ℝ)*(∑ i : Coordinate,‖realize (NativeWholeH1Mixed.modes M) i (rate seed time)‖^2) := by
  have actual:=temporal_program seed M time
  simp only [funext_iff] at actual
  simp_rw [actual]
  exact NativeWindowAbsoluteTimeCanonicalEnergy.program_mass _ _

theorem spatial_mass_le_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) :
    (∑ spin : Fin 4,∑ color : Fin 2,‖NativeWindowAbsoluteTimePhysicalMatter.spaceCoefficient seed M time j spin color‖^2) ≤
      NativeWindowAbsoluteTimeCanonicalEnergy.energy seed M time := by
  let f:Fin 4 → ℝ:=fun word => ∑ spin : Fin 4,∑ color : Fin 2,‖NativeWindowAbsoluteTimeCanonicalEnergy.value seed M time word spin color‖^2
  have positive:∀ word∈(Finset.univ : Finset (Fin 4)),0 ≤ f word := by
    intro word _
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have paid:=Finset.single_le_sum positive (Finset.mem_univ j.succ)
  simpa only [f,NativeWindowAbsoluteTimeCanonicalEnergy.value,Fin.cases_succ,
    NativeWindowAbsoluteTimeCanonicalEnergy.energy] using! paid

theorem source_jet_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ time∈Icc 0 horizon,∀ d : Fin 4,
      (∫ x : Torus,‖jet seed M time d x‖^2) ≤ C := by
  obtain ⟨L,L0,paid⟩:=NativeWindowAbsoluteTimeCanonicalEnergy.source_energy_power_bound seed horizon
  let R:=NativeWindowAbsoluteTimeSource.rateBudget seed
  refine ⟨L+2*backgroundBudget^2+R^2/8,by positivity,fun M time inside d => ?_⟩
  rw [jet_mass]
  refine Fin.cases ?_ (fun j => ?_) d
  · simp only [Fin.cases_zero]
    rw [temporal_mass]
    have background:‖NativeWindowAbsoluteTimeCanonicalEnergy.baseRate time‖^2 ≤ backgroundBudget^2 := by
      rw [NativeWindowAbsoluteTimeCanonicalEnergy.baseRate_constant]
      change ‖Lp.const 2 (volume : Measure Torus) (backgroundRate time)‖^2 ≤ _
      rw [Lp.norm_const 2 (volume : Measure Torus) (backgroundRate time) (by norm_num)]
      simpa using pow_le_pow_left₀ (norm_nonneg _) (background_bound time) 2
    have rateBound:‖rate seed time‖^2 ≤ R^2 :=
      pow_le_pow_left₀ (norm_nonneg (rate seed time)) (NativeWindowAbsoluteTimeSource.source_rate_bound seed time) 2
    have original: (∑ i : Coordinate,‖realize (NativeWholeH1Mixed.modes M) i (rate seed time)‖^2) ≤ R^2 :=
      (NativeWindowAbsoluteTimeFourier.physical_mass (NativeWholeH1Mixed.modes M) (rate seed time)).trans rateBound
    nlinarith only [background,original,L0]
  · have component:=spatial_mass_le_energy seed M time j
    exact (component.trans (paid M time inside).1).trans (by nlinarith only [sq_nonneg backgroundBudget,sq_nonneg R])

def matrix (d : Fin 4) : Module.End ℂ DiracExteriorMatterCarrier :=
  Fin.cases LinearMap.id (fun j => diracMatrixMatterAction (diracFrameEvolutionPrincipal j.succ)) d

def scalar (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (d : Fin 4) (x : Torus) : ℂ :=
  Fin.cases (NativeWindowMassReciprocal.value (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x) : ℂ) (fun _ => 1) d

theorem scalar_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (d : Fin 4) (x : Torus) :
    ‖scalar seed time d x‖ ≤ 1 := by
  refine Fin.cases ?_ (fun _ => le_of_eq norm_one) d
  change ‖(NativeWindowMassReciprocal.value (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x) : ℂ)‖ ≤ 1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (NativeWindowMassReciprocal.value_nonnegative _)]
  linarith [NativeWindowMassReciprocal.value_bound (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time x)]

theorem scalar_measurable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (d : Fin 4) :
    AEStronglyMeasurable (scalar seed time d) (volume : Measure Torus) := by
  refine Fin.cases ?_ (fun _ => aestronglyMeasurable_const) d
  have continuous:Continuous (fun v : PhysicalSpace => (NativeWindowMassReciprocal.value v : ℂ)) :=
    Complex.continuous_ofReal.comp NativeWindowMassReciprocal.value_continuous
  exact continuous.comp_aestronglyMeasurable (Lp.memLp (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time)).1

def principal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (d : Fin 4) (x : Torus) : Full Fiber :=
  scalar seed time d x • NativeWindowWeakLowerReadback.lift (E := Fiber) (matrix d) (jet seed M time d x)

theorem principal_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (d : Fin 4) (x : Torus) :
    ‖principal seed M time d x‖^2 ≤ NativeWindowAbsoluteLowerBound.matrixCost (matrix d)^2*‖jet seed M time d x‖^2 := by
  have bound:‖principal seed M time d x‖ ≤ NativeWindowAbsoluteLowerBound.matrixCost (matrix d)*‖jet seed M time d x‖ := by
    rw [principal,norm_smul,NativeWindowWeakLowerReadback.lift_original]
    apply (mul_le_mul_of_nonneg_right (scalar_bound seed time d x) (norm_nonneg _)).trans
    simpa only [one_mul] using NativeWindowAbsoluteLowerBound.lift_norm (matrix d) (jet seed M time d x)
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) bound 2

theorem principal_memLp (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (d : Fin 4) :
    MemLp (principal seed M time d) 2 (volume : Measure Torus) := by
  have measured:AEStronglyMeasurable (principal seed M time d) (volume : Measure Torus) :=
    (scalar_measurable seed time d).smul
      ((NativeWindowWeakLowerReadback.lift (E := Fiber) (matrix d)).continuous.comp (jet seed M time d).continuous).aestronglyMeasurable
  have lower:Integrable (fun x : Torus => ‖jet seed M time d x‖^2) :=
    (ContinuousMap.memLp volume ℂ (jet seed M time d) : MemLp _ 2 _).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have upper:=lower.const_mul (NativeWindowAbsoluteLowerBound.matrixCost (matrix d)^2)
  apply (memLp_two_iff_integrable_sq_norm measured).mpr
  exact upper.mono' (measured.norm.pow 2) (Eventually.of_forall fun x => by
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using principal_bound seed M time d x)

theorem principal_integral (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (d : Fin 4) :
    (∫ x : Torus,‖principal seed M time d x‖^2) ≤
      NativeWindowAbsoluteLowerBound.matrixCost (matrix d)^2*(∫ x : Torus,‖jet seed M time d x‖^2) := by
  have first:Integrable (fun x : Torus => ‖principal seed M time d x‖^2) :=
    (principal_memLp seed M time d).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have last:Integrable (fun x : Torus => ‖jet seed M time d x‖^2) :=
    (ContinuousMap.memLp volume ℂ (jet seed M time d) : MemLp _ 2 _).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  simpa only [integral_const_mul] using integral_mono_ae first
    (last.const_mul (NativeWindowAbsoluteLowerBound.matrixCost (matrix d)^2))
      (Eventually.of_forall (principal_bound seed M time d))

theorem source_principal_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ time∈Icc 0 horizon,∀ d : Fin 4,
      (∫ x : Torus,‖principal seed M time d x‖^2) ≤ C := by
  obtain ⟨L,L0,paid⟩:=source_jet_bound seed horizon
  let K:=∑ d : Fin 4,NativeWindowAbsoluteLowerBound.matrixCost (matrix d)^2
  have K0:0 ≤ K:=Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨K*L,mul_nonneg K0 L0,fun M time inside d => ?_⟩
  have component:NativeWindowAbsoluteLowerBound.matrixCost (matrix d)^2 ≤ K :=
    Finset.single_le_sum (fun a _ => sq_nonneg (NativeWindowAbsoluteLowerBound.matrixCost (matrix a))) (Finset.mem_univ d)
  apply (principal_integral seed M time d).trans
  exact (mul_le_mul_of_nonneg_left (paid M time inside d) (sq_nonneg _)).trans
    (mul_le_mul_of_nonneg_right component L0)

private theorem sum_square {G : Type*} [NormedAddCommGroup G] (v : Fin 4 → G) (w : G) :
    ‖(∑ d : Fin 4,v d)+w‖^2 ≤ 8*(∑ d : Fin 4,‖v d‖^2)+2*‖w‖^2 := by
  have normed:‖(∑ d : Fin 4,v d)+w‖ ≤ (∑ d : Fin 4,‖v d‖)+‖w‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)
  have first:=pow_le_pow_left₀ (norm_nonneg _) normed 2
  have cauchy:=Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4)) (fun _ => (1:ℝ)) (fun d => ‖v d‖)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at cauchy
  nlinarith only [first,cauchy,sq_nonneg ((∑ d : Fin 4,‖v d‖)-‖w‖)]

def forcing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) (x : Torus) : Full Fiber :=
  WithLp.toLp 2 (NativeWindowAbsoluteTimePhysicalMatter.sourceForcing seed M time valid.le x)

def lower (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) (x : Torus) : Full Fiber :=
  NativeWindowAbsoluteLowerBound.lift (NativeWindowMotherLowerProduct.point seed time valid x)
    (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => matter seed M time entry.1 entry.2 x))

theorem lower_memLp (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) :
    MemLp (lower seed M time valid) 2 (volume : Measure Torus) := by
  have paid:=NativeWindowMotherLowerProduct.source_product seed time time valid le_rfl
    (NativeWindowAbsoluteTimePhysicalMatter.support M) (NativeWindowAbsoluteTimePhysicalMatter.coefficientRow seed M time)
  simpa only [NativeWindowMotherPhysicalBudget.polynomial_original,lower] using! paid.1

theorem forcing_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) (x : Torus) :
    forcing seed M time valid x=(∑ d : Fin 4,principal seed M time d x)+
      NativeWindowAbsoluteLowerBound.lift (NativeWindowMotherLowerProduct.point seed time valid x)
        (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => matter seed M time entry.1 entry.2 x)) := by
  unfold forcing
  rw [NativeWindowAbsoluteTimePhysicalMatter.full_forcing_slot]
  rw [Fin.sum_univ_succ]
  simp only [principal,scalar,matrix,Fin.cases_zero,Fin.cases_succ,
    NativeWindowWeakLowerReadback.lift_original]
  apply PiLp.ext
  intro output
  simp only [NativeWindowAbsoluteTimePhysicalMatter.retainedSpatial,NativeWindowAbsoluteTimePhysicalMatter.extension,
    NativeWindowAbsoluteLowerBound.lift,PiLp.toLp_apply,PiLp.add_apply,PiLp.smul_apply,WithLp.ofLp_sum,Finset.sum_apply,
    Pi.add_apply,Pi.smul_apply,Fintype.sum_prod_type,jet,ContinuousMap.coe_mk,firstJet,Fin.cases_zero,Fin.cases_succ,
    NativeWindowMotherLowerProduct.point,NativeWindowMassReciprocal.value,Complex.ofReal_inv,one_smul]
  abel

theorem forcing_memLp (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) :
    MemLp (forcing seed M time valid) 2 (volume : Measure Torus) := by
  have regular:MemLp (fun x : Torus => (∑ d : Fin 4,principal seed M time d x)+lower seed M time valid x) 2 volume :=
    (memLp_finsetSum Finset.univ fun d _ => principal_memLp seed M time d).add (lower_memLp seed M time valid)
  exact MemLp.ae_eq (Eventually.of_forall fun x => (forcing_original seed M time valid x).symm) regular

theorem forcing_integral (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1<time) :
    (∫ x : Torus,‖forcing seed M time valid x‖^2) ≤
      8*(∑ d : Fin 4,∫ x : Torus,‖principal seed M time d x‖^2)+2*(∫ x : Torus,‖lower seed M time valid x‖^2) := by
  have regular (d : Fin 4):Integrable (fun x : Torus => ‖principal seed M time d x‖^2) :=
    (principal_memLp seed M time d).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have rest:Integrable (fun x : Torus => ‖lower seed M time valid x‖^2) :=
    (lower_memLp seed M time valid).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have force:Integrable (fun x : Torus => ‖forcing seed M time valid x‖^2) :=
    (forcing_memLp seed M time valid).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have upper:=((integrable_finsetSum Finset.univ fun d _ => regular d).const_mul 8).add (rest.const_mul 2)
  have bound:=integral_mono_ae force upper (Eventually.of_forall fun x => by
    dsimp only [Pi.add_apply]
    rw [forcing_original]
    exact sum_square (fun d => principal seed M time d x) (lower seed M time valid x))
  simpa only [Pi.add_apply,integral_add ((integrable_finsetSum Finset.univ fun d _ => regular d).const_mul 8) (rest.const_mul 2),
    integral_const_mul,integral_finsetSum _ (fun d _ => regular d)] using! bound

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧∀ M,∀ time : Icc (0:ℝ) horizon,
      MemLp (forcing seed M time (by linarith [time.property.1])) 2 (volume : Measure Torus) ∧
        (∫ x : Torus,‖forcing seed M time (by linarith [time.property.1]) x‖^2) ≤ C := by
  obtain ⟨P,P0,principalPaid⟩:=source_principal_bound seed horizon
  obtain ⟨B,B0,lowerPaid⟩:=NativeWindowMotherPhysicalBudget.source_lower_bound seed horizon
  refine ⟨32*P+2*B,by positivity,fun M time => ⟨forcing_memLp seed M time (by linarith [time.property.1]),?_⟩⟩
  let valid:-1<(time:ℝ):=by linarith [time.property.1]
  have principalSum:=Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun d _ => principalPaid M time time.property d)
  have lowerSum:(∫ x : Torus,‖lower seed M time valid x‖^2) ≤ B := by
    have original:=(lowerPaid M time time.property).2.1
    simpa only [NativeWindowMotherPhysicalBudget.polynomial_original,lower] using! original
  have paid:=forcing_integral seed M time valid
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at principalSum
  linarith only [paid,principalSum,lowerSum]

end
end SaturationMonoid.NavierStokes.NativeWindowMotherForcingSource
