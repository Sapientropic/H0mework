import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationIndependentDensityEvolution
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalRealReaction

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumOriginalDensity
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumActualFieldQuantization PreparationVacuumActionFieldLift
open PreparationVacuumGaugeSourceInjection PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets
open PreparationVacuumPhysicalFeedback PreparationVacuumRealReaction
open PreparationVacuumSourceFieldFamily StageNineHolonomicField PreparationVacuumNonlinearFieldCurve
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAlgebra ℝ Operator:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

def blockLinear (positive : Bool) : FullMatrix→ₗ[ℂ] FullMatrix where
  toFun M:=if positive then Matrix.fromBlocks (M.submatrix Sum.inl Sum.inl) 0 0 0
    else Matrix.fromBlocks 0 0 0 (M.submatrix Sum.inr Sum.inr)
  map_add' A B:=by
    cases positive <;> ext i j <;> cases i <;> cases j <;> simp
  map_smul' r A:=by
    cases positive <;> ext i j <;> cases i <;> cases j <;> simp

theorem rawAction_blocks (reader : Field289) (p : PhysicalMomentum) (s : ActionState) :
    blockLinear true (rawActionSymbol reader p s)+blockLinear false (rawActionSymbol reader p s)=
      rawActionSymbol reader p s :=by
  rw [rawActionSymbol,rawFourier_blocks]
  ext i j
  cases i <;> cases j <;> simp [blockLinear,Matrix.fromBlocks]

def halfFiber (positive : Bool) (reader : Field289) (p : PhysicalMomentum) (u : JointParameter) :
    FockFiber→L[ℂ] FockFiber:=
  quantizer (blockLinear positive (rawActionSymbol reader p (ambientState u)))

theorem halfFiber_original_density (positive : Bool) (reader : Field289) (p : PhysicalMomentum)
    (u : JointParameter) (v : FockFiber) :
    fiberCoordinates (halfFiber positive reader p u v)=
      (if positive then rawPairDensity
        (affineMatrix (fun i=>densityActionMatrix*densityVariation reader (ambientState u) i) p) 0
       else rawPairDensity 0
        (affineMatrix (fun i=>densityActionMatrix*densityVariation reader (ambientState u) i) (-p)))
        (fiberCoordinates v) :=by
  cases positive
  · simp only [Bool.false_eq_true,↓reduceIte]
    rw [rawPairDensity_quantize]
    have block : blockLinear false (rawActionSymbol reader p (ambientState u))=
        Matrix.fromBlocks 0 0 0
          ((affineMatrix (fun i=>densityActionMatrix*densityVariation reader (ambientState u) i) (-p)).map star):=by
      rw [rawActionSymbol,rawFourier_blocks]
      ext i j
      cases i <;> cases j <;> simp [blockLinear,Matrix.fromBlocks]
    rw [halfFiber,block]
    change fiberCoordinates (fiberCoordinates.symm (Fermion.quantize _ (fiberCoordinates v)))=_
    exact LinearEquiv.apply_symm_apply _ _
  · simp only [↓reduceIte]
    rw [rawPairDensity_quantize]
    have block : blockLinear true (rawActionSymbol reader p (ambientState u))=
        Matrix.fromBlocks
          (affineMatrix (fun i=>densityActionMatrix*densityVariation reader (ambientState u) i) p) 0 0 0:=by
      rw [rawActionSymbol,rawFourier_blocks]
      ext i j
      cases i <;> cases j <;> simp [blockLinear,Matrix.fromBlocks]
    rw [halfFiber,block]
    change fiberCoordinates (fiberCoordinates.symm (Fermion.quantize _ (fiberCoordinates v)))=_
    have mapZero : (0:FullQuantum.StateGreen.SourceMatrix).map star=0:=by ext i j;simp
    rw [mapZero]
    exact LinearEquiv.apply_symm_apply _ _

theorem halfFiber_source (reader : Field289) (p : PhysicalMomentum) (u : JointParameter) :
    halfFiber true reader p u+halfFiber false reader p u=rawFiber reader p u :=by
  apply ContinuousLinearMap.ext
  intro v
  apply fiberCoordinates.injective
  rw [add_apply,map_add,halfFiber_original_density,halfFiber_original_density,rawFiber_original_halves]
  simp only [Bool.false_eq_true,↓reduceIte,rawPairDensity,plusDensity,oppositeDensity,Matrix.zero_apply,star_zero,
    zero_smul,Finset.sum_const_zero,zero_sub,sub_zero,LinearMap.smul_apply,LinearMap.neg_apply,
    LinearMap.zero_apply,neg_zero,add_zero,zero_add,smul_sub,smul_neg,sub_eq_add_neg,smul_add]

theorem halfFiber_smooth (positive : Bool) (reader : Field289) (p : PhysicalMomentum) (u : JointParameter)
    (valid : ambientState u∈validStates) : ContDiffAt ℝ ∞ (halfFiber positive reader p) u :=
  (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp u
    (((blockLinear positive).toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp u
      ((rawActionSymbol_smooth reader p _ valid).comp u ambientState_smooth.contDiffAt))

def halfSample (positive : Bool) (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (u : JointParameter) : ℂ:=
  pairSample u.2 (a u.2) (halfFiber positive reader p u (b u.2))

theorem halfSample_zero (positive : Bool) (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) (z : SourceCoordinateSlice) (outside : z∉tsupport a) :
    halfSample positive reader p a b (h,z)=0 :=by
  simp only [halfSample,image_eq_zero_of_notMem_tsupport outside,pairSample_zero_left]

theorem halfSample_near_smooth (positive : Bool) (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) (z : SourceCoordinateSlice) (small : ‖h‖<ambientRadius a) :
    ContDiffAt ℝ ∞ (halfSample positive reader p a b) (h,z) :=by
  by_cases inside : z∈tsupport a
  · let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
    have coefficient:=R.contDiff.contDiffAt.comp (h,z)
      (halfFiber_smooth positive reader p (h,z) (ambientRadius_valid a h z small.le inside))
    exact pairSample_param Prod.snd _ _ (h,z) (a.tsupport_subset inside) contDiffAt_snd
      (a.contDiff.contDiffAt.comp (h,z) contDiffAt_snd)
      (coefficient.clm_apply (b.contDiff.contDiffAt.comp (h,z) contDiffAt_snd))
  · apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds ((isClosed_tsupport a).isOpen_compl.mem_nhds inside)] with u hu
    exact halfSample_zero positive reader p a b u.1 u.2 hu

def halfForm (positive : Bool) (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) : ℂ:=
  ∫z,halfSample positive reader p a b (h,z) ∂GaussHistoryHilbert.configurationMeasure

theorem halfForm_C2 (positive : Bool) (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    ContDiffAt ℝ 2 (halfForm positive reader p a b) 0 :=
  source_integral_C2 _ (tsupport a) a.hasCompactSupport (ambientRadius a) (ambientRadius_positive a)
    (halfSample_near_smooth positive reader p a b) (halfSample_zero positive reader p a b)

theorem halfForm_source (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (small : ‖h‖<ambientRadius a) :
    halfForm true reader p a b h+halfForm false reader p a b h=rawForm reader p a b h :=by
  have integrable (positive : Bool) : Integrable
      (fun z=>halfSample positive reader p a b (h,z)) GaussHistoryHilbert.configurationMeasure:=
    parameter_slice_integrable _ (tsupport a) a.hasCompactSupport h
      (halfSample_near_smooth positive reader p a b h · small) (halfSample_zero positive reader p a b)
  rw [halfForm,halfForm,←integral_add (integrable true) (integrable false)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change pairSample z (a z) (halfFiber true reader p (h,z) (b z))+
    pairSample z (a z) (halfFiber false reader p (h,z) (b z))=rawSample reader p a b (h,z)
  rw [←pairSample_add_right,←add_apply,halfFiber_source]
  rfl

def halfReader (positive : Bool) (reader : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (h : Field289) : Operator:=
  finiteRiesz F (fun i j=>halfForm positive reader p (frameTest F i) (frameTest F j) h)

theorem halfReader_C2 (positive : Bool) (reader : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) : ContDiffAt ℝ 2 (halfReader positive reader p F) 0 :=by
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (halfForm_C2 positive reader p (frameTest F i) (frameTest F j)).smul contDiffAt_const

private theorem finiteRiesz_add (F : GaussUnitaryHistory.Index)
    (a b : FrameIndex F→FrameIndex F→ℂ) :
    finiteRiesz F a+finiteRiesz F b=finiteRiesz F (fun i j=>a i j+b i j) :=by
  simp only [finiteRiesz,add_smul,Finset.sum_add_distrib]

theorem halfReader_source_near (reader : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    (fun h=>halfReader true reader p F h+halfReader false reader p F h)=ᶠ[𝓝 0]
      PreparationVacuumRawJointFeedback.rawReader reader p F :=by
  have each (i j : FrameIndex F) : ∀ᶠh : Field289 in 𝓝 0,
      halfForm true reader p (frameTest F i) (frameTest F j) h+
        halfForm false reader p (frameTest F i) (frameTest F j) h=
          rawForm reader p (frameTest F i) (frameTest F j) h:=by
    filter_upwards [Metric.ball_mem_nhds (0:Field289) (ambientRadius_positive (frameTest F i))] with h hh
    exact halfForm_source reader p _ _ h (by simpa only [Metric.mem_ball,dist_zero_right] using hh)
  have all:=Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (each i))
  filter_upwards [all] with h hh
  change finiteRiesz F (fun i j=>halfForm true reader p (frameTest F i) (frameTest F j) h)+
    finiteRiesz F (fun i j=>halfForm false reader p (frameTest F i) (frameTest F j) h)=
      finiteRiesz F (fun i j=>rawForm reader p (frameTest F i) (frameTest F j) h)
  rw [finiteRiesz_add]
  exact congrArg (finiteRiesz F) (funext (fun i=>funext (fun j=>hh i j)))

def halfDensityRead (positive : Bool) (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : ℂ:=
  preparedDual q h age (halfReader positive reader q.p q.F h (preparedPrimal q h age))

theorem halfDensityRead_source (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ) :
    (fun h=>halfDensityRead true q reader h age+halfDensityRead false q reader h age)=ᶠ[𝓝 0]
      (fun h=>densityRead q reader h age) :=by
  filter_upwards [halfReader_source_near reader q.p q.F] with h hh
  simp only [halfDensityRead,densityRead]
  rw [←map_add,←add_apply,hh]

/-- This generated density decomposition is consumed at the original source differential. -/
theorem sourceJacobian_density_halves (q : PhysicalResponsePoint) (age : ℝ) (force : Field289)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (i : Fin 289) :
    sourceJacobian q age force i=
      -deriv (fun r : ℝ=>halfDensityRead true q (fieldUnit i) (r • force) age+
        halfDensityRead false q (fieldUnit i) (r • force) age) 0 :=by
  have path : Tendsto (fun r : ℝ=>r • force) (𝓝 0) (𝓝 (0:Field289)):=by
    have smooth : Continuous (fun r : ℝ=>r • force):=continuous_id.smul continuous_const
    simpa only [zero_smul] using smooth.tendsto (0:ℝ)
  have same:=(halfDensityRead_source q (fieldUnit i) age).comp_tendsto path
  have sameDerivative : deriv (fun r : ℝ=>halfDensityRead true q (fieldUnit i) (r • force) age+
      halfDensityRead false q (fieldUnit i) (r • force) age) 0=
        deriv (fun r : ℝ=>densityRead q (fieldUnit i) (r • force) age) 0:=by
    simpa only [Function.comp_def] using same.deriv_eq
  rw [sameDerivative]
  rw [(densityRead_generated q (fieldUnit i) force age hz hw).deriv,sourceJacobian_actual q age force hz hw]
  change (sourceSlopeJet q force age i).value= -densitySlope q (fieldUnit i) force age
  rw [sourceSlopeJet_value,densitySlope_actual]
  rfl

end LowEnergy.PreparationVacuumOriginalDensity
