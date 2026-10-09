import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceSignedObserverCurrent

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalSignedCurrentPoleObserver
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalNormalizedFullField
open PreparationVacuumNativeFieldInjection PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumActualFieldQuantization PreparationVacuumOriginalGreenFeedback
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussNativeMatter GaussHistoryHilbert GaussQuantumMultiplier
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair FullQuantum.CoframeResponse FullQuantum.StateGreen
open PointwiseLorentzianCoframeJet PointwiseDiracSpinConnectionLift
open Filter Set
open scoped BigOperators Matrix Topology ContDiff Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalSourceHarmonicReturn
open PreparationVacuumPhysicalCharacteristic ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource FullQuantum FullSpace PreparationVacuumLowerClassical

open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumNativeSlowCoupling PreparationVacuumPhysicalFeedback
open PreparationPhysicalResponseChargeGrading PreparationVacuumLorentzFieldInjection
open PreparationVacuumPhysicalChargedFieldFactor PreparationPhysicalPoleChargeMatrix
open GaussFockLift GaussCoreHilbert PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalNativePhaseChargeInventory
open scoped InnerProductSpace

open PreparationPhysicalFirstPoleGaugeRemainder PreparationPhysicalMaterialChargeTorque
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalCoframeChargeSelection PreparationPhysicalCoframeChargeExchange
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice CanonicalGradedCharge GaussCoreDifferential GaussQuantumMultiplier
open GaussFockPair GaussLiveMomentum GaussNativePotential
open scoped ContDiff

open NativeHistoryGrade GaussUnitaryHistory CanonicalPhysicalSpatial CanonicalPhysicalWardCore
open PreparationVacuumGradedTransport PreparationVacuumUncutYukawa PreparationPhysicalActualLegNormalization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalPoleAmputation PreparationPhysicalChargedScatteringPoleReturn
open GaussFockWeights GaussDensityCore MeasureTheory PreparationVacuumFieldConstraintResponse PreparationVacuumYukawaTransport
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointResolvent actualC gradedTest

open PreparationPhysicalFirstGaugeMaterialDifference PreparationPhysicalActualUnitFourPointReturn
open PreparationPhysicalActualPolarizationResponse PreparationVacuumFullFieldRiesz

open PreparationPhysicalFirstChargeFourPointReturn PreparationPhysicalFirstTemporalChargeReturn
open PreparationVacuumFieldConstraintResponse PreparationVacuumSpatialDensityTransport
open PreparationVacuumHalfDensityFiber PreparationVacuumSourceActionJets PreparationVacuumGradedTransport

open PreparationPhysicalTemporalConstraintObserver PreparationPhysicalSignedVolumeWeightReturn
open PreparationPhysicalTemporalNumberOneReturn PreparationVacuumPhysicalN1WardCollapse
open PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalFeedback

open PreparationVacuumCausalPoleResponse PreparationPhysicalUnitCurrentFieldReturn
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumSoftPoleSelection PreparationPhysicalFinitePoleVertices
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumNativeSlowCoupling PreparationVacuumNativePoleTensor
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumFullOriginResponse PreparationVacuumWholeOrigin
attribute [local irreducible] CausalFrequency regularSource originalGreenExpression sourceGreen
  sourceUnitCompleteField originalJacobi

/-- The momenta are restrictions of the original common signed harmonic mode. -/
def sourceSignedModePoint (q : PhysicalResponsePoint) (k : PhysicalMomentum) (i : Fin 4) : PhysicalResponsePoint :=
  {q with k:=sourceModeTransfer k i}

theorem sourceSignedMode_opposite (q : PhysicalResponsePoint) (k : PhysicalMomentum) :
    -(sourceSignedModePoint q k 0).k=k ∧ -(sourceSignedModePoint q k 1).k= -k := by
  simp only [sourceSignedModePoint,sourceModeTransfer,Matrix.cons_val_zero,Matrix.cons_val_one,neg_neg]
  trivial

/-- The actual source and detector spatial profiles come from opposite restrictions, rather than a supplied equality of waves. -/
theorem sourceSignedMode_phase (k : PhysicalMomentum) (x : Position) :
    phase (sourceModeWave k 0) x*phase (sourceModeWave k 1) x=1 := by
  rw [sourceModeWave_actual]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [←sourceHarmonic_phase_add,add_neg_cancel]
  simp only [phase_physical,Pi.zero_apply,zero_mul,Finset.sum_const_zero,Complex.ofReal_zero,Complex.exp_zero]

def sourceSignedPoleWindow (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (T epsilon : ℝ) (n : PhysicalMomentum) (i : Fin 4) (lambda : ℂ) : Fin 289→ℂ :=
  sourceSignedCurrentWindow (sourceSignedModePoint q (epsilon^2 • n) i) sL eL sR eR lambda T

theorem sourceSignedPoleWindow_continuous (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (T epsilon : ℝ) (n : PhysicalMomentum) (i : Fin 4) :
    Continuous (sourceSignedPoleWindow q sL eL sR eR T epsilon n i) :=
  sourceSignedCurrentWindow_continuous _ _ _ _ _ _

open Lean Elab Term Meta in
elab "paidCausalGreenContinuity%" : term => do
  let wanted:=`LowEnergy.PreparationVacuumCausalPoleResponse.originalGreenExpression_continuous_at
  let names:=(←getEnv).constants.toList.filterMap fun (name,_)=>
    if name.toString.startsWith "_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCommonCausalReturn." && privateToUserName name==wanted
    then some name else none
  match names with
  | [name]=>
    logInfo m!"Original causal matrix continuity payer: {name}"
    mkConstWithFreshMVarLevels name
  | _=>
    let alternatives:=(←getEnv).constants.toList.filterMap fun (name,_)=>
      if privateToUserName name==wanted then some name else none
    throwError "Expected unique original causal continuity payer, actual {names}; privateToUserName alternatives {alternatives}"

private theorem causal_continuous (omega : ℝ) (k : PhysicalMomentum) :
    Continuous (fun eta : ℝ=>causalMomentum eta omega k) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · change Continuous (fun eta : ℝ=>(eta:ℂ)-Complex.I*(omega:ℂ))
    fun_prop
  · exact continuous_const

/-- The actual finite-time source numerator moves with the same Laplace frequency as the complete original Green. -/
def sourceSignedDampedField (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (T epsilon sigma : ℝ) (n : PhysicalMomentum) (eta : ℝ) : Fin 289→ℂ :=
  originalGreenExpression (causalMomentum eta (sourceFrequency epsilon sigma) (epsilon^2 • n))*ᵥ
    sourceSignedPoleWindow q sL eL sR eR T epsilon n 0 (causalLambda eta (sourceFrequency epsilon sigma))

/-- At every legal damped point the computed numerator is the original unit-current forcing, with its original field and nine-row supplement. -/
theorem sourceSignedDamped_actual (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (T epsilon sigma : ℝ) (n : PhysicalMomentum) (eta : ℝ) (future : 0≤T) (positive : 0<eta)
    (left : q.z.im≠0) (right : q.w.im≠0)
    (regular : causalMomentum eta (sourceFrequency epsilon sigma) (epsilon^2 • n)∈regularSource) :
    ∃leg : SourceUnitFieldLeg, leg.q=sourceSignedModePoint q (epsilon^2 • n) 0 ∧
      leg.sideL=sL ∧ leg.edgeL=eL ∧ leg.sideR=sR ∧ leg.edgeR=eR ∧ leg.T=T ∧
      leg.frequency.val=causalLambda eta (sourceFrequency epsilon sigma) ∧
      sourceSignedDampedField q sL eL sR eR T epsilon sigma n eta=sourceUnitCompleteField leg ∧
      originalJacobi (sourceUnitFieldPoint leg).val*ᵥsourceUnitCompleteField leg=
        sourceUnitRawForcing leg+sourceUnitConstraintSupplement leg := by
  let sourceQ:=sourceSignedModePoint q (epsilon^2 • n) 0
  have wave : -sourceQ.k=epsilon^2 • n:=(sourceSignedMode_opposite q (epsilon^2 • n)).1
  let frequency : CausalFrequency (-sourceQ.k):=⟨causalLambda eta (sourceFrequency epsilon sigma),
    by
      rw [CausalFrequency,Set.mem_ofPred_eq]
      constructor
      · rw [causalLambda_re]
        exact positive
      · rw [wave]
        exact regular⟩
  let leg : SourceUnitFieldLeg:=⟨sourceQ,sL,eL,sR,eR,T,future,frequency,left,right⟩
  have point : (sourceUnitFieldPoint leg).val=causalMomentum eta (sourceFrequency epsilon sigma) (epsilon^2 • n) := by
    dsimp only [sourceUnitFieldPoint,causalPoint,leg,frequency]
    rw [wave]
    rfl
  have forcing : sourceUnitRawForcing leg=sourceSignedPoleWindow q sL eL sR eR T epsilon n 0
      (causalLambda eta (sourceFrequency epsilon sigma)) :=
    (sourceSignedCurrentWindow_generated sourceQ sL eL sR eR _ T).symm
  refine ⟨leg,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,sourceUnitCompleteField_equation leg⟩
  rw [sourceUnitCompleteField,PreparationVacuumOriginalGreenFeedback.sourceField,←originalGreenExpression_actual,point,forcing]
  rfl

private theorem damped_continuous (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (T epsilon sigma : ℝ) (n : PhysicalMomentum)
    (regular : frequencyRay epsilon sigma n∈regularSource) :
    ContinuousAt (sourceSignedDampedField q sL eL sR eR T epsilon sigma n) 0 := by
  have center : causalMomentum 0 (sourceFrequency epsilon sigma) (epsilon^2 • n)∈regularSource := by
    rw [causalMomentum_zero]
    exact regular
  have green := ((paidCausalGreenContinuity%) _ center).tendsto.comp
    ((causal_continuous (sourceFrequency epsilon sigma) (epsilon^2 • n)).tendsto 0)
  have lambda : Continuous (fun eta : ℝ=>causalLambda eta (sourceFrequency epsilon sigma)) := by
    unfold causalLambda
    fun_prop
  have numerator := (sourceSignedPoleWindow_continuous q sL eL sR eR T epsilon n 0).comp lambda
  exact (continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    (green.prodMk_nhds numerator.continuousAt.tendsto)

private theorem regular_green (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀ᶠ sigma in 𝓝[≠] (sourceSheet branch n unit e.val),
      ∃point : regularSource, point.val=frequencyRay e.val sigma n ∧
        sourceWholePhotonGreen e.val sigma n=sourceGreen point := by
  filter_upwards [scaleVal_tendsto.eventually (sourceSheet_simple branch n unit),
    scaleVal_tendsto.eventually (sourceSheet_equation branch n unit),
    scaleVal_tendsto.eventually (sourceSheet_bounds branch n unit)] with e simple equation bounds
  let center:=sourceSheet branch n unit e.val
  have inside : |center|<1 := by
    apply abs_lt.mpr
    change (if branch=0 then (1/2:ℝ) else (4/5:ℝ))<center ∧ center<(if branch=0 then (2/3:ℝ) else (9/10:ℝ)) at bounds
    split_ifs at bounds <;> constructor <;> linarith
  have slopes:=simple.2.tendsto_slope.eventually_ne simple.1
  have interval:=((continuous_abs.continuousAt : ContinuousAt (fun t : ℝ=>|t|) center).eventually_lt_const inside).filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] center≤𝓝 center)
  filter_upwards [slopes,interval] with t slope insideT
  have nonzero : physicalDeterminant e.val t n≠0 := by
    intro zero
    apply slope
    simp only [slope_def_module,zero,equation,sub_self,smul_zero]
  let s : slopeDomain:=⟨t,insideT.le⟩
  have legal : IsUnit (normalizedEffective e s n (unit_direction_bound n unit)).det := by
    apply isUnit_iff_ne_zero.mpr
    intro zero
    have actual:=extendedTensor_actual e s n (unit_direction_bound n unit)
    rw [←actual] at zero
    apply nonzero
    change (extendedTensor e.val t n).det=0 at zero
    simpa only [physicalDeterminant,Complex.zero_re] using congrArg Complex.re zero
  refine ⟨dynamicPoint e s n (unit_direction_bound n unit) legal,rfl,?_⟩
  ext i j
  rw [sourceWholePhotonGreen,nativeResponse_original e s n (unit_direction_bound n unit) legal]
  simp only [PreparationVacuumOriginalGreenFeedback.sourceField,Matrix.mulVec_single_one,Matrix.col_apply]

def sourceSignedRayField (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (T epsilon sigma : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  sourceWholePhotonGreen epsilon sigma n*ᵥ
    sourceSignedPoleWindow q sL eL sR eR T epsilon n 0 (causalLambda 0 (sourceFrequency epsilon sigma))

/-- Damping is removed only at finite observation time and on the source-generated punctured regular ray. -/
theorem sourceSignedDamped_boundary (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (T : ℝ) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀ᶠ sigma in 𝓝[≠] (sourceSheet branch n unit e.val),
      Tendsto (sourceSignedDampedField q sL eL sR eR T e.val sigma n)
        (𝓝[>] (0:ℝ)) (𝓝 (sourceSignedRayField q sL eL sR eR T e.val sigma n)) := by
  filter_upwards [regular_green branch n unit] with e near
  filter_upwards [near] with sigma data
  obtain ⟨point,coordinate,green⟩:=data
  have regular : frequencyRay e.val sigma n∈regularSource:=coordinate ▸ point.property
  have result := (damped_continuous q sL eL sR eR T e.val sigma n regular).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  have same : sourceSignedDampedField q sL eL sR eR T e.val sigma n 0=
      sourceSignedRayField q sL eL sR eR T e.val sigma n := by
    rw [sourceSignedDampedField,sourceSignedRayField,causalMomentum_zero,←coordinate,
      originalGreenExpression_actual,green]
  rw [same] at result
  exact result

/-- The frequency residue retains the moving finite-window numerator at the physical pole. -/
theorem sourceSignedPoleField_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (T : ℝ) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      Tendsto (fun sigma : ℝ=>((sourceFrequency e.val sigma-
          sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ) •
        sourceSignedRayField q sL eL sR eR T e.val sigma n)
        (𝓝[≠] (sourceSheet branch n unit e.val))
        (𝓝 (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
          sourceSignedPoleWindow q sL eL sR eR T e.val n 0
            (causalLambda 0 (sourceFrequency e.val (sourceSheet branch n unit e.val))))) := by
  filter_upwards [sourceWholePhotonGreen_residue branch n unit] with e pole
  let center:=sourceSheet branch n unit e.val
  have lambda : Continuous (fun sigma : ℝ=>causalLambda 0 (sourceFrequency e.val sigma)) := by
    unfold causalLambda sourceFrequency
    fun_prop
  have current := ((sourceSignedPoleWindow_continuous q sL eL sR eR T e.val n 0).comp lambda).tendsto center
    |>.mono_left (nhdsWithin_le_nhds : 𝓝[≠] center≤𝓝 center)
  have matrix : Tendsto (fun sigma : ℝ=>((e.val^2:ℝ):ℂ) •
      (((sigma-center:ℝ):ℂ) • sourceWholePhotonGreen e.val sigma n))
      (𝓝[≠] center) (𝓝 (((e.val^2:ℝ):ℂ) • sourceWholePhotonResidue e.val center n)) :=
    tendsto_const_nhds.smul pole
  have residue : ((e.val^2:ℝ):ℂ) • sourceWholePhotonResidue e.val center n=
      sourceWholePhotonFrequencyResidue e.val center n := by
    ext i j
    simp only [sourceWholePhotonFrequencyResidue,Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  rw [residue] at matrix
  have returned := (continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    (matrix.prodMk_nhds current)
  change Tendsto (fun sigma : ℝ=>(((e.val^2:ℝ):ℂ) •
      (((sigma-center:ℝ):ℂ) • sourceWholePhotonGreen e.val sigma n))*ᵥ
        sourceSignedPoleWindow q sL eL sR eR T e.val n 0 (causalLambda 0 (sourceFrequency e.val sigma)))
    (𝓝[≠] center) (𝓝 _) at returned
  apply returned.congr'
  filter_upwards [] with sigma
  simp only [sourceSignedRayField,Matrix.smul_mulVec,smul_smul,sourceFrequency,center,
    Complex.ofReal_mul,Complex.ofReal_sub]
  congr 1
  ring

/-- Full physical polarization, including origin, literal slow, fast and residual fields, is read by the calculated current. -/
theorem sourceSignedPole_components (J : Fin 289→ℂ) (branch : Fin 2) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (nonzero : epsilon≠0) :
    (∑i : Fin 289,J i*sourceNativeFrequencyPolarization branch epsilon sigma n i)=
      ∑a : Fin 3,∑i : Fin 289,J i*sourceFinitePoleComponents branch epsilon sigma n a i := by
  rw [sourceFinitePoleComponents_sum branch epsilon sigma n nonzero]
  simp only [Finset.sum_apply,Finset.mul_sum]
  exact Finset.sum_comm

private def sourceDot (J V : Fin 289→ℂ) : ℂ:=∑i,J i*V i

private theorem dot_scaled (c : ℂ) (J V : Fin 289→ℂ) : sourceDot J (c • V)=c*sourceDot J V := by
  simp only [sourceDot,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem dot_continuous : Continuous (fun pair : (Fin 289→ℂ)×(Fin 289→ℂ)=>sourceDot pair.1 pair.2) := by
  unfold sourceDot
  fun_prop

/-- Both current windows follow the same generated opposite mode, with their actual material endpoints retained independently. -/
def sourceSignedRayCoupling (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T epsilon sigma : ℝ) (n : PhysicalMomentum) : ℂ :=
  sourceDot (sourceSignedPoleWindow qd dSL dEL dSR dER T epsilon n 1
    (causalLambda 0 (-sourceFrequency epsilon sigma)))
    (sourceSignedRayField q sL eL sR eR T epsilon sigma n)/
      ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)

def sourceSignedDampedCoupling (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T epsilon sigma : ℝ) (n : PhysicalMomentum) (eta : ℝ) : ℂ :=
  sourceDot (sourceSignedPoleWindow qd dSL dEL dSR dER T epsilon n 1
    (causalLambda eta (-sourceFrequency epsilon sigma)))
    (sourceSignedDampedField q sL eL sR eR T epsilon sigma n eta)/
      ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)

/-- The detector numerator is taken to the same boundary before the frequency pole is approached. -/
theorem sourceSignedCoupling_boundary (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀ᶠ sigma in 𝓝[≠] (sourceSheet branch n unit e.val),
      Tendsto (sourceSignedDampedCoupling branch qd q dSL dEL dSR dER sL eL sR eR T e.val sigma n)
        (𝓝[>] (0:ℝ)) (𝓝 (sourceSignedRayCoupling branch qd q dSL dEL dSR dER sL eL sR eR T e.val sigma n)) := by
  filter_upwards [sourceSignedDamped_boundary q sL eL sR eR T branch n unit] with e near
  filter_upwards [near] with sigma field
  have lambda : Continuous (fun eta : ℝ=>causalLambda eta (-sourceFrequency e.val sigma)) := by
    unfold causalLambda
    fun_prop
  have detector := ((sourceSignedPoleWindow_continuous qd dSL dEL dSR dER T e.val n 1).comp lambda).tendsto 0
    |>.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  exact (dot_continuous.continuousAt.tendsto.comp (detector.prodMk_nhds field)).div_const _

/-- Both physical residue coefficients are now the actual computed configuration currents; beta is not supplied as a charge unit. -/
theorem sourceSignedCoupling_pole (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      Tendsto (fun sigma : ℝ=>((sourceFrequency e.val sigma-
          sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ)*
        sourceSignedRayCoupling branch qd q dSL dEL dSR dER sL eL sR eR T e.val sigma n)
        (𝓝[≠] (sourceSheet branch n unit e.val))
        (𝓝 (sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
          (sourceSignedPoleWindow q sL eL sR eR T e.val n 0
            (causalLambda 0 (sourceFrequency e.val (sourceSheet branch n unit e.val))))*
          (∑a : Fin 3,∑i : Fin 289,
            sourceSignedPoleWindow qd dSL dEL dSR dER T e.val n 1
              (causalLambda 0 (-sourceFrequency e.val (sourceSheet branch n unit e.val))) i*
            sourceFinitePoleComponents branch e.val (sourceSheet branch n unit e.val) n a i)/
          ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ))) := by
  filter_upwards [sourceSignedPoleField_return q sL eL sR eR T branch n unit,
    sourceWholePhotonResidue_factor branch n unit] with e field factor
  let center:=sourceSheet branch n unit e.val
  let Js:=sourceSignedPoleWindow q sL eL sR eR T e.val n 0 (causalLambda 0 (sourceFrequency e.val center))
  let Jd:=sourceSignedPoleWindow qd dSL dEL dSR dER T e.val n 1 (causalLambda 0 (-sourceFrequency e.val center))
  have frequencyFactor : sourceWholePhotonFrequencyResidue e.val center n*ᵥJs=
      sourcePhotonLeftReader branch e.val center n Js • sourceNativeFrequencyPolarization branch e.val center n := by
    rw [sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,factor]
    exact smul_comm _ _ _
  have lambda : Continuous (fun sigma : ℝ=>causalLambda 0 (-sourceFrequency e.val sigma)) := by
    unfold causalLambda sourceFrequency
    fun_prop
  have detector := ((sourceSignedPoleWindow_continuous qd dSL dEL dSR dER T e.val n 1).comp lambda).tendsto center
    |>.mono_left (nhdsWithin_le_nhds : 𝓝[≠] center≤𝓝 center)
  have result := (dot_continuous.continuousAt.tendsto.comp (detector.prodMk_nhds field)).div_const
    ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)
  change Tendsto (fun sigma : ℝ=>sourceDot
      (sourceSignedPoleWindow qd dSL dEL dSR dER T e.val n 1 (causalLambda 0 (-sourceFrequency e.val sigma)))
      (((sourceFrequency e.val sigma-sourceFrequency e.val center:ℝ):ℂ) •
        sourceSignedRayField q sL eL sR eR T e.val sigma n)/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ))
    (𝓝[≠] center) (𝓝 (sourceDot Jd (sourceWholePhotonFrequencyResidue e.val center n*ᵥJs)/
      ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ))) at result
  rw [frequencyFactor,dot_scaled] at result
  have components := sourceSignedPole_components Jd branch e.val center n (ne_of_gt e.property.1)
  change sourceDot Jd (sourceNativeFrequencyPolarization branch e.val center n)=_ at components
  rw [components] at result
  apply result.congr'
  filter_upwards [] with sigma
  rw [dot_scaled,sourceSignedRayCoupling]
  ring

end LowEnergy.PreparationPhysicalSignedCurrentPoleObserver
