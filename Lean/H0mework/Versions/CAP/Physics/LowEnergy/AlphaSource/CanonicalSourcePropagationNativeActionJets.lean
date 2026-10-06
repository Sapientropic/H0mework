import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeActionFieldLift
import H0mework.Versions.AB.Physics.LowEnergyActiveGauge.Phase

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open StageNineLorentzConnectionVariation StageNineDiracDualFormNativeMotherAction
open DiracExteriorMatterAction DiracCliffordRepresentation Stage9C.Material.SpinPair
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical
open PreparationVacuumNativeSourceRestriction SU7ExteriorMatterRestriction SU7ExteriorMatterRepresentation
open SU7MotherGaugeTheory SU7MotherLieAlgebra StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariationDensity StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualYukawaLocalSpinDensity StageNineMatterCovariantDerivativeAffine
open PointwiseDiracSpinConnectionLift StageNineDiracMatterCoordinateCalculus StageNineMatterVariation
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
attribute [local irreducible] SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual
local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : Fintype MatterCoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def scalarInsertionLinear : Field289 →ₗ[ℝ] ScalarCoordinateCarrier where
  toFun := fieldScalar
  map_add' := fieldScalar_add
  map_smul' := fieldScalar_smul

def gaugeInsertionLinear (mu : Fin 4) : Field289 →ₗ[ℝ] NativeLie where
  toFun f := fieldGauge f mu
  map_add' f g := fieldGauge_add f g mu
  map_smul' r f := fieldGauge_smul r f mu

/-- Identical P286 coordinates in their original Euclidean jet norm. -/
def gaugeCoordinateLinear (mu : Fin 4) : Field289 →ₗ[ℝ] P286CoordinateCarrier where
  toFun f := fieldGauge f mu
  map_add' f g := fieldGauge_add f g mu
  map_smul' r f := fieldGauge_smul r f mu

def gaugeCoordinateCLM (mu : Fin 4) : Field289 →L[ℝ] P286CoordinateCarrier :=
  (gaugeCoordinateLinear mu).toContinuousLinearMap

def primalInsertionCoordinates : Field289 →ₗ[ℝ] MatterCoordinateCarrier where
  toFun f := matterCoordinateEquiv (primalInsertion f)
  map_add' f g := by
    change matterCoordinateEquiv (primalInsertion (f+g)) = _
    have coefficient (spin : Fin 4) (color : Fin 3) :
        fieldPrimalComplex (f+g) spin color = fieldPrimalComplex f spin color + fieldPrimalComplex g spin color := by
      simp only [fieldPrimalComplex, fieldPrimal, Pi.add_apply, Complex.ofReal_add]
      ring
    simp only [primalInsertion, coefficient, add_smul, Finset.sum_add_distrib, map_add]
  map_smul' r f := by
    have coefficient (spin : Fin 4) (color : Fin 3) :
        fieldPrimalComplex (r • f) spin color = (r:ℂ)*fieldPrimalComplex f spin color := by
      simp only [fieldPrimalComplex, fieldPrimal, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
      ring
    change matterCoordinateEquiv (primalInsertion (r • f)) = _
    simp only [primalInsertion, coefficient, mul_smul, ←Finset.smul_sum]
    change matterCoordinateEquiv ((r:ℂ) • _) = r • _
    rw [map_smul]
    rfl

def scalarInsertionCLM : Field289 →L[ℝ] ScalarCoordinateCarrier := scalarInsertionLinear.toContinuousLinearMap
def gaugeInsertionCLM (mu : Fin 4) : Field289 →L[ℝ] NativeLie := (gaugeInsertionLinear mu).toContinuousLinearMap
def primalInsertionCLM : Field289 →L[ℝ] MatterCoordinateCarrier := primalInsertionCoordinates.toContinuousLinearMap

private theorem insertion_directionalDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Field289 →L[ℝ] E) (jet : NativeFirstJet) (mu : Fin 4) :
    fieldDirectionalDerivative (fun x => C (affineSignal jet x)) 0 mu = C (jet.2 mu) := by
  have derivative : HasFDerivAt (fun x => C (affineSignal jet x)) (C.comp (jetDerivative jet.2)) 0 :=
    C.hasFDerivAt.comp 0 (affineSignal_hasFDerivAt jet 0)
  rw [fieldDirectionalDerivative, derivative.fderiv]
  change C (jetDerivative jet.2 (coordinateDirection mu)) = C (jet.2 mu)
  exact congrArg C (by simpa [fieldDirectionalDerivative,
    (affineSignal_hasFDerivAt jet 0).fderiv] using affineSignal_directionalDerivative jet mu)

theorem scalarInsertion_derivative (jet : NativeFirstJet) (mu : Fin 4) :
    fieldDirectionalDerivative (fun x => fieldScalar (affineSignal jet x)) 0 mu = fieldScalar (jet.2 mu) :=
  insertion_directionalDerivative scalarInsertionCLM jet mu

theorem gaugeInsertion_derivative (jet : NativeFirstJet) (mu nu : Fin 4) :
    fieldDirectionalDerivative (fun x => fieldGauge (affineSignal jet x) nu) 0 mu = fieldGauge (jet.2 mu) nu :=
  insertion_directionalDerivative (gaugeInsertionCLM nu) jet mu

theorem primalInsertion_derivative (jet : NativeFirstJet) (mu : Fin 4) :
    fieldDirectionalDerivative (fun x => matterCoordinateEquiv (primalInsertion (affineSignal jet x))) 0 mu =
      matterCoordinateEquiv (primalInsertion (jet.2 mu)) :=
  insertion_directionalDerivative primalInsertionCLM jet mu

def nativeGaugeCurvature (jet : NativeFirstJet) (pair : Fin 6) : SU7MotherLieAlgebra.P286LieBlockData :=
  holonomicGaugeCurvature actual 0 pair +
    p286CoordinateEquiv.symm (fieldGauge (jet.2 (pairFirst pair)) (pairSecond pair) -
      fieldGauge (jet.2 (pairSecond pair)) (pairFirst pair)) +
    p286LieBracket (actual.gaugeConnection 0 (pairFirst pair))
      (p286CoordinateEquiv.symm (fieldGauge jet.1 (pairSecond pair))) +
    p286LieBracket (p286CoordinateEquiv.symm (fieldGauge jet.1 (pairFirst pair)))
      (actual.gaugeConnection 0 (pairSecond pair)) +
    p286LieBracket (p286CoordinateEquiv.symm (fieldGauge jet.1 (pairFirst pair)))
      (p286CoordinateEquiv.symm (fieldGauge jet.1 (pairSecond pair)))

private theorem gaugeConnectionDerivative_native (jet : NativeFirstJet) (mu nu : Fin 4) :
    p286ConnectionDerivative (nativeConfiguration (affineSignal jet)) 0 mu nu =
      p286CoordinateEquiv.symm (fieldGauge (jet.2 mu) nu) := by
  unfold p286ConnectionDerivative
  have values : (fun x => p286CoordinateEquiv ((nativeConfiguration (affineSignal jet)).gaugeConnection x nu)) =
      fun x => p286CoordinateEquiv (actual.gaugeConnection 0 nu) + gaugeCoordinateCLM nu (affineSignal jet x) := by
    funext x
    simp only [nativeConfiguration, actual_gaugeConnection, map_add, LinearEquiv.apply_symm_apply]
    rfl
  rw [values]
  unfold fieldDirectionalDerivative
  have derivative : HasFDerivAt
      (fun x => p286CoordinateEquiv (actual.gaugeConnection 0 nu) + gaugeCoordinateCLM nu (affineSignal jet x))
      ((gaugeCoordinateCLM nu).comp (jetDerivative jet.2)) 0 :=
    ((gaugeCoordinateCLM nu).hasFDerivAt.comp 0 (affineSignal_hasFDerivAt jet 0))
      |>.const_add (p286CoordinateEquiv (actual.gaugeConnection 0 nu))
  rw [derivative.fderiv]
  change p286CoordinateEquiv.symm (fieldGauge (jetDerivative jet.2 (coordinateDirection mu)) nu) = _
  have value : jetDerivative jet.2 (coordinateDirection mu) = jet.2 mu := by
    simpa [fieldDirectionalDerivative, (affineSignal_hasFDerivAt jet 0).fderiv]
      using affineSignal_directionalDerivative jet mu
  rw [value]

theorem nativeGaugeCurvature_generated (jet : NativeFirstJet) :
    holonomicGaugeCurvature (nativeConfiguration (affineSignal jet)) 0 = nativeGaugeCurvature jet := by
  funext pair
  have original (mu nu : Fin 4) : p286ConnectionDerivative actual 0 mu nu = 0 := by
    simp [p286ConnectionDerivative, fieldDirectionalDerivative, actual_gaugeConnection]
  change p286ConnectionDerivative (nativeConfiguration (affineSignal jet)) 0 (pairFirst pair) (pairSecond pair) -
    p286ConnectionDerivative (nativeConfiguration (affineSignal jet)) 0 (pairSecond pair) (pairFirst pair) +
    p286LieBracket ((nativeConfiguration (affineSignal jet)).gaugeConnection 0 (pairFirst pair))
      ((nativeConfiguration (affineSignal jet)).gaugeConnection 0 (pairSecond pair)) = _
  rw [gaugeConnectionDerivative_native, gaugeConnectionDerivative_native]
  simp only [nativeConfiguration, affineSignal_zero, p286LieBracket_add_left, p286LieBracket_add_right]
  unfold nativeGaugeCurvature holonomicGaugeCurvature
  rw [original, original, sub_self, zero_add, map_sub]
  abel

def nativeScalarCovariant (jet : NativeFirstJet) (mu : Fin 4) : ScalarCoordinateCarrier :=
  fieldScalar (jet.2 mu) +
    scalarMotherLieAction
      (p286LieBlockEmbed (actual.gaugeConnection 0 mu + p286CoordinateEquiv.symm (fieldGauge jet.1 mu)))
      (actual.scalar 0 + fieldScalar jet.1)

theorem nativeScalarCovariant_generated (jet : NativeFirstJet) :
    holonomicScalarCovariantDerivative (nativeConfiguration (affineSignal jet)) 0 = nativeScalarCovariant jet := by
  funext mu
  unfold holonomicScalarCovariantDerivative nativeScalarCovariant
  have scalarValues : (nativeConfiguration (affineSignal jet)).scalar =
      fun x => actual.scalar 0 + scalarInsertionCLM (affineSignal jet x) := by
    funext x
    simp only [nativeConfiguration, actual_scalar]
    rfl
  have scalarDerivative : fieldDirectionalDerivative (nativeConfiguration (affineSignal jet)).scalar 0 mu =
      fieldScalar (jet.2 mu) := by
    rw [scalarValues]
    unfold fieldDirectionalDerivative
    have derivative : HasFDerivAt (fun x => actual.scalar 0 + scalarInsertionCLM (affineSignal jet x))
        (scalarInsertionCLM.comp (jetDerivative jet.2)) 0 :=
      (scalarInsertionCLM.hasFDerivAt.comp 0 (affineSignal_hasFDerivAt jet 0)) |>.const_add (actual.scalar 0)
    rw [derivative.fderiv]
    have value : jetDerivative jet.2 (coordinateDirection mu) = jet.2 mu := by
      simpa [fieldDirectionalDerivative, (affineSignal_hasFDerivAt jet 0).fderiv]
        using affineSignal_directionalDerivative jet mu
    change fieldScalar (jetDerivative jet.2 (coordinateDirection mu)) = _
    rw [value]
  rw [scalarDerivative]
  simp only [nativeConfiguration, affineSignal_zero]

theorem dualInsertion_yukawa_zero (f : Field289) (scalar : SU7ExteriorBreakingYukawa.ExteriorBreakingScalarCarrier)
    (v : DiracExteriorMatterCarrier) : dualInsertion f (diracDualRightChiralYukawaAction scalar v) = 0 := by
  change (∑ spin : Fin 4, ∑ color : Fin 3, fieldDualComplex f spin color *
    sourceTripletRead (diracDualRightChiralYukawaAction scalar v spin) color) = 0
  simp only [sourceTripletRead,
    Response.Yukawa.output_degree_two_zero, map_zero, Finsupp.zero_apply,
    mul_zero, Finset.sum_const_zero]

def lorentzCoordinatesLinear : Field289 →ₗ[ℝ] LorentzBivectorOneForm where
  toFun := fieldLorentz
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lorentzInsertionLinear : Field289 →ₗ[ℝ] PointwiseLorentzSpinConnection :=
  PreparationVacuumGaugeSourceInjection.lorentzLinear.comp lorentzCoordinatesLinear

def lorentzInsertionCLM : Field289 →L[ℝ] PointwiseLorentzSpinConnection :=
  lorentzInsertionLinear.toContinuousLinearMap

theorem lorentzInsertion_derivative (jet : NativeFirstJet) (mu : Fin 4) :
    fieldDirectionalDerivative (fun x => lorentzInsertionCLM (affineSignal jet x)) 0 mu =
      lorentzInsertionCLM (jet.2 mu) :=
  insertion_directionalDerivative lorentzInsertionCLM jet mu

def nativeGravityCurvature (jet : NativeFirstJet) : PhysicalBivector := fun internal pair =>
  let a := pairFirst internal
  let b := pairSecond internal
  let mu := pairFirst pair
  let nu := pairSecond pair
  holonomicGravityCurvature actual 0 internal pair + minkowskiInternalSign a *
    (lorentzInsertionCLM (jet.2 mu) nu a b - lorentzInsertionCLM (jet.2 nu) mu a b +
      ∑ middle : Fin 4,
        (actual.gravityConnection 0 mu a middle * lorentzInsertionCLM jet.1 nu middle b +
          lorentzInsertionCLM jet.1 mu a middle * actual.gravityConnection 0 nu middle b -
          actual.gravityConnection 0 nu a middle * lorentzInsertionCLM jet.1 mu middle b -
          lorentzInsertionCLM jet.1 nu a middle * actual.gravityConnection 0 mu middle b +
          lorentzInsertionCLM jet.1 mu a middle * lorentzInsertionCLM jet.1 nu middle b -
          lorentzInsertionCLM jet.1 nu a middle * lorentzInsertionCLM jet.1 mu middle b))

private theorem gravityConnectionDerivative_native (jet : NativeFirstJet) (mu nu a b : Fin 4) :
    gravityConnectionDerivative (nativeConfiguration (affineSignal jet)) 0 mu nu a b =
      gravityConnectionDerivative actual 0 mu nu a b + lorentzInsertionCLM (jet.2 mu) nu a b := by
  have insertion : HasFDerivAt (fun x => lorentzInsertionCLM (affineSignal jet x))
      (lorentzInsertionCLM.comp (jetDerivative jet.2)) 0 :=
    lorentzInsertionCLM.hasFDerivAt.comp 0 (affineSignal_hasFDerivAt jet 0)
  let evaluation : PointwiseLorentzSpinConnection →ₗ[ℝ] ℝ :=
    { toFun := fun w => w nu a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have entry := evaluation.toContinuousLinearMap.hasFDerivAt.comp 0 insertion
  have background : HasFDerivAt (fun x : BasePoint => actual.gravityConnection x nu a b)
      (fderiv ℝ (fun x : BasePoint => actual.gravityConnection x nu a b) 0) 0 :=
    ((actual_smooth.2.1 nu a b).differentiable (by simp)).differentiableAt.hasFDerivAt
  have derivative := background.add entry
  change HasFDerivAt (fun x => (nativeConfiguration (affineSignal jet)).gravityConnection x nu a b) _ 0 at derivative
  rw [gravityConnectionDerivative, derivative.fderiv]
  have value : jetDerivative jet.2 (coordinateDirection mu) = jet.2 mu := by
    simpa [fieldDirectionalDerivative, (affineSignal_hasFDerivAt jet 0).fderiv]
      using affineSignal_directionalDerivative jet mu
  change gravityConnectionDerivative actual 0 mu nu a b +
    lorentzInsertionCLM (jetDerivative jet.2 (coordinateDirection mu)) nu a b = _
  rw [value]

theorem nativeGravityCurvature_generated (jet : NativeFirstJet) :
    holonomicGravityCurvature (nativeConfiguration (affineSignal jet)) 0 = nativeGravityCurvature jet := by
  funext internal pair
  unfold holonomicGravityCurvature
  dsimp only
  rw [gravityConnectionDerivative_native, gravityConnectionDerivative_native]
  simp only [nativeConfiguration, affineSignal_zero]
  unfold nativeGravityCurvature holonomicGravityCurvature
  change minkowskiInternalSign (pairFirst internal) *
      (gravityConnectionDerivative actual 0 (pairFirst pair) (pairSecond pair) (pairFirst internal) (pairSecond internal) +
        lorentzInsertionCLM (jet.2 (pairFirst pair)) (pairSecond pair) (pairFirst internal) (pairSecond internal) -
        (gravityConnectionDerivative actual 0 (pairSecond pair) (pairFirst pair) (pairFirst internal) (pairSecond internal) +
          lorentzInsertionCLM (jet.2 (pairSecond pair)) (pairFirst pair) (pairFirst internal) (pairSecond internal)) +
        ∑ middle : Fin 4, ((actual.gravityConnection 0 (pairFirst pair) (pairFirst internal) middle +
          lorentzInsertionCLM jet.1 (pairFirst pair) (pairFirst internal) middle) *
            (actual.gravityConnection 0 (pairSecond pair) middle (pairSecond internal) +
              lorentzInsertionCLM jet.1 (pairSecond pair) middle (pairSecond internal)) -
          (actual.gravityConnection 0 (pairSecond pair) (pairFirst internal) middle +
            lorentzInsertionCLM jet.1 (pairSecond pair) (pairFirst internal) middle) *
              (actual.gravityConnection 0 (pairFirst pair) middle (pairSecond internal) +
                lorentzInsertionCLM jet.1 (pairFirst pair) middle (pairSecond internal)))) = _
  simp only [mul_add, add_mul, add_sub_add_comm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

def primalCoefficientLinear (spin : Fin 4) (color : Fin 3) : Field289 →ₗ[ℝ] ℂ where
  toFun f := fieldPrimalComplex f spin color
  map_add' f g := by
    simp only [fieldPrimalComplex, fieldPrimal, Pi.add_apply, Complex.ofReal_add]
    ring
  map_smul' r f := by
    simp only [fieldPrimalComplex, fieldPrimal, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    change _ = (r:ℂ) * _
    ring

def primalCoefficientCLM (spin : Fin 4) (color : Fin 3) : Field289 →L[ℝ] ℂ :=
  (primalCoefficientLinear spin color).toContinuousLinearMap

def phaseComponents (point : BasePoint) : Fin 4 → ℂ :=
  ![upperPhase point, upperPhase point, lowerPhase point, lowerPhase point]

def phaseComponentVelocity : Fin 4 → ℂ :=
  ![(frequency:ℂ)*Complex.I, (frequency:ℂ)*Complex.I,
    (-frequency:ℂ)*Complex.I, (-frequency:ℂ)*Complex.I]

theorem phaseComponents_first (spin : Fin 4) :
    HasFDerivAt (fun x : BasePoint => phaseComponents x spin)
      ((EuclideanSpace.proj (0:Fin 4) : BasePoint →L[ℝ] ℝ).smulRight (phaseComponentVelocity spin)) 0 := by
  fin_cases spin
  · simpa [phaseComponents, phaseComponentVelocity, upperPhase, phase_zero] using phase_hasFDerivAt frequency (0:BasePoint)
  · simpa [phaseComponents, phaseComponentVelocity, upperPhase, phase_zero] using phase_hasFDerivAt frequency (0:BasePoint)
  · simpa [phaseComponents, phaseComponentVelocity, lowerPhase, phase_zero] using phase_hasFDerivAt (-frequency) (0:BasePoint)
  · simpa [phaseComponents, phaseComponentVelocity, lowerPhase, phase_zero] using phase_hasFDerivAt (-frequency) (0:BasePoint)

def rotatedPrimalCoordinates (jet : NativeFirstJet) (point : BasePoint) : MatterCoordinateCarrier :=
  ∑ spin : Fin 4, ∑ color : Fin 3,
    (phaseComponents point spin * primalCoefficientCLM spin color (affineSignal jet point)) •
      matterCoordinateEquiv (sourceTripletLeg spin color)

theorem rotatedPrimalCoordinates_source (jet : NativeFirstJet) (point : BasePoint) :
    rotatedPrimalCoordinates jet point = matterCoordinateEquiv
      (diracMatrixMatterAction (ActiveGauge.rotation point) (primalInsertion (affineSignal jet point))) := by
  unfold rotatedPrimalCoordinates
  simp only [← map_smul, ← map_sum]
  apply congrArg matterCoordinateEquiv
  funext row
  simp [diracMatrixMatterAction, ActiveGauge.rotation, phaseComponents, primalInsertion,
    sourceTripletLeg, Pi.single_apply, Finset.sum_apply, Matrix.diagonal_apply,
    Finset.smul_sum, smul_smul, primalCoefficientCLM, primalCoefficientLinear]
  apply Finset.sum_congr rfl
  intro color _
  rw [mul_comm]

def rotatedPrimalDerivative (jet : NativeFirstJet) (mu : Fin 4) : MatterCoordinateCarrier :=
  ∑ spin : Fin 4, ∑ color : Fin 3,
    ((if mu = 0 then phaseComponentVelocity spin else 0) * fieldPrimalComplex jet.1 spin color +
      fieldPrimalComplex (jet.2 mu) spin color) • matterCoordinateEquiv (sourceTripletLeg spin color)

theorem rotatedPrimalCoordinates_derivative (jet : NativeFirstJet) (mu : Fin 4) :
    fieldDirectionalDerivative (rotatedPrimalCoordinates jet) 0 mu = rotatedPrimalDerivative jet mu := by
  let coefficient (spin : Fin 4) (color : Fin 3) (x : BasePoint) :=
    phaseComponents x spin * primalCoefficientCLM spin color (affineSignal jet x)
  have hd (spin : Fin 4) (color : Fin 3) :=
    (phaseComponents_first spin).mul ((primalCoefficientCLM spin color).hasFDerivAt.comp 0
      (affineSignal_hasFDerivAt jet 0))
  have hs (spin : Fin 4) (color : Fin 3) := (hd spin color).smul_const
    (matterCoordinateEquiv (sourceTripletLeg spin color))
  have derivative := HasFDerivAt.fun_sum (u := Finset.univ) (fun spin _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun color _ => hs spin color))
  change HasFDerivAt (rotatedPrimalCoordinates jet) _ 0 at derivative
  rw [fieldDirectionalDerivative, derivative.fderiv]
  unfold rotatedPrimalDerivative
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro spin _
  apply Finset.sum_congr rfl
  intro color _
  have value : jetDerivative jet.2 (coordinateDirection mu) = jet.2 mu := by
    simpa [fieldDirectionalDerivative, (affineSignal_hasFDerivAt jet 0).fderiv]
      using affineSignal_directionalDerivative jet mu
  have phaseZero : phaseComponents 0 spin = 1 := by
    fin_cases spin <;> simp [phaseComponents, upperPhase, lowerPhase, phase_zero]
  simp only [ContinuousLinearMap.smulRight_apply, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply, Function.comp_apply,
    affineSignal_zero, phaseZero, one_smul, one_mul, value, smul_eq_mul]
  dsimp only [primalCoefficientCLM, primalCoefficientLinear, LinearMap.toContinuousLinearMap,
    LinearMap.mkContinuous, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  by_cases time : mu = 0
  · subst mu
    simp [coordinateDirection]
    congr 1
    ring
  · simp [coordinateDirection, Ne.symm time, time]

theorem affineSignal_smooth (jet : NativeFirstJet) : ContDiff ℝ ∞ (affineSignal jet) := by
  convert! contDiff_const.add (jetDerivative jet.2).contDiff using 1

theorem phaseComponents_smooth (spin : Fin 4) :
    ContDiff ℝ ∞ (fun p : BasePoint => phaseComponents p spin) := by
  fin_cases spin <;> first
    | exact phase_smooth frequency
    | exact phase_smooth (-frequency)

theorem rotatedPrimalCoordinates_smooth (jet : NativeFirstJet) :
    ContDiff ℝ ∞ (rotatedPrimalCoordinates jet) := by
  apply ContDiff.sum
  intro spin _
  apply ContDiff.sum
  intro color _
  exact ((phaseComponents_smooth spin).mul
    ((primalCoefficientCLM spin color).contDiff.comp (affineSignal_smooth jet))).smul contDiff_const

def nativeMatterValue (jet : NativeFirstJet) : DiracExteriorMatterCarrier :=
  actual.matter 0 + primalInsertion jet.1

def nativeDualValue (jet : NativeFirstJet) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  actual.conjugateMatter 0 + dualInsertion jet.1

def nativeMatterCovariant (jet : NativeFirstJet) (mu : Fin 4) : DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm
    (fieldDirectionalDerivative (fun x => matterCoordinateEquiv (actual.matter x)) 0 mu +
      rotatedPrimalDerivative jet mu) +
    diracMatrixMatterAction
      (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift
        (actual.gravityConnection 0 + lorentzInsertionCLM jet.1) mu) (nativeMatterValue jet) +
    diracExteriorMotherLieAction
      (p286LieBlockEmbed (actual.gaugeConnection 0 mu + p286CoordinateEquiv.symm (fieldGauge jet.1 mu)))
      (nativeMatterValue jet)

theorem nativeMatterValue_generated (jet : NativeFirstJet) :
    (nativeConfiguration (affineSignal jet)).matter 0 = nativeMatterValue jet := by
  simp [nativeConfiguration, nativeMatterValue, affineSignal_zero, ActiveGauge.rotation_zero,
    diracMatrixMatterAction, Matrix.one_apply]

theorem nativeDualValue_generated (jet : NativeFirstJet) :
    (nativeConfiguration (affineSignal jet)).conjugateMatter 0 = nativeDualValue jet := by
  apply LinearMap.ext
  intro v
  simp [nativeConfiguration, nativeDualValue, affineSignal_zero, ActiveGauge.rotation_zero,
    diracMatrixMatterAction, Matrix.one_apply, LinearMap.comp_apply]

theorem nativeMatterCovariant_generated (jet : NativeFirstJet) :
    holonomicMatterCovariantDerivative (nativeConfiguration (affineSignal jet)) 0 = nativeMatterCovariant jet := by
  funext mu
  have values : (fun x => matterCoordinateEquiv ((nativeConfiguration (affineSignal jet)).matter x)) =
      fun x => matterCoordinateEquiv (actual.matter x) + rotatedPrimalCoordinates jet x := by
    funext x
    rw [rotatedPrimalCoordinates_source]
    simp only [nativeConfiguration, map_add]
  obtain ⟨_, _, _, _, _, _, _, actualMatterSmooth, _⟩ := actual_smooth
  have derivative : fieldDirectionalDerivative
      (fun x => matterCoordinateEquiv ((nativeConfiguration (affineSignal jet)).matter x)) 0 mu =
      fieldDirectionalDerivative (fun x => matterCoordinateEquiv (actual.matter x)) 0 mu +
        rotatedPrimalDerivative jet mu := by
    rw [values]
    unfold fieldDirectionalDerivative
    have derivative : HasFDerivAt
        (fun x => matterCoordinateEquiv (actual.matter x) + rotatedPrimalCoordinates jet x)
        (fderiv ℝ (fun x => matterCoordinateEquiv (actual.matter x)) 0 +
          fderiv ℝ (rotatedPrimalCoordinates jet) 0) 0 :=
      (actualMatterSmooth.differentiable (by simp) |>.differentiableAt.hasFDerivAt).add
        ((rotatedPrimalCoordinates_smooth jet).differentiable (by simp) |>.differentiableAt.hasFDerivAt)
    rw [derivative.fderiv]
    change _ + fieldDirectionalDerivative (rotatedPrimalCoordinates jet) 0 mu = _
    rw [rotatedPrimalCoordinates_derivative]
    rfl
  unfold holonomicMatterCovariantDerivative nativeMatterCovariant
  rw [derivative, nativeMatterValue_generated]
  have frame : (nativeConfiguration (affineSignal jet)).gravityConnection 0 =
      actual.gravityConnection 0 + lorentzInsertionCLM jet.1 := by
    simp only [nativeConfiguration, affineSignal_zero]
    rfl
  have gauge : (nativeConfiguration (affineSignal jet)).gaugeConnection 0 =
      fun mu => actual.gaugeConnection 0 mu + p286CoordinateEquiv.symm (fieldGauge jet.1 mu) := by
    simp only [nativeConfiguration, affineSignal_zero]
  rw [frame, gauge]

/-- Explicit tensorial first jets of the same holonomic full-field lift. -/
def nativeJetPoint (jet : NativeFirstJet) : StageNineContinuumPointField where
  coframe := actual.coframe 0 + fieldCoframe jet.1
  gravityCurvature := nativeGravityCurvature jet
  gravityAuxiliary := actual.gravityAuxiliary 0 + fieldGravityB jet.1
  gravitySimplicityMultiplier := actual.gravitySimplicityMultiplier 0 + fieldMultiplier jet.1
  gaugeCurvature := nativeGaugeCurvature jet
  gaugeAuxiliary pair := actual.gaugeAuxiliary 0 pair + gaugeBInsertion jet.1 pair
  scalar := actual.scalar 0 + fieldScalar jet.1
  scalarCovariantDerivative := nativeScalarCovariant jet
  matter := nativeMatterValue jet
  matterCovariantDerivative := nativeMatterCovariant jet
  conjugateMatter := nativeDualValue jet

theorem nativeJetPoint_generated (jet : NativeFirstJet) :
    nativePoint (affineSignal jet) 0 = nativeJetPoint jet := by
  apply StageNineContinuumPointField.ext
  · simp only [nativePoint, toContinuumPointField, nativeConfiguration, nativeJetPoint, affineSignal_zero]
  · exact nativeGravityCurvature_generated jet
  · simp only [nativePoint, toContinuumPointField, nativeConfiguration, nativeJetPoint, affineSignal_zero]
  · simp only [nativePoint, toContinuumPointField, nativeConfiguration, nativeJetPoint, affineSignal_zero]
  · exact nativeGaugeCurvature_generated jet
  · simp only [nativePoint, toContinuumPointField, nativeConfiguration, nativeJetPoint, affineSignal_zero]
  · simp only [nativePoint, toContinuumPointField, nativeConfiguration, nativeJetPoint, affineSignal_zero]
  · exact nativeScalarCovariant_generated jet
  · exact nativeMatterValue_generated jet
  · exact nativeMatterCovariant_generated jet
  · exact nativeDualValue_generated jet

theorem nativeJetDensity_generated (jet : NativeFirstJet) :
    nativeJetDensity jet = generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
      positiveSmoothUnifiedSource (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      0 0 (nativeJetPoint jet) := by
  change sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 0
    (nativePoint (affineSignal jet) 0) = _
  rw [nativeJetPoint_generated]
  rfl

theorem nativeYukawaDensity_zero (jet : NativeFirstJet) :
    generatedDensitizedContinuumDiracDualYukawaDensity positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet) = 0 := by
  unfold generatedDensitizedContinuumDiracDualYukawaDensity generatedContinuumDiracDualYukawaVector
  simp only [matterDualFrameRelative_zeroChart, scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, nativeJetPoint, nativeDualValue, LinearMap.add_apply]
  rw [actual_conjugateMatter]
  simp only [upperDualPhase, lowerDualPhase, upperPhase, lowerPhase, phase_zero, mul_one]
  rw [spinPairDual_yukawa_annihilates, dualInsertion_yukawa_zero]
  simp

def coframeInsertionLinear : Field289 →ₗ[ℝ] LorentzianCoframe where
  toFun := fieldCoframe
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coframeInsertionCLM : Field289 →L[ℝ] LorentzianCoframe := coframeInsertionLinear.toContinuousLinearMap

theorem nativeCoframe_smooth :
    ContDiff ℝ ∞ (fun jet : NativeFirstJet => (nativeJetPoint jet).coframe) := by
  change ContDiff ℝ ∞ (fun jet : NativeFirstJet => actual.coframe 0 + coframeInsertionCLM jet.1)
  exact contDiff_const.add (coframeInsertionCLM.contDiff.comp contDiff_fst)

theorem nativeGravityCurvature_smooth : ContDiff ℝ ∞ nativeGravityCurvature := by
  unfold nativeGravityCurvature
  fun_prop

private theorem wedge_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B R : E → PhysicalBivector) (hB : ContDiff ℝ ∞ B) (hR : ContDiff ℝ ∞ R) :
    ContDiff ℝ ∞ (fun x => StageNineTopologicalFourFormPairing.gravityTopologicalWedgeCoefficient (B x) (R x)) := by
  unfold StageNineTopologicalFourFormPairing.gravityTopologicalWedgeCoefficient
    StageNineTopologicalFourFormPairing.orientedTwoFormWedgeCoefficient
    StageNineTopologicalFourFormPairing.generatedTwoFormWedgeCoefficient
  apply ContDiff.sum
  intro i _
  apply contDiff_const.mul
  apply ContDiff.sum
  intro j _
  exact (contDiff_pi.mp (contDiff_pi.mp hB i) j).mul
    (contDiff_pi.mp (contDiff_pi.mp hR i) _)

theorem nativeGravityDensity_smooth : ContDiff ℝ ∞ (fun jet : NativeFirstJet =>
    StageNineFormNativeMotherAction.generatedFormNativeGravityBFDensity (nativeJetPoint jet) +
      StageNineFormNativeMotherAction.generatedFormNativeGravityConstraintDensity (nativeJetPoint jet)) := by
  have coframe := nativeCoframe_smooth
  have bivector : ContDiff ℝ ∞ (fun jet : NativeFirstJet => actual.gravityAuxiliary 0 + fieldGravityB jet.1) := by
    unfold fieldGravityB
    fun_prop
  have multiplier : ContDiff ℝ ∞ (fun jet : NativeFirstJet => actual.gravitySimplicityMultiplier 0 + fieldMultiplier jet.1) := by
    unfold fieldMultiplier
    fun_prop
  have curvature : ContDiff ℝ ∞ (fun jet : NativeFirstJet =>
      StageNineHolonomicGravityCurvatureVarianceNormalization.gravityInternalPairVarianceNormalization (nativeGravityCurvature jet)) :=
    StageNineHolonomicGravityCurvatureVarianceNormalization.gravityInternalPairVarianceNormalization.toContinuousLinearEquiv.contDiff.comp
      nativeGravityCurvature_smooth
  have dual : ContDiff ℝ ∞ (fun jet : NativeFirstJet =>
      StageNineBlockwiseConstitutive.gravityInternalDualEquiv (actual.gravityAuxiliary 0 + fieldGravityB jet.1)) :=
    StageNineBlockwiseConstitutive.gravityInternalDualEquiv.toContinuousLinearEquiv.contDiff.comp bivector
  have wedge : ContDiff ℝ ∞ (fun jet : NativeFirstJet => physicalIIPlusBivector ((nativeJetPoint jet).coframe)) :=
    StageNineCoframeLocalDifferentiability.physicalIIPlusBivector_contDiff.comp coframe
  exact ((wedge_smooth _ _ bivector curvature).sub (contDiff_const.mul
    (wedge_smooth _ _ bivector dual))).add (wedge_smooth _ _ multiplier (bivector.sub wedge))

def nativeGaugeCoordinateCurvature (jet : NativeFirstJet) (pair : Fin 6) : P286CoordinateCarrier :=
  p286CoordinateEquiv (nativeGaugeCurvature jet pair)

theorem nativeGaugeCoordinateCurvature_smooth (pair : Fin 6) :
    ContDiff ℝ ∞ (fun jet : NativeFirstJet => nativeGaugeCoordinateCurvature jet pair) := by
  let B := p286CoordinateLieBracketBilinear.toContinuousBilinearMap
  have bracket (f g : NativeFirstJet → P286CoordinateCarrier) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
      ContDiff ℝ ∞ (fun jet => p286CoordinateEquiv
        (p286LieBracket (p286CoordinateEquiv.symm (f jet)) (p286CoordinateEquiv.symm (g jet)))) := by
    exact (B.contDiff.comp hf).clm_apply hg
  have direction (mu : Fin 4) : ContDiff ℝ ∞ (fun jet : NativeFirstJet => gaugeCoordinateCLM mu jet.1) :=
    (gaugeCoordinateCLM mu).contDiff.comp contDiff_fst
  have gradient (mu nu : Fin 4) : ContDiff ℝ ∞ (fun jet : NativeFirstJet => gaugeCoordinateCLM nu (jet.2 mu)) := by
    exact (gaugeCoordinateCLM nu).contDiff.comp (by fun_prop)
  unfold nativeGaugeCoordinateCurvature nativeGaugeCurvature
  simp only [map_add, LinearEquiv.apply_symm_apply]
  have original (mu : Fin 4) : actual.gaugeConnection 0 mu =
      p286CoordinateEquiv.symm (p286CoordinateEquiv (actual.gaugeConnection 0 mu)) :=
    (p286CoordinateEquiv.symm_apply_apply _).symm
  rw [original (pairFirst pair), original (pairSecond pair)]
  exact (((contDiff_const.add ((gradient _ _).sub (gradient _ _))).add
    (bracket _ _ contDiff_const (direction _))).add
    (bracket _ _ (direction _) contDiff_const)).add (bracket _ _ (direction _) (direction _))

def ambientCoordinateLinear : P286CoordinateCarrier →ₗ[ℝ] P286AmbientData :=
  p286AmbientLinear.comp p286CoordinateEquiv.symm.toLinearMap

def ambientCoordinateCLM : P286CoordinateCarrier →L[ℝ] P286AmbientData :=
  ambientCoordinateLinear.toContinuousLinearMap

theorem ambientCoordinate_source (data : P286LieBlockData) :
    ambientCoordinateCLM (p286CoordinateEquiv data) = p286AmbientLinear data := by
  change p286AmbientLinear (p286CoordinateEquiv.symm (p286CoordinateEquiv data)) = _
  rw [LinearEquiv.symm_apply_apply]

def gaugeBCoordinateLinear (pair : Fin 6) : Field289 →ₗ[ℝ] P286CoordinateCarrier where
  toFun f := ∑ a : Fin 12, fieldGaugeB f pair a • (show P286CoordinateCarrier from originalUnit a)
  map_add' f g := by
    simp only [fieldGaugeB, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [fieldGaugeB, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

def gaugeBCoordinateCLM (pair : Fin 6) : Field289 →L[ℝ] P286CoordinateCarrier :=
  (gaugeBCoordinateLinear pair).toContinuousLinearMap

theorem nativeGaugeAuxiliary_coordinate_smooth (pair : Fin 6) : ContDiff ℝ ∞
    (fun jet : NativeFirstJet => p286CoordinateEquiv ((nativeJetPoint jet).gaugeAuxiliary pair)) := by
  change ContDiff ℝ ∞ (fun jet : NativeFirstJet => p286CoordinateEquiv
    (actual.gaugeAuxiliary 0 pair + gaugeBInsertion jet.1 pair))
  simp only [map_add, gaugeBInsertion, LinearEquiv.apply_symm_apply]
  exact contDiff_const.add ((gaugeBCoordinateCLM pair).contDiff.comp contDiff_fst)

theorem nativeGaugeCurvature_ambient_smooth (pair : Fin 6) : ContDiff ℝ ∞
    (fun jet : NativeFirstJet => p286AmbientLinear ((nativeJetPoint jet).gaugeCurvature pair)) := by
  have generated := ambientCoordinateCLM.contDiff.comp (nativeGaugeCoordinateCurvature_smooth pair)
  convert! generated using 1
  funext jet
  exact (ambientCoordinate_source (nativeGaugeCurvature jet pair)).symm

theorem nativeGaugeAuxiliary_ambient_smooth (pair : Fin 6) : ContDiff ℝ ∞
    (fun jet : NativeFirstJet => p286AmbientLinear ((nativeJetPoint jet).gaugeAuxiliary pair)) := by
  have generated := ambientCoordinateCLM.contDiff.comp (nativeGaugeAuxiliary_coordinate_smooth pair)
  convert! generated using 1
  funext jet
  exact (ambientCoordinate_source ((nativeJetPoint jet).gaugeAuxiliary pair)).symm

theorem nativeCoframe_zero : (nativeJetPoint 0).coframe = actual.coframe 0 := by
  simp only [nativeJetPoint, Prod.fst_zero]
  have zero : PreparationVacuumMixedFieldReturn.fieldCoframe (0:Field289) = 0 := by
    funext a mu
    rfl
  rw [zero, add_zero]

theorem nativeCoframe_inverse_smooth : ContDiffAt ℝ ∞
    (fun jet : NativeFirstJet => (nativeJetPoint jet).coframe⁻¹) 0 := by
  have coframe := StageNineCoframeVariation.coframe_inv_contDiffAt
    (actual.coframe 0) (actual_nondegenerate 0)
  rw [← nativeCoframe_zero] at coframe
  exact coframe.comp (f := fun jet : NativeFirstJet => (nativeJetPoint jet).coframe) 0 nativeCoframe_smooth.contDiffAt

private theorem matrixPair_smooth {E n : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype n] [DecidableEq n] (M N : E → Matrix n n ℂ) (x : E)
    (hM : ContDiffAt ℝ ∞ M x) (hN : ContDiffAt ℝ ∞ N x) :
    ContDiffAt ℝ ∞ (fun y => -(Matrix.trace (M y * N y)).re) x := by
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  apply ContDiffAt.neg
  apply Complex.reCLM.contDiff.contDiffAt.comp x
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hM i) j).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hN j) i)

private theorem scalarPair_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M N : E → ℂ) (x : E) (hM : ContDiffAt ℝ ∞ M x) (hN : ContDiffAt ℝ ∞ N x) :
    ContDiffAt ℝ ∞ (fun y => -(M y * N y).re) x :=
  (Complex.reCLM.contDiff.contDiffAt.comp x (hM.mul hN)).neg

def nativeConstitutiveCoefficient (coupling : ℝ) (output input : Fin 6) (jet : NativeFirstJet) : ℝ :=
  gaugeOperatorCoefficient (coupling • coframeGaugeSpacetimeHodgeLinear (nativeJetPoint jet).coframe) output input

theorem nativeConstitutiveCoefficient_smooth (coupling : ℝ) (output input : Fin 6) :
    ContDiffAt ℝ ∞ (nativeConstitutiveCoefficient coupling output input) 0 := by
  have coframe := StageNineCoframeLocalDifferentiability.scaledCoframeHodgeOperatorCoefficient_contDiffAt
    (actual.coframe 0) (actual_nondegenerate 0) coupling output input
  rw [← nativeCoframe_zero] at coframe
  change ContDiffAt ℝ ∞ (fun jet : NativeFirstJet => gaugeOperatorCoefficient
    (coupling • coframeGaugeSpacetimeHodgeLinear (nativeJetPoint jet).coframe) output input) 0
  exact coframe.comp (f := fun jet : NativeFirstJet => (nativeJetPoint jet).coframe) 0 nativeCoframe_smooth.contDiffAt

private theorem matrixSector_smooth {E n : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype n] [DecidableEq n] (B F : E → Fin 6 → Matrix n n ℂ)
    (K : E → Fin 6 → Fin 6 → ℝ) (x : E)
    (hB : ∀ pair, ContDiffAt ℝ ∞ (fun y => B y pair) x)
    (hF : ∀ pair, ContDiffAt ℝ ∞ (fun y => F y pair) x)
    (hK : ∀ output input, ContDiffAt ℝ ∞ (fun y => K y output input) x) :
    ContDiffAt ℝ ∞ (fun y =>
      (∑ pair : Fin 6, -(Matrix.trace (B y pair * F y (StageNineTopologicalFourFormPairing.twoFormComplement pair))).re) -
        (1/2:ℝ) * (∑ pair : Fin 6, -(Matrix.trace (B y pair *
          ∑ input : Fin 6, K y (StageNineTopologicalFourFormPairing.twoFormComplement pair) input • B y input)).re)) x := by
  apply ContDiffAt.sub
  · apply ContDiffAt.sum
    intro pair _
    exact matrixPair_smooth _ _ x (hB pair) (hF _)
  · apply contDiffAt_const.mul
    apply ContDiffAt.sum
    intro pair _
    apply matrixPair_smooth _ _ x (hB pair)
    apply ContDiffAt.sum
    intro input _
    exact (hK _ input).smul (hB input)

private theorem scalarSector_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B F : E → Fin 6 → ℂ) (K : E → Fin 6 → Fin 6 → ℝ) (x : E)
    (hB : ∀ pair, ContDiffAt ℝ ∞ (fun y => B y pair) x)
    (hF : ∀ pair, ContDiffAt ℝ ∞ (fun y => F y pair) x)
    (hK : ∀ output input, ContDiffAt ℝ ∞ (fun y => K y output input) x) :
    ContDiffAt ℝ ∞ (fun y =>
      (∑ pair : Fin 6, -(B y pair * F y (StageNineTopologicalFourFormPairing.twoFormComplement pair)).re) -
        (1/2:ℝ) * (∑ pair : Fin 6, -(B y pair *
          ∑ input : Fin 6, K y (StageNineTopologicalFourFormPairing.twoFormComplement pair) input • B y input).re)) x := by
  apply ContDiffAt.sub
  · apply ContDiffAt.sum
    intro pair _
    exact scalarPair_smooth _ _ x (hB pair) (hF _)
  · apply contDiffAt_const.mul
    apply ContDiffAt.sum
    intro pair _
    apply scalarPair_smooth _ _ x (hB pair)
    apply ContDiffAt.sum
    intro input _
    exact (hK _ input).smul (hB input)

theorem nativeGaugeDensity_smooth : ContDiffAt ℝ ∞ (fun jet : NativeFirstJet =>
    StageNineFormNativeMotherAction.generatedFormNativeGaugeDensityAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) (nativeJetPoint jet)) 0 := by
  let boundary := sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource
  have strong := matrixSector_smooth (E := NativeFirstJet) (n := Fin 3)
    (fun jet pair => ((nativeJetPoint jet).gaugeAuxiliary pair).1.val)
    (fun jet pair => ((nativeJetPoint jet).gaugeCurvature pair).1.val)
    (fun jet => fun output input => nativeConstitutiveCoefficient (boundary.strongCouplingSquared:ℝ) output input jet) 0
    (fun pair => (nativeGaugeAuxiliary_ambient_smooth pair).fst.contDiffAt)
    (fun pair => (nativeGaugeCurvature_ambient_smooth pair).fst.contDiffAt)
    (fun _ _ => nativeConstitutiveCoefficient_smooth _ _ _)
  have weak := matrixSector_smooth (E := NativeFirstJet) (n := Fin 2)
    (fun jet pair => ((nativeJetPoint jet).gaugeAuxiliary pair).2.1.val)
    (fun jet pair => ((nativeJetPoint jet).gaugeCurvature pair).2.1.val)
    (fun jet => fun output input => nativeConstitutiveCoefficient (boundary.weakCouplingSquared:ℝ) output input jet) 0
    (fun pair => (nativeGaugeAuxiliary_ambient_smooth pair).snd.fst.contDiffAt)
    (fun pair => (nativeGaugeCurvature_ambient_smooth pair).snd.fst.contDiffAt)
    (fun _ _ => nativeConstitutiveCoefficient_smooth _ _ _)
  have center := scalarSector_smooth (E := NativeFirstJet)
    (fun jet pair => ((nativeJetPoint jet).gaugeAuxiliary pair).2.2.val)
    (fun jet pair => ((nativeJetPoint jet).gaugeCurvature pair).2.2.val)
    (fun jet => fun output input => nativeConstitutiveCoefficient (boundary.hyperchargeCouplingSquared:ℝ) output input jet) 0
    (fun pair => (nativeGaugeAuxiliary_ambient_smooth pair).snd.snd.contDiffAt)
    (fun pair => (nativeGaugeCurvature_ambient_smooth pair).snd.snd.contDiffAt)
    (fun _ _ => nativeConstitutiveCoefficient_smooth _ _ _)
  exact (strong.add weak).add center

theorem nativeScalar_smooth : ContDiff ℝ ∞ (fun jet : NativeFirstJet => (nativeJetPoint jet).scalar) :=
  contDiff_const.add (scalarInsertionCLM.contDiff.comp contDiff_fst)

private theorem scalarAction_coordinate_add (a : P286LieBlockData) (v : P286CoordinateCarrier)
    (phi : ScalarCoordinateCarrier) :
    scalarMotherLieAction (p286LieBlockEmbed (a + p286CoordinateEquiv.symm v)) phi =
      scalarP286ActionBilinear (p286CoordinateEquiv a + v) phi := by
  change scalarMotherLieAction (p286LieBlockEmbed (a + p286CoordinateEquiv.symm v)) phi =
    scalarMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (p286CoordinateEquiv a + v))) phi
  rw [map_add, LinearEquiv.symm_apply_apply]

theorem nativeScalarCovariant_smooth (mu : Fin 4) :
    ContDiff ℝ ∞ (fun jet : NativeFirstJet => nativeScalarCovariant jet mu) := by
  let B := scalarP286ActionBilinear.toContinuousBilinearMap
  have gauge : ContDiff ℝ ∞ (fun jet : NativeFirstJet => p286CoordinateEquiv (actual.gaugeConnection 0 mu) +
      gaugeCoordinateCLM mu jet.1) :=
    contDiff_const.add ((gaugeCoordinateCLM mu).contDiff.comp contDiff_fst)
  have gradient : ContDiff ℝ ∞ (fun jet : NativeFirstJet => scalarInsertionCLM (jet.2 mu)) :=
    scalarInsertionCLM.contDiff.comp (by fun_prop)
  have generated : ContDiff ℝ ∞ (fun jet : NativeFirstJet => scalarInsertionCLM (jet.2 mu) +
      B (p286CoordinateEquiv (actual.gaugeConnection 0 mu) + gaugeCoordinateCLM mu jet.1)
        ((nativeJetPoint jet).scalar)) :=
    gradient.add ((B.contDiff.comp gauge).clm_apply nativeScalar_smooth)
  have values : (fun jet : NativeFirstJet => nativeScalarCovariant jet mu) =
      fun jet => scalarInsertionCLM (jet.2 mu) +
        B (p286CoordinateEquiv (actual.gaugeConnection 0 mu) + gaugeCoordinateCLM mu jet.1) ((nativeJetPoint jet).scalar) := by
    funext jet
    change scalarInsertionCLM (jet.2 mu) + scalarMotherLieAction
      (p286LieBlockEmbed (actual.gaugeConnection 0 mu + p286CoordinateEquiv.symm (gaugeCoordinateCLM mu jet.1)))
      ((nativeJetPoint jet).scalar) = scalarInsertionCLM (jet.2 mu) +
      B (p286CoordinateEquiv (actual.gaugeConnection 0 mu) + gaugeCoordinateCLM mu jet.1) ((nativeJetPoint jet).scalar)
    exact congrArg (fun w : ScalarCoordinateCarrier => scalarInsertionCLM (jet.2 mu) + w)
      (scalarAction_coordinate_add _ _ _)
  rw [values]
  exact generated

theorem nativeVolume_smooth : ContDiffAt ℝ ∞ (fun jet : NativeFirstJet => generatedVolumeDensity (nativeJetPoint jet)) 0 := by
  have volume := StageNineCoframeVariation.coframe_volume_contDiffAt (actual.coframe 0) (actual_nondegenerate 0)
  rw [← nativeCoframe_zero] at volume
  exact volume.comp (f := fun jet : NativeFirstJet => (nativeJetPoint jet).coframe) 0 nativeCoframe_smooth.contDiffAt

private theorem scalarCoordinatePair_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M N : E → ScalarCoordinateCarrier) (x : E) (hM : ContDiffAt ℝ ∞ M x) (hN : ContDiffAt ℝ ∞ N x) :
    ContDiffAt ℝ ∞ (fun y => scalarCoordinatePairingRe (M y) (N y)) x := by
  unfold scalarCoordinatePairingRe
  apply ContDiffAt.sum
  intro i _
  let evaluation := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : ScalarBasisIndex => ℂ) i).restrictScalars ℝ
  have m := evaluation.contDiff.contDiffAt.comp x hM
  have n := evaluation.contDiff.contDiffAt.comp x hN
  exact Complex.reCLM.contDiff.contDiffAt.comp x
    (((RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.contDiffAt.comp x m).mul n)

theorem nativeScalarKinetic_smooth : ContDiffAt ℝ ∞ (fun jet : NativeFirstJet =>
    generatedScalarKineticDensity positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet)) 0 := by
  have inverse := StageNineCoframeLocalDifferentiability.lorentzianMetric_inv_contDiffAt
    (actual.coframe 0) (actual_nondegenerate 0)
  rw [← nativeCoframe_zero] at inverse
  have metric := inverse.comp (f := fun jet : NativeFirstJet => (nativeJetPoint jet).coframe) 0 nativeCoframe_smooth.contDiffAt
  unfold generatedScalarKineticDensity
  simp only [scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart,
    nativeJetPoint]
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro mu _
  apply ContDiffAt.sum
  intro nu _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp metric mu) nu).mul
    (scalarCoordinatePair_smooth _ _ 0 (nativeScalarCovariant_smooth mu).contDiffAt
      (nativeScalarCovariant_smooth nu).contDiffAt)

theorem nativeScalarPotential_smooth : ContDiff ℝ ∞ (fun jet : NativeFirstJet =>
    generatedScalarPotential positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet).scalar) := by
  unfold generatedScalarPotential
  simp only [scalarFrameRelativeCoordinates_zeroChart]
  have delta := nativeScalar_smooth.sub (contDiff_const (c := sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))
  unfold scalarCoordinateSquaredNorm
  apply ContDiff.sum
  intro i _
  let evaluation := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : ScalarBasisIndex => ℂ) i).restrictScalars ℝ
  have value := evaluation.contDiff.comp delta
  simp only [Complex.normSq_apply]
  have re := Complex.reCLM.contDiff.comp value
  have im := Complex.imCLM.contDiff.comp value
  exact (re.mul re).add (im.mul im)

theorem nativeScalarDensity_smooth : ContDiffAt ℝ ∞ (fun jet : NativeFirstJet =>
    StageNineScalarLocalSpinDensity.generatedDensitizedContinuumScalarDensity
      positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet)) 0 := by
  exact nativeVolume_smooth.mul (nativeScalarKinetic_smooth.sub nativeScalarPotential_smooth.contDiffAt)

abbrev spinCoordinateBilinear := StageNineDiracMatterCoordinateCalculus.diracMatrixMatterCoordinateRealBilinear

theorem nativeMatterValue_smooth : ContDiff ℝ ∞ (fun jet : NativeFirstJet => matterCoordinateEquiv (nativeMatterValue jet)) := by
  have values : (fun jet : NativeFirstJet => matterCoordinateEquiv (nativeMatterValue jet)) =
      fun jet => matterCoordinateEquiv (actual.matter 0) + primalInsertionCLM jet.1 := by
    funext jet
    exact matterCoordinateEquiv.map_add _ _
  rw [values]
  exact contDiff_const.add (primalInsertionCLM.contDiff.comp contDiff_fst)

theorem rotatedPrimalDerivative_smooth (mu : Fin 4) :
    ContDiff ℝ ∞ (fun jet : NativeFirstJet => rotatedPrimalDerivative jet mu) := by
  unfold rotatedPrimalDerivative
  apply ContDiff.sum
  intro spin _
  apply ContDiff.sum
  intro color _
  change ContDiff ℝ ∞ (fun jet : NativeFirstJet =>
    ((if mu=0 then phaseComponentVelocity spin else 0) * primalCoefficientCLM spin color jet.1 +
      primalCoefficientCLM spin color (jet.2 mu)) • matterCoordinateEquiv (sourceTripletLeg spin color))
  exact (contDiff_const.mul ((primalCoefficientCLM spin color).contDiff.comp contDiff_fst) |>.add
    ((primalCoefficientCLM spin color).contDiff.comp (by fun_prop))).smul contDiff_const

private theorem spinCoordinate_apply (a : DiracMatrix) (v : MatterCoordinateCarrier) :
    spinCoordinateBilinear.toContinuousBilinearMap a v =
      matterCoordinateEquiv (diracMatrixMatterAction a (matterCoordinateEquiv.symm v)) := rfl

private theorem gaugeCoordinate_apply (a : P286CoordinateCarrier) (v : MatterCoordinateCarrier) :
    matterP286ActionCoordinateBilinear.toContinuousBilinearMap a v =
      matterCoordinateEquiv (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm a))
        (matterCoordinateEquiv.symm v)) := rfl

private theorem matterAction_coordinate_add (a : P286LieBlockData) (v : P286CoordinateCarrier)
    (psi : DiracExteriorMatterCarrier) :
    matterCoordinateEquiv (diracExteriorMotherLieAction (p286LieBlockEmbed (a+p286CoordinateEquiv.symm v)) psi) =
      matterP286ActionCoordinateBilinear.toContinuousBilinearMap (p286CoordinateEquiv a+v)
        (matterCoordinateEquiv psi) := by
  rw [gaugeCoordinate_apply, LinearEquiv.symm_apply_apply, map_add, LinearEquiv.symm_apply_apply]

theorem nativeMatterCovariant_smooth (mu : Fin 4) : ContDiff ℝ ∞
    (fun jet : NativeFirstJet => matterCoordinateEquiv (nativeMatterCovariant jet mu)) := by
  let S := spinCoordinateBilinear.toContinuousBilinearMap
  let A := matterP286ActionCoordinateBilinear.toContinuousBilinearMap
  let spinLift := (PointwiseDiracSpinConnectionLift.diracSpinConnectionLiftLinear mu).toContinuousLinearMap
  have spin : ContDiff ℝ ∞ (fun jet : NativeFirstJet => PointwiseDiracSpinConnectionLift.diracSpinConnectionLift
      (actual.gravityConnection 0 + lorentzInsertionCLM jet.1) mu) :=
    spinLift.contDiff.comp (contDiff_const.add (lorentzInsertionCLM.contDiff.comp contDiff_fst))
  have gauge : ContDiff ℝ ∞ (fun jet : NativeFirstJet => p286CoordinateEquiv (actual.gaugeConnection 0 mu) +
      gaugeCoordinateCLM mu jet.1) :=
    contDiff_const.add ((gaugeCoordinateCLM mu).contDiff.comp contDiff_fst)
  have derivative : ContDiff ℝ ∞ (fun jet : NativeFirstJet =>
      fieldDirectionalDerivative (fun x => matterCoordinateEquiv (actual.matter x)) 0 mu + rotatedPrimalDerivative jet mu) :=
    contDiff_const.add (rotatedPrimalDerivative_smooth mu)
  have generated := (derivative.add ((S.contDiff.comp spin).clm_apply nativeMatterValue_smooth)).add
    ((A.contDiff.comp gauge).clm_apply nativeMatterValue_smooth)
  convert! generated using 1
  funext jet
  dsimp only [Function.comp_apply]
  rw [spinCoordinate_apply, LinearEquiv.symm_apply_apply]
  change matterCoordinateEquiv (nativeMatterCovariant jet mu) =
    fieldDirectionalDerivative (fun x => matterCoordinateEquiv (actual.matter x)) 0 mu + rotatedPrimalDerivative jet mu +
      matterCoordinateEquiv (diracMatrixMatterAction
        (diracSpinConnectionLift (actual.gravityConnection 0+lorentzInsertionCLM jet.1) mu) (nativeMatterValue jet)) +
      A (p286CoordinateEquiv (actual.gaugeConnection 0 mu)+gaugeCoordinateCLM mu jet.1) (matterCoordinateEquiv (nativeMatterValue jet))
  have original := matterAction_coordinate_add (actual.gaugeConnection 0 mu) (gaugeCoordinateCLM mu jet.1) (nativeMatterValue jet)
  change matterCoordinateEquiv (diracExteriorMotherLieAction
      (p286LieBlockEmbed (actual.gaugeConnection 0 mu+p286CoordinateEquiv.symm (fieldGauge jet.1 mu))) (nativeMatterValue jet)) = _ at original
  have split : matterCoordinateEquiv (nativeMatterCovariant jet mu) =
      fieldDirectionalDerivative (fun x => matterCoordinateEquiv (actual.matter x)) 0 mu + rotatedPrimalDerivative jet mu +
        matterCoordinateEquiv (diracMatrixMatterAction
          (diracSpinConnectionLift (actual.gravityConnection 0+lorentzInsertionCLM jet.1) mu) (nativeMatterValue jet)) +
        matterCoordinateEquiv (diracExteriorMotherLieAction
          (p286LieBlockEmbed (actual.gaugeConnection 0 mu+p286CoordinateEquiv.symm (fieldGauge jet.1 mu)))
            (nativeMatterValue jet)) := by
    simp only [nativeMatterCovariant, map_add, LinearEquiv.apply_symm_apply]
  exact split.trans (congrArg (fun v : MatterCoordinateCarrier =>
    fieldDirectionalDerivative (fun x => matterCoordinateEquiv (actual.matter x)) 0 mu + rotatedPrimalDerivative jet mu +
      matterCoordinateEquiv (diracMatrixMatterAction
        (diracSpinConnectionLift (actual.gravityConnection 0+lorentzInsertionCLM jet.1) mu) (nativeMatterValue jet)) + v) original)

def nativeKineticCoordinates (jet : NativeFirstJet) : MatterCoordinateCarrier :=
  Complex.I • ∑ mu : Fin 4, spinCoordinateBilinear
    (inverseCoframeDiracGamma
      {coframe := (nativeJetPoint jet).coframe, derivative := 0} mu)
    (matterCoordinateEquiv (nativeMatterCovariant jet mu))

theorem nativeKineticCoordinates_smooth : ContDiffAt ℝ ∞ nativeKineticCoordinates 0 := by
  let S := spinCoordinateBilinear.toContinuousBilinearMap
  have gamma (mu : Fin 4) := StageNineCoframeLocalDifferentiability.inverseCoframeDiracGamma_contDiffAt
    (actual.coframe 0) (actual_nondegenerate 0) mu
  have matrix (mu : Fin 4) : ContDiffAt ℝ ∞ (fun jet : NativeFirstJet =>
      inverseCoframeDiracGamma
        {coframe := (nativeJetPoint jet).coframe, derivative := 0} mu) 0 := by
    have primitive := gamma mu
    rw [← nativeCoframe_zero] at primitive
    exact primitive.comp (f := fun jet : NativeFirstJet => (nativeJetPoint jet).coframe) 0 nativeCoframe_smooth.contDiffAt
  unfold nativeKineticCoordinates
  apply ContDiffAt.const_smul
  apply ContDiffAt.sum
  intro mu _
  exact (S.contDiff.contDiffAt.comp 0 (matrix mu)).clm_apply (nativeMatterCovariant_smooth mu).contDiffAt

theorem nativeKineticCoordinates_original (jet : NativeFirstJet) :
    nativeKineticCoordinates jet = matterCoordinateEquiv
      (StageNineDiracKineticLocalSpinDensity.generatedContinuumMatterKineticVector
        positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet)) := by
  unfold nativeKineticCoordinates StageNineDiracKineticLocalSpinDensity.generatedContinuumMatterKineticVector
    StageNineMatterCovariantDerivativeAffine.matterCovariantDerivativeVariationVector
    StageNineMatterCovariantDerivativeAffine.matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart, nativeJetPoint, map_smul, map_sum, spinCoordinateBilinear,
    diracMatrixMatterCoordinateRealBilinear_apply,
    LinearEquiv.symm_apply_apply]

def dualCoefficientLinear (spin : Fin 4) (color : Fin 3) : Field289 →ₗ[ℝ] ℂ where
  toFun f := fieldDualComplex f spin color
  map_add' f g := by
    simp only [fieldDualComplex, fieldDual, Pi.add_apply, Complex.ofReal_add]
    ring
  map_smul' r f := by
    simp only [fieldDualComplex, fieldDual, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    change _ = (r:ℂ) * _
    ring

def dualCoefficientCLM (spin : Fin 4) (color : Fin 3) : Field289 →L[ℝ] ℂ :=
  (dualCoefficientLinear spin color).toContinuousLinearMap

def matterReadLinear (spin : Fin 4) (color : Fin 3) : MatterCoordinateCarrier →ₗ[ℝ] ℂ where
  toFun v := sourceTripletRead (matterCoordinateEquiv.symm v spin) color
  map_add' v w := by
    simp only [map_add, Pi.add_apply, sourceTripletRead, Prod.snd_add, Prod.fst_add,
      map_add, Finsupp.add_apply]
  map_smul' r v := by
    simp only [matterCoordinateEquiv_symm_real_smul, Pi.smul_apply, sourceTripletRead,
      Prod.snd_smul, Prod.fst_smul]
    change (su7ExteriorBasis 2).repr ((r:ℂ) • (matterCoordinateEquiv.symm v spin).2.1)
      (sourceTripletIndex color) = r • _
    rw [map_smul]
    rfl

def matterReadCLM (spin : Fin 4) (color : Fin 3) : MatterCoordinateCarrier →L[ℝ] ℂ :=
  (matterReadLinear spin color).toContinuousLinearMap

def originalDualCLM : MatterCoordinateCarrier →L[ℝ] ℂ :=
  ((actual.conjugateMatter 0).comp matterCoordinateEquiv.symm.toLinearMap).restrictScalars ℝ |>.toContinuousLinearMap

def nativeKineticPair (jet : NativeFirstJet) : ℂ :=
  originalDualCLM (nativeKineticCoordinates jet) + ∑ spin : Fin 4, ∑ color : Fin 3,
    dualCoefficientCLM spin color jet.1 * matterReadCLM spin color (nativeKineticCoordinates jet)

theorem nativeKineticPair_smooth : ContDiffAt ℝ ∞ nativeKineticPair 0 := by
  apply ContDiffAt.add
  · exact originalDualCLM.contDiff.contDiffAt.comp 0 nativeKineticCoordinates_smooth
  · apply ContDiffAt.sum
    intro spin _
    apply ContDiffAt.sum
    intro color _
    exact ((dualCoefficientCLM spin color).contDiff.contDiffAt.comp 0 contDiffAt_fst).mul
      ((matterReadCLM spin color).contDiff.contDiffAt.comp 0 nativeKineticCoordinates_smooth)

private theorem dualPair_coordinate (f : Field289) (v : DiracExteriorMatterCarrier) :
    originalDualCLM (matterCoordinateEquiv v) + ∑ spin : Fin 4, ∑ color : Fin 3,
      dualCoefficientCLM spin color f * matterReadCLM spin color (matterCoordinateEquiv v) =
      (actual.conjugateMatter 0 + dualInsertion f) v := by
  change actual.conjugateMatter 0 (matterCoordinateEquiv.symm (matterCoordinateEquiv v)) +
      (∑ spin : Fin 4, ∑ color : Fin 3, fieldDualComplex f spin color *
        sourceTripletRead (matterCoordinateEquiv.symm (matterCoordinateEquiv v) spin) color) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem nativeKineticPair_original (jet : NativeFirstJet) :
    nativeKineticPair jet = (nativeJetPoint jet).conjugateMatter
      (StageNineDiracKineticLocalSpinDensity.generatedContinuumMatterKineticVector
        positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet)) := by
  unfold nativeKineticPair
  rw [nativeKineticCoordinates_original]
  exact dualPair_coordinate jet.1 _

theorem nativeDiracKinetic_smooth : ContDiffAt ℝ ∞ (fun jet : NativeFirstJet =>
    StageNineDiracKineticLocalSpinDensity.generatedDensitizedContinuumMatterKineticDensity
      positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet)) 0 := by
  have realPair := Complex.reCLM.contDiff.contDiffAt.comp 0 nativeKineticPair_smooth
  have generated := nativeVolume_smooth.mul realPair
  have values : (fun jet : NativeFirstJet =>
      StageNineDiracKineticLocalSpinDensity.generatedDensitizedContinuumMatterKineticDensity
        positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet)) =
      fun jet => generatedVolumeDensity (nativeJetPoint jet) * (nativeKineticPair jet).re := by
    funext jet
    rw [nativeKineticPair_original]
    unfold StageNineDiracKineticLocalSpinDensity.generatedDensitizedContinuumMatterKineticDensity
    rw [matterDualFrameRelative_zeroChart]
  rw [values]
  exact generated

theorem nativeJetDensity_smooth : ContDiffAt ℝ ∞ nativeJetDensity 0 := by
  have values : nativeJetDensity = fun jet : NativeFirstJet =>
      StageNineFormNativeMotherAction.generatedFormNativeGravityBFDensity (nativeJetPoint jet) +
      StageNineFormNativeMotherAction.generatedFormNativeGravityConstraintDensity (nativeJetPoint jet) +
      StageNineFormNativeMotherAction.generatedFormNativeGaugeDensityAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) (nativeJetPoint jet) +
      StageNineScalarLocalSpinDensity.generatedDensitizedContinuumScalarDensity
        positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet) +
      StageNineDiracKineticLocalSpinDensity.generatedDensitizedContinuumMatterKineticDensity
        positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet) := by
    funext jet
    rw [nativeJetDensity_generated]
    unfold generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary generatedDiracDualFormNativeMatterDensity
      generatedDensitizedContinuumDiracDualMatterDensity
    rw [nativeYukawaDensity_zero]
    ring
  rw [values]
  exact ((nativeGravityDensity_smooth.contDiffAt.add nativeGaugeDensity_smooth).add
    nativeScalarDensity_smooth).add nativeDiracKinetic_smooth

def nativeFirstDensity (jet : NativeFirstJet) : ℝ := fderiv ℝ nativeJetDensity 0 jet

def nativeSecondDensity (jet : NativeFirstJet) : ℝ :=
  (1/2:ℝ) * (fderiv ℝ (fderiv ℝ nativeJetDensity) 0 jet) jet

theorem nativeFirstDensity_generated (jet : NativeFirstJet) :
    HasDerivAt (fun r : ℝ => nativeJetDensity (r • jet)) (nativeFirstDensity jet) 0 := by
  have line : HasDerivAt (fun r : ℝ => r • jet) jet 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const jet
  exact nativeJetDensity_smooth.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt_of_eq
    0 line (by simp)

theorem nativeSecondDensity_generated (jet : NativeFirstJet) :
    HasDerivAt (fun r : ℝ => fderiv ℝ nativeJetDensity (r • jet) jet) (2 * nativeSecondDensity jet) 0 := by
  have line : HasDerivAt (fun r : ℝ => r • jet) jet 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const jet
  have derivative := (nativeJetDensity_smooth.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 line (by simp)
  have evaluation := derivative.clm_apply (hasDerivAt_const (0:ℝ) jet)
  convert! evaluation using 1
  simp only [nativeSecondDensity, zero_smul, add_zero, Function.comp_apply, map_zero]
  ring

def nativeHessian : NativeFirstJet →L[ℝ] NativeFirstJet →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ nativeJetDensity) 0

theorem nativeHessian_generated : HasFDerivAt (fderiv ℝ nativeJetDensity) nativeHessian 0 :=
  (nativeJetDensity_smooth.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp) |>.hasFDerivAt

theorem nativeHessian_symmetric (first second : NativeFirstJet) :
    nativeHessian first second = nativeHessian second first := by
  have order : (2:ℕ∞ω) ≤ ∞ := by
    change ((2:ℕ∞):ℕ∞ω) ≤ ((⊤:ℕ∞):ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact (nativeJetDensity_smooth.isSymmSndFDerivAt (by simpa using order)).eq first second

theorem nativeHessian_diagonal (jet : NativeFirstJet) :
    nativeHessian jet jet = 2 * nativeSecondDensity jet := by
  unfold nativeHessian nativeSecondDensity
  ring

end LowEnergy.SourcePropagationNativeActionHessian
