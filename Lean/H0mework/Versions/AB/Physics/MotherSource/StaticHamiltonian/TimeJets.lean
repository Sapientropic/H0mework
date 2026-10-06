import H0mework.Versions.AB.Physics.MotherSource.StaticHamiltonian.Hamiltonian

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 150000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticHamiltonian
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineGlobalIntegratedAction StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum
open StageNineTopologicalFourFormPairing StageNineScalarPointwiseEquation StageNineMatterPointwiseEquation
open DiracExteriorMatterAction SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeConnectionVariation
open scoped ContDiff
noncomputable section
local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-- All nine original fields follow the same time-coordinate perturbation about the same point. -/
def stretchMap (point : BasePoint) (rate : ℝ) (candidate : BasePoint) : BasePoint :=
  candidate + (rate*(candidate 0-point 0)) • coordinateDirection 0

@[simp] theorem stretch_self (point : BasePoint) (rate : ℝ) : stretchMap point rate point = point := by
  simp [stretchMap]

def timeStretch (background : StageNineHolonomicConfiguration) (point : BasePoint) (rate : ℝ) :
    StageNineHolonomicConfiguration where
  coframe := background.coframe ∘ stretchMap point rate
  gravityConnection := background.gravityConnection ∘ stretchMap point rate
  gravityAuxiliary := background.gravityAuxiliary ∘ stretchMap point rate
  gravitySimplicityMultiplier := background.gravitySimplicityMultiplier ∘ stretchMap point rate
  gaugeConnection := background.gaugeConnection ∘ stretchMap point rate
  gaugeAuxiliary := background.gaugeAuxiliary ∘ stretchMap point rate
  scalar := background.scalar ∘ stretchMap point rate
  matter := background.matter ∘ stretchMap point rate
  conjugateMatter := background.conjugateMatter ∘ stretchMap point rate

theorem stretch_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : BasePoint → E) (point : BasePoint) (regular : DifferentiableAt ℝ field point)
    (rate : ℝ) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (field ∘ stretchMap point rate) point direction =
      fieldDirectionalDerivative field point direction +
        if direction = 0 then rate • fieldDirectionalDerivative field point 0 else 0 := by
  have mapDerivative : HasFDerivAt (stretchMap point rate)
      (ContinuousLinearMap.id ℝ BasePoint +
        (rate • (EuclideanSpace.proj 0 : BasePoint →L[ℝ] ℝ)).smulRight (coordinateDirection 0)) point :=
    (hasFDerivAt_id point).add
      ((((EuclideanSpace.proj 0 : BasePoint →L[ℝ] ℝ).hasFDerivAt.sub_const (point 0)).const_mul rate).smul_const _)
  have targetDerivative : HasFDerivAt field (fderiv ℝ field point) (stretchMap point rate point) := by
    simpa only [stretch_self] using regular.hasFDerivAt
  unfold fieldDirectionalDerivative
  rw [(targetDerivative.comp point mapDerivative).fderiv]
  by_cases zero : direction = 0
  · subst direction
    simp [coordinateDirection]
  · simp [coordinateDirection, zero, Ne.symm zero]

def temporalScalarVelocity (background : StageNineHolonomicConfiguration) (point : BasePoint) :
    LorentzianIndex → ScalarCoordinateCarrier :=
  scalarVariationDifferentialDirection (fieldDirectionalDerivative background.scalar point 0) 0

def temporalMatterVelocity (background : StageNineHolonomicConfiguration) (point : BasePoint) :
    LorentzianIndex → DiracExteriorMatterCarrier :=
  fun direction => if direction = 0 then matterCoordinateEquiv.symm
    (fieldDirectionalDerivative (fun candidate => matterCoordinateEquiv (background.matter candidate)) point 0) else 0

/-- These jets are generated from the original primitive ordinary-time derivatives. -/
def timeJets (background : StageNineHolonomicConfiguration) (point : BasePoint) (rate : ℝ) :
    StageNineContinuumPointField :=
  { toContinuumPointField background point with
    gravityCurvature := holonomicGravityCurvature background point + rate • gravityVelocityCurvature background point
    gaugeCurvature := holonomicGaugeCurvature background point + rate • gaugeVelocityCurvature background point
    scalarCovariantDerivative := holonomicScalarCovariantDerivative background point + rate • temporalScalarVelocity background point
    matterCovariantDerivative := holonomicMatterCovariantDerivative background point + (rate : ℂ) • temporalMatterVelocity background point }

private theorem gravity_derivative_stretch (background : StageNineHolonomicConfiguration)
    (smooth : background.Smooth) (point : BasePoint) (rate : ℝ)
    (d f i j : LorentzianIndex) :
    gravityConnectionDerivative (timeStretch background point rate) point d f i j =
      gravityConnectionDerivative background point d f i j +
        if d = 0 then rate*gravityConnectionDerivative background point 0 f i j else 0 := by
  have result := stretch_derivative
    (fun candidate => background.gravityConnection candidate f i j) point
    ((smooth.2.1 f i j).differentiable (by simp) point) rate d
  exact result

private theorem gauge_derivative_stretch (background : StageNineHolonomicConfiguration)
    (smooth : background.Smooth) (point : BasePoint) (rate : ℝ) (d f : LorentzianIndex) :
    p286ConnectionDerivative (timeStretch background point rate) point d f =
      p286ConnectionDerivative background point d f +
        if d = 0 then rate • p286ConnectionDerivative background point 0 f else 0 := by
  unfold p286ConnectionDerivative
  change p286CoordinateEquiv.symm (fieldDirectionalDerivative
    ((fun candidate => p286CoordinateEquiv (background.gaugeConnection candidate f)) ∘ stretchMap point rate) point d) = _
  rw [stretch_derivative _ point ((smooth.2.2.2.2.1 f).differentiable (by simp) point)]
  split_ifs <;> simp

theorem gravity_curvature_stretch (background : StageNineHolonomicConfiguration)
    (smooth : background.Smooth) (point : BasePoint) (rate : ℝ) :
    holonomicGravityCurvature (timeStretch background point rate) point =
      holonomicGravityCurvature background point + rate • gravityVelocityCurvature background point := by
  funext internalPair spacetimePair
  simp only [holonomicGravityCurvature, gravity_derivative_stretch background smooth]
  simp only [timeStretch, Function.comp_apply, stretch_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    gravityVelocityCurvature]
  simp only [holonomicGravityCurvature]
  split_ifs <;> ring

theorem gauge_curvature_stretch (background : StageNineHolonomicConfiguration)
    (smooth : background.Smooth) (point : BasePoint) (rate : ℝ) :
    holonomicGaugeCurvature (timeStretch background point rate) point =
      holonomicGaugeCurvature background point + rate • gaugeVelocityCurvature background point := by
  funext pair
  simp only [holonomicGaugeCurvature, gauge_derivative_stretch background smooth]
  simp only [timeStretch, Function.comp_apply, stretch_self, Pi.add_apply, Pi.smul_apply,
    gaugeVelocityCurvature, TemporalGauge.electricForm]
  simp only [holonomicGaugeCurvature]
  fin_cases pair <;> simp [pairFirst, pairSecond] <;> module

theorem scalar_derivative_stretch (background : StageNineHolonomicConfiguration)
    (smooth : background.Smooth) (point : BasePoint) (rate : ℝ) :
    holonomicScalarCovariantDerivative (timeStretch background point rate) point =
      holonomicScalarCovariantDerivative background point + rate • temporalScalarVelocity background point := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  simp only [timeStretch, Function.comp_apply, stretch_self]
  rw [stretch_derivative _ point (smooth.2.2.2.2.2.2.1.differentiable (by simp) point)]
  simp only [temporalScalarVelocity, scalarVariationDifferentialDirection, Pi.add_apply, Pi.smul_apply]
  split_ifs <;> module

theorem matter_derivative_stretch (background : StageNineHolonomicConfiguration)
    (smooth : background.Smooth) (point : BasePoint) (rate : ℝ) :
    holonomicMatterCovariantDerivative (timeStretch background point rate) point =
      holonomicMatterCovariantDerivative background point + (rate : ℂ) • temporalMatterVelocity background point := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  simp only [timeStretch, Function.comp_apply, stretch_self]
  have derivative := stretch_derivative
    (fun candidate => matterCoordinateEquiv (background.matter candidate)) point
    (smooth.2.2.2.2.2.2.2.1.differentiable (by simp) point) rate direction
  change fieldDirectionalDerivative
    (fun candidate => matterCoordinateEquiv (background.matter (stretchMap point rate candidate))) point direction = _ at derivative
  rw [derivative]
  simp only [temporalMatterVelocity, Pi.add_apply, Pi.smul_apply, map_add]
  split_ifs
  all_goals try simp only [StageNineMatterVariation.matterCoordinateEquiv_symm_real_smul, map_zero, add_zero, smul_zero]
  all_goals module

theorem source_time_jets (background : StageNineHolonomicConfiguration) (smooth : background.Smooth)
    (point : BasePoint) (rate : ℝ) :
    toContinuumPointField (timeStretch background point rate) point = timeJets background point rate := by
  refine StageNineContinuumPointField.ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [toContinuumPointField, timeStretch, timeJets]
  · exact gravity_curvature_stretch background smooth point rate
  · simp [toContinuumPointField, timeStretch, timeJets]
  · simp [toContinuumPointField, timeStretch, timeJets]
  · exact gauge_curvature_stretch background smooth point rate
  · simp [toContinuumPointField, timeStretch, timeJets]
  · simp [toContinuumPointField, timeStretch, timeJets]
  · exact scalar_derivative_stretch background smooth point rate
  · simp [toContinuumPointField, timeStretch, timeJets]
  · exact matter_derivative_stretch background smooth point rate
  · simp [toContinuumPointField, timeStretch, timeJets]

end
end SaturationMonoid.PhysicsCore.Stage10.StaticHamiltonian
