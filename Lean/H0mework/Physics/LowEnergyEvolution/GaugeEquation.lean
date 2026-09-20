import H0mework.Physics.LowEnergyEvolution.GaugeCurrent

/-! Actual constitutive derivatives close the original gauge Euler channel. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineP286GaugeConnectionVariation
open StageNineP286GaugeAuxiliaryVariation StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeGeometricFirstVariation StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineP286SourceRelativeWardAlgebra StageNineResidualLinearPlebanskiTorsionReduction
open StageNineLorentzConnectionVariation
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open Stage10.GaugeSpectrum.Dynamics Set Filter
open scoped Topology
noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance
local instance : NormedAddCommGroup P286CoordinateCarrier :=
  PiLp.normedAddCommGroup 2 (fun _ : P286CoordinateIndex => ℝ)
local instance : NormedSpace ℝ P286CoordinateCarrier :=
  PiLp.normedSpace 2 ℝ (fun _ : P286CoordinateIndex => ℝ)

def gaugeAuxiliaryCoordinates (x : State) : P286GaugeTwoForm :=
  electricAmplitude x • electricCoordinates + magneticAmplitude x • magneticCoordinates

theorem gaugeAuxiliary_coordinates (x : State) :
    (fun pair => p286CoordinateEquiv (gaugeAuxiliary x pair)) = gaugeAuxiliaryCoordinates x := by
  funext pair
  fin_cases pair <;> simp [gaugeAuxiliaryCoordinates, gaugeAuxiliary, electricCoordinates,
    magneticCoordinates, map_smul]

def electricRate (x : State) : ℝ := fderiv ℝ electricAmplitude x (generator x)
def gaugeAuxiliaryJet (x : State) (mu : LorentzianIndex) : P286GaugeTwoForm :=
  if mu = 0 then electricRate x • electricCoordinates +
    (generator x 3 / sourceCoupling) • magneticCoordinates else 0

theorem electricAmplitude_differentiableAt (x : State) (h : Admissible x) :
    DifferentiableAt ℝ electricAmplitude x := by
  have smoothClock := (clock_contDiffAt x h).differentiableAt (by simp)
  have hn := ne_of_gt (clock_positive x h)
  have hs : sourceCoupling ≠ 0 := by rw [sourceCoupling_eq]; norm_num
  unfold electricAmplitude
  fun_prop (disch := positivity)

theorem Solution.gauge_auxiliary_derivative {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) (mu : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative flow.configuration point mu =
      gaugeAuxiliaryJet (flow.pointState point) mu := by
  have electric := (electricAmplitude_differentiableAt _ (flow.admissible _ inside)).hasFDerivAt.comp_hasDerivAt
    (point 0) (flow.evolves _ inside)
  change HasDerivAt (fun time => electricAmplitude (flow.curve time))
    (electricRate (flow.pointState point)) (point 0) at electric
  have magnetic := (flow.coordinate_derivative _ inside 3).div_const sourceCoupling
  have derivative := (electric.smul_const electricCoordinates).add (magnetic.smul_const magneticCoordinates)
  have composed := derivative.hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun p : BasePoint => gaugeAuxiliaryCoordinates (flow.pointState p)) _ point at composed
  have neighborhood : ∀ᶠ p : BasePoint in 𝓝 point, p 0 ∈ Ioo (-flow.radius) flow.radius :=
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).continuous.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds inside)
  have localValues : holonomicP286GaugeAuxiliaryCoordinate flow.configuration =ᶠ[𝓝 point]
      fun p => gaugeAuxiliaryCoordinates (flow.pointState p) := by
    filter_upwards [neighborhood] with p hp
    change (fun pair => p286CoordinateEquiv (flow.configuration.gaugeAuxiliary p pair)) = _
    rw [flow.gauge_auxiliary p hp, gaugeAuxiliary_coordinates]
  unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
  rw [localValues.fderiv_eq, composed.fderiv]
  change (coordinateDirection mu) 0 •
    (electricRate (flow.pointState point) • electricCoordinates +
      (generator (flow.pointState point) 3 / sourceCoupling) • magneticCoordinates) = _
  by_cases same : mu = 0
  · simp [gaugeAuxiliaryJet, same, coordinateDirection]
  · simp [gaugeAuxiliaryJet, same, coordinateDirection, Ne.symm same]

private theorem triadExterior (amplitude electric magnetic electricRate magneticRate : ℝ) :
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
      (fun mu => p286CoordinateEquiv (gaugePotential amplitude mu))
      (electric • electricCoordinates + magnetic • magneticCoordinates)
      (fun mu => if mu = 0 then electricRate • electricCoordinates + magneticRate • magneticCoordinates else 0) =
      ![(magneticRate+2*amplitude*electric) • p286CoordinateEquiv (sourceColorP286Generator 2),
        (-(magneticRate+2*amplitude*electric)) • p286CoordinateEquiv (sourceColorP286Generator 1),
        (magneticRate+2*amplitude*electric) • p286CoordinateEquiv (sourceColorP286Generator 0),0] := by
  have bracket (first second : Fin 3) :
      p286CoordinateLieBracket (p286CoordinateEquiv (sourceColorP286Generator first))
        (p286CoordinateEquiv (sourceColorP286Generator second)) =
      p286CoordinateEquiv (p286LieBracket (sourceColorP286Generator first)
        (sourceColorP286Generator second)) := by simp [p286CoordinateLieBracket]
  funext triple
  fin_cases triple <;>
    simp [pointwiseP286GaugeTwoFormExteriorCovariantDerivative,
      pointwiseP286GaugeTwoFormCovariantDerivative, orderedP286GaugeTwoFormComponent,
      p286GaugeTwoFormAdjoint, gaugePotential, threeFormFirst, threeFormSecond, threeFormThird,
      orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond, Fin.sum_univ_six,
      electricCoordinates, magneticCoordinates, map_smul,
      p286CoordinateLieBracket_smul_left, p286CoordinateLieBracket_smul_right,
      bracket, sourceColorP286Generator_bracket, smul_smul]
  all_goals module

theorem Solution.gauge_euler_zero {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0 flow.configuration point = 0 := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [flow.charged_three_form point inside]
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
  have value : holonomicP286GaugeAuxiliaryCoordinate flow.configuration point =
      gaugeAuxiliaryCoordinates (flow.pointState point) := by
    change (fun pair => p286CoordinateEquiv (flow.configuration.gaugeAuxiliary point pair)) = _
    rw [flow.gauge_auxiliary point inside, gaugeAuxiliary_coordinates]
  have derivative : p286GaugeAuxiliaryDirectionalDerivative flow.configuration point =
      gaugeAuxiliaryJet (flow.pointState point) := funext (flow.gauge_auxiliary_derivative point inside)
  rw [value, derivative]
  change pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    (fun mu => p286CoordinateEquiv (gaugePotential (flow.pointState point 2) mu))
      (gaugeAuxiliaryCoordinates (flow.pointState point)) (gaugeAuxiliaryJet (flow.pointState point)) + _ = 0
  unfold gaugeAuxiliaryCoordinates gaugeAuxiliaryJet
  rw [triadExterior]
  have force : generator (flow.pointState point) 3 / sourceCoupling +
      2 * flow.pointState point 2 * electricAmplitude (flow.pointState point) =
      4*clock (flow.pointState point)*spinScale/(flow.pointState point 0) := by
    have balance := gauge_zero (flow.pointState point) (flow.admissible _ inside)
    unfold electricAmplitude
    have product : 2 * flow.pointState point 2 *
        (flow.pointState point 0 * (flow.pointState point 2)^2 /
          (sourceCoupling * clock (flow.pointState point))) =
        2 * flow.pointState point 0 * (flow.pointState point 2)^3 /
          (sourceCoupling * clock (flow.pointState point)) := by ring
    rw [product]
    exact sub_eq_zero.mp balance
  rw [force]
  have factor : clock (flow.pointState point)/(lapse*flow.pointState point 0) *
      (4*lapse*spinScale) = 4*clock (flow.pointState point)*spinScale/(flow.pointState point 0) := by
    field_simp [ne_of_gt lapse_pos]
  funext triple
  fin_cases triple <;> simp [chargedThreeForm, smul_smul, factor]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
