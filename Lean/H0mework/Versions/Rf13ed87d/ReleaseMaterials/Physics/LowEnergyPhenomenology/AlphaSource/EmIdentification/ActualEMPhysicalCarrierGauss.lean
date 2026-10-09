import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCarrier
import H0mework.Versions.AB.Physics.MotherSource.CanonicalGauss.Poisson

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMPhysicalCarrier
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineCoframeLocalDifferentiability StageNineCanonicalCauchyState
open StageNineP286GaugeConnectionVariation StageNineDynamicBreakingVacuum
open StageNineFormNativeP286GaugeGeometricFirstVariation
open Stage9C.Material.SpinPair Stage10 TemporalGauge CanonicalGauss
open PhysicalEMGaugeRealization ActualEMCarrierOwn
open scoped BigOperators ContDiff

attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source
local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def directionalPotential (a : P286LieBlockData) (V : BasePoint → ℝ) : Potential :=
  fun x => V x • a

def backgroundAdjoint (a : P286LieBlockData) (i : Fin 3) : P286LieBlockData :=
  p286LieBracket (gaugeScale • sourceColorP286Generator i) a

private theorem directional_regular (a : P286LieBlockData) (V : BasePoint → ℝ)
    (hV : Differentiable ℝ V) : PotentialDifferentiable (directionalPotential a V) := by
  unfold PotentialDifferentiable directionalPotential
  simp only [map_smul]
  exact hV.smul_const _

private theorem directional_derivative (a : P286LieBlockData) (V : BasePoint → ℝ)
    (x : BasePoint) (hV : DifferentiableAt ℝ V x) (mu : LorentzianIndex) :
    derivative (directionalPotential a V) x mu = fieldDirectionalDerivative V x mu • a := by
  unfold derivative directionalPotential
  simp only [map_smul]
  unfold fieldDirectionalDerivative
  rw [fderiv_smul_const hV]
  simp

theorem directional_electric (a : P286LieBlockData) (V : BasePoint → ℝ)
    (x : BasePoint) (hV : DifferentiableAt ℝ V x) (i : Fin 3) :
    electric (directionalPotential a V) x i =
      (-fieldDirectionalDerivative V x i.succ) • a + (-V x) • backgroundAdjoint a i := by
  rw [electric, directional_derivative a V x hV]
  simp only [directionalPotential, p286LieBracket_smul_left]
  rw [StageNineP286BracketCalculus.p286LieBracket_skew a]
  simp only [backgroundAdjoint, smul_neg]
  module

private theorem directional_electric_regular (a : P286LieBlockData) (V : BasePoint → ℝ)
    (hV : ScalarRegular V) (x : BasePoint) :
    ElectricDifferentiableAt (directionalPotential a V) x := by
  intro i
  simp only [directional_electric a V _ (hV.1 _), map_add, map_smul]
  exact (((hV.2 i x).neg).smul_const _).add (((hV.1 x).neg).smul_const _)

private theorem electric_derivative (a : P286LieBlockData) (V : BasePoint → ℝ)
    (hV : ScalarRegular V) (x : BasePoint) (i : Fin 3) :
    derivative (fun p => electric (directionalPotential a V) p i) x i.succ =
      (-fieldDirectionalDerivative (fun p => fieldDirectionalDerivative V p i.succ) x i.succ) • a +
      (-fieldDirectionalDerivative V x i.succ) • backgroundAdjoint a i := by
  unfold derivative
  simp only [directional_electric a V _ (hV.1 _), map_add, map_smul]
  change p286CoordinateEquiv.symm
    ((fderiv ℝ (fun p => (-fieldDirectionalDerivative V p i.succ) • p286CoordinateEquiv a +
      (-V p) • p286CoordinateEquiv (backgroundAdjoint a i)) x) (coordinateDirection i.succ)) = _
  have h1 : DifferentiableAt ℝ (fun p : BasePoint =>
      (-fieldDirectionalDerivative V p i.succ) • p286CoordinateEquiv a) x :=
    ((hV.2 i x).neg).smul_const _
  have h2 : DifferentiableAt ℝ (fun p : BasePoint =>
      (-V p) • p286CoordinateEquiv (backgroundAdjoint a i)) x := (hV.1 x).neg.smul_const _
  rw [fderiv_fun_add h1 h2,
    fderiv_smul_const (c := fun p => -fieldDirectionalDerivative V p i.succ)
      ((hV.2 i x).neg) (p286CoordinateEquiv a),
    fderiv_smul_const (c := fun p => -V p) ((hV.1 x).neg)
      (p286CoordinateEquiv (backgroundAdjoint a i)),
    fderiv_fun_neg, fderiv_fun_neg]
  simp [fieldDirectionalDerivative]
  module

/-- The complete original covariant Gauss operator; all mixing rows remain present. -/
theorem directional_divergence (a : P286LieBlockData) (V : BasePoint → ℝ)
    (hV : ScalarRegular V) (x : BasePoint) :
    divergence (directionalPotential a V) x =
      (-spatialLaplacian V x) • a +
      ∑ i : Fin 3, ((-2*fieldDirectionalDerivative V x i.succ) • backgroundAdjoint a i +
        (-V x) • backgroundAdjoint (backgroundAdjoint a i) i) := by
  unfold divergence
  simp_rw [electric_derivative a V hV]
  simp only [directional_electric a V _ (hV.1 _),
    p286LieBracket_add_right, p286LieBracket_smul_right]
  have term (i : Fin 3) :
      (-fieldDirectionalDerivative (fun p => fieldDirectionalDerivative V p i.succ) x i.succ) • a +
      (-fieldDirectionalDerivative V x i.succ) • backgroundAdjoint a i +
      ((-fieldDirectionalDerivative V x i.succ) •
        p286LieBracket (gaugeScale • sourceColorP286Generator i) a +
        (-V x) • p286LieBracket (gaugeScale • sourceColorP286Generator i) (backgroundAdjoint a i)) =
      (-fieldDirectionalDerivative (fun p => fieldDirectionalDerivative V p i.succ) x i.succ) • a +
      ((-2*fieldDirectionalDerivative V x i.succ) • backgroundAdjoint a i +
        (-V x) • backgroundAdjoint (backgroundAdjoint a i) i) := by
    simp only [backgroundAdjoint]
    module
  simp only [term, Finset.sum_add_distrib]
  rw [← Finset.sum_smul, Finset.sum_neg_distrib]
  rfl

def emPotential (V : BasePoint → ℝ) : Potential := directionalPotential emDirection V

/-- One Cauchy event carries the literal EM potential, the generated scalar jet and independent matter. -/
def emCauchyField (V : BasePoint → ℝ) (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) : StageNineHolonomicConfiguration :=
  CanonicalGauss.withMatter (emPotential V) matter dual

private theorem em_background (i : Fin 3) :
    backgroundAdjoint emDirection i =
      (![ -gaugeScale • sourceColorP286Generator 1,
        gaugeScale • sourceColorP286Generator 0, 0] : Fin 3 → P286LieBlockData) i := by
  have paid := congrFun (em_actual_background_derivative 0) i.succ
  fin_cases i <;> exact paid

private theorem em_background_second (i : Fin 3) :
    backgroundAdjoint (backgroundAdjoint emDirection i) i =
      (![gaugeScale^2 • sourceColorP286Generator 2,
        gaugeScale^2 • sourceColorP286Generator 2, 0] : Fin 3 → P286LieBlockData) i := by
  rw [em_background]
  fin_cases i <;>
    simp [backgroundAdjoint, p286LieBracket_smul_left, p286LieBracket_smul_right,
      sourceColorP286Generator_bracket, bracket_zero_right, smul_smul, pow_two, smul_neg]
  module

theorem em_cauchy_electric (V : BasePoint → ℝ) (x : BasePoint)
    (hV : DifferentiableAt ℝ V x) :
    electric (emPotential V) x =
      ![(-fieldDirectionalDerivative V x 1) • emDirection +
          (gaugeScale*V x) • sourceColorP286Generator 1,
        (-fieldDirectionalDerivative V x 2) • emDirection +
          (-gaugeScale*V x) • sourceColorP286Generator 0,
        (-fieldDirectionalDerivative V x 3) • emDirection] := by
  funext i
  rw [emPotential, directional_electric emDirection V x hV, em_background]
  fin_cases i <;> simp [smul_smul] <;> module

theorem em_cauchy_divergence (V : BasePoint → ℝ) (hV : ScalarRegular V) (x : BasePoint) :
    divergence (emPotential V) x =
      (-spatialLaplacian V x) • emDirection +
      (2*gaugeScale*fieldDirectionalDerivative V x 1) • sourceColorP286Generator 1 +
      (-2*gaugeScale*fieldDirectionalDerivative V x 2) • sourceColorP286Generator 0 +
      (-2*gaugeScale^2*V x) • sourceColorP286Generator 2 := by
  rw [emPotential, directional_divergence emDirection V hV]
  simp_rw [em_background_second]
  simp_rw [em_background]
  rw [Fin.sum_univ_three]
  change (-spatialLaplacian V x) • emDirection +
    (((-2*fieldDirectionalDerivative V x 1) • (-gaugeScale • sourceColorP286Generator 1) +
      (-V x) • (gaugeScale^2 • sourceColorP286Generator 2)) +
     ((-2*fieldDirectionalDerivative V x 2) • (gaugeScale • sourceColorP286Generator 0) +
      (-V x) • (gaugeScale^2 • sourceColorP286Generator 2)) +
     ((-2*fieldDirectionalDerivative V x 3) • (0 : P286LieBlockData) + (-V x) • 0)) = _
  simp only [smul_zero, add_zero]
  module

theorem em_cauchy_scalar (V : BasePoint → ℝ)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (x : BasePoint) :
    (emCauchyField V matter dual).scalar x =
      sourceGeneratedVacuumCoordinates Stage10.Runtime.source +
      canonicalTimeProjection x • (-scalarCharge
        (emPotential V (canonicalCauchySlicePoint 0 (canonicalSpatialProjection x)))) :=
  CanonicalGauss.scalar_field (emPotential V) x

theorem em_cauchy_scalar_time_zero (V : BasePoint → ℝ) (hV : Differentiable ℝ V)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (x : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative (emCauchyField V matter dual)
      (canonicalCauchySlicePoint 0 x) 0 = 0 :=
  CanonicalGauss.covariant_time_zero (emPotential V) (directional_regular emDirection V hV) x

theorem em_cauchy_auxiliary (V : BasePoint → ℝ)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (x : BasePoint) :
    (emCauchyField V matter dual).gaugeAuxiliary x =
      TemporalGauge.field (fun i => -(2*lapse⁻¹) • magnetic i)
        (fun i => (2*lapse) • electric (emPotential V) x i) :=
  TemporalGauge.auxiliary_value (emPotential V) x

/-- Every original gauge test observes the same full Cauchy event and its unchanged dual current. -/
theorem em_cauchy_gauss (V : BasePoint → ℝ) (hV : ScalarRegular V)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (x : StageNineSpatialPoint)
    (a : P286LieBlockData) :
    p286CoordinateLiePairing (p286CoordinateEquiv a)
      (holonomicFormNativeP286GaugeEulerThreeForm Stage10.Runtime.source 0
        (emCauchyField V matter dual) (canonicalCauchySlicePoint 0 x) 3) =
      2*lapse*p286LiePairing a
        ((-spatialLaplacian V (canonicalCauchySlicePoint 0 x)) • emDirection +
        (2*gaugeScale*fieldDirectionalDerivative V (canonicalCauchySlicePoint 0 x) 1) • sourceColorP286Generator 1 +
        (-2*gaugeScale*fieldDirectionalDerivative V (canonicalCauchySlicePoint 0 x) 2) • sourceColorP286Generator 0 +
        (-2*gaugeScale^2*V (canonicalCauchySlicePoint 0 x)) • sourceColorP286Generator 2) +
      (dual (canonicalCauchySlicePoint 0 x) (Stage9DEF.Compatibility.currentAction 0 a
        (matter (canonicalCauchySlicePoint 0 x)))).re := by
  have paid := CanonicalGauss.gauss_projection (emPotential V)
    (directional_regular emDirection V hV.1) matter dual x
    (directional_electric_regular emDirection V hV _) a
  rw [em_cauchy_divergence V hV] at paid
  exact paid

end LowEnergy.GaussComposite.ActualEMPhysicalCarrier
