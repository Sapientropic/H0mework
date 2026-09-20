import H0mework.Physics.Gauge.ConnectionSectorSourceBalance

/-!
# S9-C3h75: fixed-background P286 affine-response fiber

This checkpoint changes only the primitive P286 connection by a
constant coordinate one-form.  It studies the actual pointwise P286
Euler--Lagrange coefficient as a function of that displacement.

The intended result is only a fixed-background, fixed-point response
classifier.  It is not a holonomic source producer, local solution germ,
stationarity theorem, or branch selector.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineP286FixedBackgroundAffineResponseFiber

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineBlockwiseConstitutive
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineConnectionSectorSourceBalance
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Gauge-only constant displacement -/

/-- Install a constant P286 coordinate one-form displacement.  Every
primitive field other than `gaugeConnection` is retained definitionally. -/
def installConstantP286ConnectionShift
    (configuration : StageNineHolonomicConfiguration)
    (shift : P286GaugeOneForm) : StageNineHolonomicConfiguration :=
  varyP286GaugeConnectionCoordinate configuration (fun _ => shift) 1

@[simp] theorem installConstantP286ConnectionShift_zero
    (configuration : StageNineHolonomicConfiguration) :
    installConstantP286ConnectionShift configuration 0 = configuration := by
  cases configuration
  simp [installConstantP286ConnectionShift,
    varyP286GaugeConnectionCoordinate,
    holonomicP286GaugeConnectionCoordinate]

@[simp] theorem installConstantP286ConnectionShift_coframe
    (configuration : StageNineHolonomicConfiguration)
    (shift : P286GaugeOneForm) :
    (installConstantP286ConnectionShift configuration shift).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem installConstantP286ConnectionShift_gaugeAuxiliary
    (configuration : StageNineHolonomicConfiguration)
    (shift : P286GaugeOneForm) :
    (installConstantP286ConnectionShift configuration shift).gaugeAuxiliary =
      configuration.gaugeAuxiliary :=
  rfl

@[simp] theorem installConstantP286ConnectionShift_scalar
    (configuration : StageNineHolonomicConfiguration)
    (shift : P286GaugeOneForm) :
    (installConstantP286ConnectionShift configuration shift).scalar =
      configuration.scalar :=
  rfl

@[simp] theorem installConstantP286ConnectionShift_matter
    (configuration : StageNineHolonomicConfiguration)
    (shift : P286GaugeOneForm) :
    (installConstantP286ConnectionShift configuration shift).matter =
      configuration.matter :=
  rfl

@[simp] theorem installConstantP286ConnectionShift_conjugateMatter
    (configuration : StageNineHolonomicConfiguration)
    (shift : P286GaugeOneForm) :
    (installConstantP286ConnectionShift configuration shift).conjugateMatter =
      configuration.conjugateMatter :=
  rfl

theorem holonomicP286GaugeConnectionCoordinate_installConstantShift
    (configuration : StageNineHolonomicConfiguration)
    (shift : P286GaugeOneForm) (point : BasePoint) :
    holonomicP286GaugeConnectionCoordinate
        (installConstantP286ConnectionShift configuration shift) point =
      holonomicP286GaugeConnectionCoordinate configuration point + shift := by
  simp [installConstantP286ConnectionShift]

/-! ## Exact sector dependence on the displacement -/

/-- The cross-bracket by which a background displacement changes the
algebraic curvature variation `D_A direction`. -/
def p286ConnectionShiftBracketResponse
    (shift direction : P286GaugeOneForm) : P286GaugeTwoForm :=
  fun pair =>
    p286CoordinateLieBracket (direction (pairFirst pair))
        (shift (pairSecond pair)) +
      p286CoordinateLieBracket (shift (pairFirst pair))
        (direction (pairSecond pair))

theorem p286ConnectionShiftBracketResponse_add
    (first second direction : P286GaugeOneForm) :
    p286ConnectionShiftBracketResponse (first + second) direction =
      p286ConnectionShiftBracketResponse first direction +
        p286ConnectionShiftBracketResponse second direction := by
  funext pair
  unfold p286ConnectionShiftBracketResponse
  simp only [Pi.add_apply, p286CoordinateLieBracket_add_left,
    p286CoordinateLieBracket_add_right]
  abel

theorem p286ConnectionShiftBracketResponse_smul
    (parameter : ℝ) (shift direction : P286GaugeOneForm) :
    p286ConnectionShiftBracketResponse (parameter • shift) direction =
      parameter • p286ConnectionShiftBracketResponse shift direction := by
  funext pair
  unfold p286ConnectionShiftBracketResponse
  simp only [Pi.smul_apply, p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_smul_right]
  module

theorem p286GaugeConnectionAlgebraicCurvatureDirection_installConstantShift
    (configuration : StageNineHolonomicConfiguration)
    (shift direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionAlgebraicCurvatureDirection
        (installConstantP286ConnectionShift configuration shift)
        direction point =
      p286GaugeConnectionAlgebraicCurvatureDirection configuration direction
          point +
        p286ConnectionShiftBracketResponse shift direction := by
  funext pair
  unfold p286GaugeConnectionAlgebraicCurvatureDirection
    p286GaugeConnectionAlgebraicCurvatureVariation
    p286ConnectionShiftBracketResponse
  rw [holonomicP286GaugeConnectionCoordinate_installConstantShift]
  simp only [Pi.add_apply, p286CoordinateLieBracket_add_left,
    p286CoordinateLieBracket_add_right]
  abel

/-- Actual BF cross-bracket contribution to the connection response. -/
def p286GaugeBFShiftCoefficient
    (configuration : StageNineHolonomicConfiguration)
    (shift direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    p286GaugeBFCurvatureIncrementDensity
      (configuration.coframe point)
      (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
      (holonomicP286GaugeAuxiliaryCoordinate configuration point)
      (p286ConnectionShiftBracketResponse shift direction)

theorem p286GaugeBFShiftCoefficient_add
    (configuration : StageNineHolonomicConfiguration)
    (first second direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeBFShiftCoefficient configuration (first + second) direction point =
      p286GaugeBFShiftCoefficient configuration first direction point +
        p286GaugeBFShiftCoefficient configuration second direction point := by
  unfold p286GaugeBFShiftCoefficient
  rw [p286ConnectionShiftBracketResponse_add,
    p286GaugeBFCurvatureIncrementDensity_add]
  ring

theorem p286GaugeBFShiftCoefficient_smul
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ) (shift direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeBFShiftCoefficient configuration (parameter • shift) direction
        point =
      parameter *
        p286GaugeBFShiftCoefficient configuration shift direction point := by
  unfold p286GaugeBFShiftCoefficient
  rw [p286ConnectionShiftBracketResponse_smul,
    p286GaugeBFCurvatureIncrementDensity_smul]
  ring

theorem p286GaugeBFAlgebraicCoefficient_installConstantShift
    (configuration : StageNineHolonomicConfiguration)
    (shift direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeBFAlgebraicCoefficient
        (installConstantP286ConnectionShift configuration shift)
        direction point =
      p286GaugeBFAlgebraicCoefficient configuration direction point +
        p286GaugeBFShiftCoefficient configuration shift direction point := by
  have volumeEq :
      generatedVolumeDensity
          (toContinuumPointField
            (installConstantP286ConnectionShift configuration shift) point) =
        generatedVolumeDensity
          (toContinuumPointField configuration point) := by
    rfl
  have auxiliaryEq :
      holonomicP286GaugeAuxiliaryCoordinate
          (installConstantP286ConnectionShift configuration shift) point =
        holonomicP286GaugeAuxiliaryCoordinate configuration point := by
    rfl
  have coframeEq :
      (installConstantP286ConnectionShift configuration shift).coframe point =
        configuration.coframe point := by
    rfl
  unfold p286GaugeBFAlgebraicCoefficient p286GaugeBFShiftCoefficient
  rw [volumeEq, auxiliaryEq, coframeEq,
    p286GaugeConnectionAlgebraicCurvatureDirection_installConstantShift,
    p286GaugeBFCurvatureIncrementDensity_add]
  ring

theorem p286GaugeConnectionBFDifferentialMomentumDivergence_installConstantShift
    (configuration : StageNineHolonomicConfiguration)
    (shift direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        (installConstantP286ConnectionShift configuration shift)
        direction point =
      p286GaugeConnectionBFDifferentialMomentumDivergence configuration
        direction point := by
  rfl

theorem p286MatterCurrentCoefficient_installConstantShift
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (shift direction : P286GaugeOneForm) (point : BasePoint) :
    p286MatterCurrentCoefficient source
        (installConstantP286ConnectionShift configuration shift)
        direction point =
      p286MatterCurrentCoefficient source configuration direction point := by
  rfl

/-- The scalar covariant-derivative displacement generated by the same
primitive connection shift. -/
def p286ScalarCovariantDerivativeShift
    (configuration : StageNineHolonomicConfiguration)
    (shift : P286GaugeOneForm) (point : BasePoint) :
    LorentzianIndex → ScalarCoordinateCarrier :=
  holonomicScalarGaugeConnectionVariation configuration
    (fun _ => shift) point

theorem p286ScalarCovariantDerivativeShift_add
    (configuration : StageNineHolonomicConfiguration)
    (first second : P286GaugeOneForm) (point : BasePoint) :
    p286ScalarCovariantDerivativeShift configuration (first + second) point =
      p286ScalarCovariantDerivativeShift configuration first point +
        p286ScalarCovariantDerivativeShift configuration second point := by
  funext direction
  unfold p286ScalarCovariantDerivativeShift
    holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [Pi.add_apply, map_add, p286LieBlockEmbed_add,
    scalarMotherLieAction_add]

theorem p286ScalarCovariantDerivativeShift_smul
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ) (shift : P286GaugeOneForm) (point : BasePoint) :
    p286ScalarCovariantDerivativeShift configuration (parameter • shift)
        point =
      parameter •
        p286ScalarCovariantDerivativeShift configuration shift point := by
  funext direction
  unfold p286ScalarCovariantDerivativeShift
    holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  simp only [Pi.smul_apply, map_smul, p286LieBlockEmbed_real_smul,
    scalarMotherLieAction_real_smul]

theorem holonomicScalarCovariantDerivative_installConstantShift
    (configuration : StageNineHolonomicConfiguration)
    (shift : P286GaugeOneForm) (point : BasePoint) :
    holonomicScalarCovariantDerivative
        (installConstantP286ConnectionShift configuration shift) point =
      holonomicScalarCovariantDerivative configuration point +
        p286ScalarCovariantDerivativeShift configuration shift point := by
  funext direction
  simpa [installConstantP286ConnectionShift,
    p286ScalarCovariantDerivativeShift] using
    holonomicScalarCovariantDerivative_gaugeConnection_expansion
      configuration (fun _ => shift) 1 point direction

theorem weightedDoubleSum_cross_split
    {First Second : Type*} [Fintype First] [Fintype Second]
    (weight baseLeft shiftLeft baseRight shiftRight : First → Second → ℝ) :
    (∑ first : First, ∑ second : Second,
      weight first second *
        ((baseLeft first second + shiftLeft first second) +
          (baseRight first second + shiftRight first second))) =
      (∑ first : First, ∑ second : Second,
        weight first second *
          (baseLeft first second + baseRight first second)) +
      ∑ first : First, ∑ second : Second,
        weight first second *
          (shiftLeft first second + shiftRight first second) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro first _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro second _
  ring

/-- Mixed scalar-current term generated when the background covariant
derivative changes by `shift`, while the connection test direction is held
fixed. -/
def p286ScalarCurrentShiftCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (shift direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    ((1 / 2 : ℝ) *
      ∑ first : LorentzianIndex,
        ∑ second : LorentzianIndex,
          ((lorentzianMetricOfCoframe (configuration.coframe point))⁻¹
              first second) *
            (scalarCoordinatePairingRe
                (scalarFrameRelativeCovariantDerivative source 0 point
                  (holonomicScalarGaugeConnectionVariation configuration
                    (fun _ => direction) point) first)
                (scalarFrameRelativeCovariantDerivative source 0 point
                  (p286ScalarCovariantDerivativeShift configuration shift
                    point) second) +
              scalarCoordinatePairingRe
                (scalarFrameRelativeCovariantDerivative source 0 point
                  (p286ScalarCovariantDerivativeShift configuration shift
                    point) first)
                (scalarFrameRelativeCovariantDerivative source 0 point
                  (holonomicScalarGaugeConnectionVariation configuration
                    (fun _ => direction) point) second)))

theorem p286ScalarCurrentShiftCoefficient_add
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (first second direction : P286GaugeOneForm) (point : BasePoint) :
    p286ScalarCurrentShiftCoefficient source configuration (first + second)
        direction point =
      p286ScalarCurrentShiftCoefficient source configuration first direction
          point +
        p286ScalarCurrentShiftCoefficient source configuration second direction
          point := by
  unfold p286ScalarCurrentShiftCoefficient
  rw [p286ScalarCovariantDerivativeShift_add]
  simp only [scalarFrameRelativeCovariantDerivative_add, Pi.add_apply,
    scalarCoordinatePairingRe_add_left,
    scalarCoordinatePairingRe_add_right]
  simp_rw [← Matrix.of_symm_apply]
  rw [weightedDoubleSum_cross_split]
  ring

theorem p286ScalarCurrentShiftCoefficient_smul
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (parameter : ℝ) (shift direction : P286GaugeOneForm) (point : BasePoint) :
    p286ScalarCurrentShiftCoefficient source configuration (parameter • shift)
        direction point =
      parameter *
        p286ScalarCurrentShiftCoefficient source configuration shift direction
          point := by
  unfold p286ScalarCurrentShiftCoefficient
  rw [p286ScalarCovariantDerivativeShift_smul]
  simp only [scalarFrameRelativeCovariantDerivative_real_smul, Pi.smul_apply,
    scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  simp_rw [← Matrix.of_symm_apply]
  rw [weightedDoubleSum_real_linear]
  ring

theorem p286ScalarCurrentCoefficient_installConstantShift
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (shift direction : P286GaugeOneForm) (point : BasePoint) :
    p286ScalarCurrentCoefficient source
        (installConstantP286ConnectionShift configuration shift)
        direction point =
      p286ScalarCurrentCoefficient source configuration direction point +
        p286ScalarCurrentShiftCoefficient source configuration shift direction
          point := by
  have volumeEq :
      generatedVolumeDensity
          (toContinuumPointField
            (installConstantP286ConnectionShift configuration shift) point) =
        generatedVolumeDensity
          (toContinuumPointField configuration point) := by
    rfl
  have variationEq :
      holonomicScalarGaugeConnectionVariation
          (installConstantP286ConnectionShift configuration shift)
          (fun _ => direction) point =
        holonomicScalarGaugeConnectionVariation configuration
          (fun _ => direction) point := by
    rfl
  have coframeEq :
      (installConstantP286ConnectionShift configuration shift).coframe point =
        configuration.coframe point := by
    rfl
  unfold p286ScalarCurrentCoefficient p286ScalarCurrentShiftCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
  rw [volumeEq, variationEq]
  simp only [toContinuumPointField]
  rw [coframeEq,
    holonomicScalarCovariantDerivative_installConstantShift]
  simp only [
    scalarFrameRelativeCovariantDerivative_add,
    Pi.add_apply,
    scalarCoordinatePairingRe_add_left,
    scalarCoordinatePairingRe_add_right]
  simp_rw [← Matrix.of_symm_apply]
  rw [weightedDoubleSum_cross_split]
  ring

/-! ## Actual response and its displacement readout -/

abbrev P286PointwiseResidual := P286GaugeOneForm → ℝ

def fixedBackgroundP286Response
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (shift : P286GaugeOneForm) : P286PointwiseResidual :=
  fun direction =>
    p286GaugeConnectionEulerLagrangeCoefficient source
      (installConstantP286ConnectionShift configuration shift) direction point

def fixedBackgroundP286LinearDisplacement
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (shift : P286GaugeOneForm) : P286PointwiseResidual :=
  fixedBackgroundP286Response source configuration point shift -
    fixedBackgroundP286Response source configuration point 0

/-- The exact connection-dependent linear part.  Its first summand is the BF
cross bracket; its second is the scalar current's dependence on `D_A scalar`.
The BF divergence and exterior-matter current do not occur here. -/
def fixedBackgroundP286SectorLinearResponse
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (shift : P286GaugeOneForm) : P286PointwiseResidual :=
  fun direction =>
    p286GaugeBFShiftCoefficient configuration shift direction point +
      p286ScalarCurrentShiftCoefficient source configuration shift direction
        point

theorem fixedBackgroundP286SectorLinearResponse_add
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (first second : P286GaugeOneForm) :
    fixedBackgroundP286SectorLinearResponse source configuration point
        (first + second) =
      fixedBackgroundP286SectorLinearResponse source configuration point first +
        fixedBackgroundP286SectorLinearResponse source configuration point
          second := by
  funext direction
  unfold fixedBackgroundP286SectorLinearResponse
  simp only [Pi.add_apply]
  rw [p286GaugeBFShiftCoefficient_add,
    p286ScalarCurrentShiftCoefficient_add]
  ring

theorem fixedBackgroundP286SectorLinearResponse_smul
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (parameter : ℝ) (shift : P286GaugeOneForm) :
    fixedBackgroundP286SectorLinearResponse source configuration point
        (parameter • shift) =
      parameter •
        fixedBackgroundP286SectorLinearResponse source configuration point
          shift := by
  funext direction
  unfold fixedBackgroundP286SectorLinearResponse
  change
    p286GaugeBFShiftCoefficient configuration (parameter • shift) direction
          point +
        p286ScalarCurrentShiftCoefficient source configuration
          (parameter • shift) direction point =
      parameter *
        (p286GaugeBFShiftCoefficient configuration shift direction point +
          p286ScalarCurrentShiftCoefficient source configuration shift direction
            point)
  rw [p286GaugeBFShiftCoefficient_smul,
    p286ScalarCurrentShiftCoefficient_smul]
  ring

/-- Linear operator underlying the actual affine response. -/
def fixedBackgroundP286LinearResponseMap
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    P286GaugeOneForm →ₗ[ℝ] P286PointwiseResidual where
  toFun := fixedBackgroundP286SectorLinearResponse source configuration point
  map_add' :=
    fixedBackgroundP286SectorLinearResponse_add source configuration point
  map_smul' := by
    intro parameter shift
    exact fixedBackgroundP286SectorLinearResponse_smul source configuration
      point parameter shift

@[simp] theorem fixedBackgroundP286LinearResponseMap_apply
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (shift : P286GaugeOneForm) :
    fixedBackgroundP286LinearResponseMap source configuration point shift =
      fixedBackgroundP286SectorLinearResponse source configuration point
        shift :=
  rfl

theorem fixedBackgroundP286Offset_apply_eq_sectors
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : P286GaugeOneForm) :
    fixedBackgroundP286Response source configuration point 0 direction =
      p286GaugeBFAlgebraicCoefficient configuration direction point -
        p286GaugeConnectionBFDifferentialMomentumDivergence configuration
          direction point +
        p286ScalarCurrentCoefficient source configuration direction point +
        p286MatterCurrentCoefficient source configuration direction point := by
  simp only [fixedBackgroundP286Response,
    installConstantP286ConnectionShift_zero]
  rw [p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance]
  unfold p286GaugeBFBalanceCoefficient
  ring

/-- The scalar-current term in the offset reads the actual background
covariant derivative; its first summand is the primitive scalar derivative,
not a supplied current or derivative receipt. -/
theorem fixedBackgroundP286Offset_scalarDerivative_eq_primitive_add_connection
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex) :
    (toContinuumPointField configuration point).scalarCovariantDerivative
        direction =
      fieldDirectionalDerivative configuration.scalar point direction +
        scalarMotherLieAction
          (p286LieBlockEmbed
            (configuration.gaugeConnection point direction))
          (configuration.scalar point) :=
  rfl

theorem fixedBackgroundP286Response_apply_affine
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (shift direction : P286GaugeOneForm) :
    fixedBackgroundP286Response source configuration point shift direction =
      fixedBackgroundP286SectorLinearResponse source configuration point shift
          direction +
        fixedBackgroundP286Response source configuration point 0 direction := by
  unfold fixedBackgroundP286Response
    fixedBackgroundP286SectorLinearResponse
  rw [p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance,
    p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance]
  unfold p286GaugeBFBalanceCoefficient
  rw [
    p286GaugeBFAlgebraicCoefficient_installConstantShift,
    p286GaugeConnectionBFDifferentialMomentumDivergence_installConstantShift,
    p286ScalarCurrentCoefficient_installConstantShift,
    p286MatterCurrentCoefficient_installConstantShift]
  simp only [installConstantP286ConnectionShift_zero]
  ring

theorem fixedBackgroundP286Response_affine
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (shift : P286GaugeOneForm) :
    fixedBackgroundP286Response source configuration point shift =
      fixedBackgroundP286SectorLinearResponse source configuration point shift +
        fixedBackgroundP286Response source configuration point 0 := by
  funext direction
  exact fixedBackgroundP286Response_apply_affine source configuration point
    shift direction

@[simp] theorem fixedBackgroundP286LinearDisplacement_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    fixedBackgroundP286LinearDisplacement source configuration point 0 = 0 := by
  funext direction
  simp [fixedBackgroundP286LinearDisplacement]

theorem fixedBackgroundP286Response_eq_displacement_add_offset
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (shift : P286GaugeOneForm) :
    fixedBackgroundP286Response source configuration point shift =
      fixedBackgroundP286LinearDisplacement source configuration point shift +
        fixedBackgroundP286Response source configuration point 0 := by
  funext direction
  simp [fixedBackgroundP286LinearDisplacement]

theorem fixedBackgroundP286LinearDisplacement_eq_sectorLinearResponse
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (shift : P286GaugeOneForm) :
    fixedBackgroundP286LinearDisplacement source configuration point shift =
      fixedBackgroundP286SectorLinearResponse source configuration point
        shift := by
  funext direction
  unfold fixedBackgroundP286LinearDisplacement
  change
    fixedBackgroundP286Response source configuration point shift direction -
        fixedBackgroundP286Response source configuration point 0 direction =
      fixedBackgroundP286SectorLinearResponse source configuration point shift
        direction
  rw [fixedBackgroundP286Response_apply_affine]
  ring

theorem fixedBackgroundP286LinearDisplacement_add
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (first second : P286GaugeOneForm) :
    fixedBackgroundP286LinearDisplacement source configuration point
        (first + second) =
      fixedBackgroundP286LinearDisplacement source configuration point first +
        fixedBackgroundP286LinearDisplacement source configuration point
          second := by
  rw [fixedBackgroundP286LinearDisplacement_eq_sectorLinearResponse,
    fixedBackgroundP286LinearDisplacement_eq_sectorLinearResponse,
    fixedBackgroundP286LinearDisplacement_eq_sectorLinearResponse,
    fixedBackgroundP286SectorLinearResponse_add]

theorem fixedBackgroundP286LinearDisplacement_sub
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (first second : P286GaugeOneForm) :
    fixedBackgroundP286LinearDisplacement source configuration point
        (first - second) =
      fixedBackgroundP286LinearDisplacement source configuration point first -
        fixedBackgroundP286LinearDisplacement source configuration point
          second := by
  rw [fixedBackgroundP286LinearDisplacement_eq_sectorLinearResponse,
    fixedBackgroundP286LinearDisplacement_eq_sectorLinearResponse,
    fixedBackgroundP286LinearDisplacement_eq_sectorLinearResponse]
  exact map_sub
    (fixedBackgroundP286LinearResponseMap source configuration point)
    first second

/-! ## Zero fiber, range, kernel, and transported-response classifiers -/

def fixedBackgroundP286ZeroFiber
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Set P286GaugeOneForm :=
  { shift | fixedBackgroundP286Response source configuration point shift = 0 }

theorem fixedBackgroundP286ZeroFiber_mem_iff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (shift : P286GaugeOneForm) :
    shift ∈ fixedBackgroundP286ZeroFiber source configuration point ↔
      fixedBackgroundP286LinearResponseMap source configuration point shift =
        -fixedBackgroundP286Response source configuration point 0 := by
  change
    fixedBackgroundP286Response source configuration point shift = 0 ↔ _
  rw [fixedBackgroundP286Response_affine]
  change
    fixedBackgroundP286LinearResponseMap source configuration point shift +
        fixedBackgroundP286Response source configuration point 0 = 0 ↔ _
  constructor
  · intro responseZero
    exact eq_neg_of_add_eq_zero_left responseZero
  · intro linearEq
    rw [linearEq]
    exact neg_add_cancel _

theorem fixedBackgroundP286ZeroFiber_nonempty_iff_offset_mem_range
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (∃ shift, shift ∈
      fixedBackgroundP286ZeroFiber source configuration point) ↔
      -fixedBackgroundP286Response source configuration point 0 ∈
        LinearMap.range
          (fixedBackgroundP286LinearResponseMap source configuration point) := by
  constructor
  · rintro ⟨shift, zeroFiber⟩
    refine ⟨shift, ?_⟩
    exact (fixedBackgroundP286ZeroFiber_mem_iff source configuration point
      shift).1 zeroFiber
  · rintro ⟨shift, linearEq⟩
    refine ⟨shift, ?_⟩
    exact (fixedBackgroundP286ZeroFiber_mem_iff source configuration point
      shift).2 linearEq

theorem fixedBackgroundP286Response_eq_iff_sub_mem_kernel
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (first second : P286GaugeOneForm) :
    fixedBackgroundP286Response source configuration point first =
        fixedBackgroundP286Response source configuration point second ↔
      first - second ∈
        LinearMap.ker
          (fixedBackgroundP286LinearResponseMap source configuration point) := by
  have firstAffine := fixedBackgroundP286Response_affine source configuration
    point first
  have secondAffine := fixedBackgroundP286Response_affine source configuration
    point second
  rw [firstAffine, secondAffine]
  change
    fixedBackgroundP286LinearResponseMap source configuration point first +
          fixedBackgroundP286Response source configuration point 0 =
        fixedBackgroundP286LinearResponseMap source configuration point second +
          fixedBackgroundP286Response source configuration point 0 ↔
      fixedBackgroundP286LinearResponseMap source configuration point
          (first - second) = 0
  rw [map_sub]
  constructor
  · intro responseEq
    apply sub_eq_zero.mpr
    exact add_right_cancel responseEq
  · intro linearEq
    have equalLinear := sub_eq_zero.mp linearEq
    rw [equalLinear]

/-- Framework-facing range test.  It only characterizes existence of a
constant-shift endpoint.  It does not select one or claim that such a shift
extends to a holonomic stationary configuration. -/
theorem fixedBackgroundP286_transport_endpoint_exists_iff_range
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (k : ℝ) (initial : P286GaugeOneForm) :
    (∃ terminal : P286GaugeOneForm,
      fixedBackgroundP286Response source configuration point terminal =
        k • fixedBackgroundP286Response source configuration point initial) ↔
      k • fixedBackgroundP286Response source configuration point initial -
          fixedBackgroundP286Response source configuration point 0 ∈
        LinearMap.range
          (fixedBackgroundP286LinearResponseMap source configuration point) := by
  constructor
  · rintro ⟨terminal, transport⟩
    refine ⟨terminal, ?_⟩
    funext direction
    have pointTransport := congrFun transport direction
    have affine := fixedBackgroundP286Response_apply_affine source
      configuration point terminal direction
    change
      fixedBackgroundP286LinearResponseMap source configuration point terminal
          direction =
        k * fixedBackgroundP286Response source configuration point initial
            direction -
          fixedBackgroundP286Response source configuration point 0 direction
    change
      fixedBackgroundP286SectorLinearResponse source configuration point
          terminal direction = _
    change
      fixedBackgroundP286Response source configuration point terminal
            direction =
        k * fixedBackgroundP286Response source configuration point initial
          direction at pointTransport
    linarith
  · rintro ⟨terminal, rangeEq⟩
    refine ⟨terminal, ?_⟩
    funext direction
    have pointRange := congrFun rangeEq direction
    have affine := fixedBackgroundP286Response_apply_affine source
      configuration point terminal direction
    change
      fixedBackgroundP286LinearResponseMap source configuration point terminal
          direction =
        k * fixedBackgroundP286Response source configuration point initial
            direction -
          fixedBackgroundP286Response source configuration point 0 direction
      at pointRange
    change
      fixedBackgroundP286SectorLinearResponse source configuration point
          terminal direction = _ at pointRange
    change
      fixedBackgroundP286Response source configuration point terminal direction =
        k * fixedBackgroundP286Response source configuration point initial
          direction
    linarith

/-- Once an actual endpoint is supplied, its full displacement fiber is
classified by the kernel.  No witness is selected from a merely nonempty
fiber. -/
theorem fixedBackgroundP286_actualEndpoint_fiber_iff_kernel
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (endpoint candidate : P286GaugeOneForm) :
    fixedBackgroundP286Response source configuration point candidate =
        fixedBackgroundP286Response source configuration point endpoint ↔
      candidate - endpoint ∈
        LinearMap.ker
          (fixedBackgroundP286LinearResponseMap source configuration point) :=
  fixedBackgroundP286Response_eq_iff_sub_mem_kernel source configuration point
    candidate endpoint

end


end SaturationMonoid.PhysicsCore.StageNineP286FixedBackgroundAffineResponseFiber
