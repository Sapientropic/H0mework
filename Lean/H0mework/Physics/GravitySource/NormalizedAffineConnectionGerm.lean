import H0mework.Physics.GravitySource.ConnectionLiftNoGo
import H0mework.Physics.Geometry.GravityBianchi

/-!
# S9-C3g7c: normalized affine Lorentz-connection germ

For an arbitrary Lorentz-skew origin value `omega0` and an arbitrary target
physical bivector `target`, this file constructs an explicit affine connection
field whose actual `d omega + omega wedge omega` curvature at the origin is
`target`.

The affine derivative is not an independent receipt.  It is the canonical
antisymmetric derivative jet

`(target - [omega0, omega0]) / 2`.

The factor `1/2` is forced because antisymmetrization subtracts the reversed
derivative and hence doubles the chosen oriented coefficient.

The declared carrier fixes the symmetric first jet and every higher jet to
zero in the existing canonical BasePoint chart.  It is therefore a
subsingleton normalized local-germ class, exactly the restricted jurisdiction
needed after C3g7b.  This is not a claim that curvature globally determines a
connection, nor yet a proof that the normalization is gauge-natural or that a
full source-generated joint configuration exists.
Although the representative is written as a total affine field so Lean can
differentiate it, its present jurisdiction is the origin germ only; no raw
absolute-action integrability, boundary condition, or global extension is
claimed.
-/

namespace SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineLorentzConnectionVariation
open StageNineEnrichedProofFreeSource
open StageNineGlobalConnection
open StageNineGravityBianchi
open StageNinePositiveSourceGravityMouthTransportCurvature
open StageNinePositiveSourceGravityMouthConnectionLiftNoGo
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

/-- The actual quadratic bracket contribution of a prescribed connection
value at the origin, in the same lowered bivector coordinates used by
`holonomicGravityCurvature`. -/
def originLorentzBracketCurvature
    (omega0 : PointwiseLorentzSpinConnection) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    let internalOut := pairFirst internalPair
    let internalIn := pairSecond internalPair
    let first := pairFirst spacetimePair
    let second := pairSecond spacetimePair
    minkowskiInternalSign internalOut *
      ∑ middle : LorentzianIndex,
        (omega0 first internalOut middle *
            omega0 second middle internalIn -
          omega0 second internalOut middle *
            omega0 first middle internalIn)

/-- The uniquely normalized antisymmetric derivative coefficient after the
fixed origin bracket has been removed from the target curvature. -/
def normalizedDerivativeBivector
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) : PhysicalBivector :=
  (2 : ℝ)⁻¹ • (target - originLorentzBracketCurvature omega0)

/-- No constitutive coefficient was added: within the antisymmetric affine
right-inverse grammar, the coefficient is forced uniquely by the two oriented
derivative terms. -/
theorem antisymmetricAffineNormalizationCoefficient_iff
    (coefficient : ℝ) :
    2 * coefficient = 1 ↔ coefficient = (2 : ℝ)⁻¹ := by
  constructor <;> intro equality <;> norm_num at equality ⊢ <;> linarith

/-- Continuous coordinate projection on the Euclidean base. -/
def baseCoordinate (direction : LorentzianIndex) : BasePoint →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj direction).comp
    (EuclideanSpace.equiv LorentzianIndex ℝ).toContinuousLinearMap

@[simp] theorem baseCoordinate_apply
    (direction : LorentzianIndex) (point : BasePoint) :
    baseCoordinate direction point = point direction :=
  rfl

@[simp] theorem baseCoordinate_coordinateDirection
    (first second : LorentzianIndex) :
    baseCoordinate first (coordinateDirection second) =
      if first = second then 1 else 0 := by
  fin_cases first <;> fin_cases second <;>
    simp [baseCoordinate, coordinateDirection]

/-- For fixed one-form and internal-bivector indices, the affine increment is
literally a continuous linear functional on the base point. -/
def normalizedAffineBivectorComponentLinear
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) : BasePoint →L[ℝ] ℝ :=
  ∑ spacetimePair : Fin 6,
    normalizedDerivativeBivector omega0 target internalPair spacetimePair •
      ∑ derivativeDirection : LorentzianIndex,
        orientedLorentzBivectorBasisCoefficient spacetimePair
            derivativeDirection formDirection •
          baseCoordinate derivativeDirection

/-- Explicit affine lower-bivector one-form.  The spacetime bivector basis is
used a second time to turn an antisymmetric two-form coefficient into the
linear one-form `A_nu(x) = (1/2) C_{mu nu} x^mu`. -/
def normalizedAffineBivectorOneForm
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (point : BasePoint) : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    normalizedAffineBivectorComponentLinear omega0 target formDirection
      internalPair point

/-- The normalized affine germ.  `target` is only a constructor argument; the
resulting primitive field contains a connection, not a stored curvature or a
curvature certificate. -/
def normalizedAffineLorentzConnectionField
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) : LorentzConnectionField :=
  fun point =>
    omega0 +
      lorentzSkewConnectionOfBivectorOneForm
        (normalizedAffineBivectorOneForm omega0 target point)

def SmoothLorentzConnectionField (connection : LorentzConnectionField) : Prop :=
  ∀ formDirection internalOut internalIn,
    ContDiff ℝ ∞ fun point =>
      connection point formDirection internalOut internalIn

@[simp] theorem normalizedAffineBivectorOneForm_zero
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) :
    normalizedAffineBivectorOneForm omega0 target 0 = 0 := by
  funext formDirection internalPair
  simp [normalizedAffineBivectorOneForm]

@[simp] theorem normalizedAffineLorentzConnectionField_zero
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) :
    normalizedAffineLorentzConnectionField omega0 target 0 = omega0 := by
  funext formDirection internalOut internalIn
  simp [normalizedAffineLorentzConnectionField]

theorem normalizedAffineLorentzConnectionField_smooth
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) :
    SmoothLorentzConnectionField
      (normalizedAffineLorentzConnectionField omega0 target) := by
  intro formDirection internalOut internalIn
  unfold normalizedAffineLorentzConnectionField
    lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
    normalizedAffineBivectorOneForm
  fun_prop

/-- Lorentz skewness is preserved pointwise: the affine increment is produced
by the existing six-coordinate Lorentz-skew lift. -/
theorem normalizedAffineLorentzConnectionField_lorentzSkew
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (originSkew : LorentzSkew omega0)
    (point : BasePoint) :
    LorentzSkew (normalizedAffineLorentzConnectionField omega0 target point) := by
  have incrementSkew :=
    lorentzSkewConnectionOfBivectorOneForm_lorentzSkew
      (normalizedAffineBivectorOneForm omega0 target point)
  intro formDirection
  have originAt := originSkew formDirection
  have incrementAt := incrementSkew formDirection
  rw [show spinConnectionMatrix
        (normalizedAffineLorentzConnectionField omega0 target point)
          formDirection =
      spinConnectionMatrix omega0 formDirection +
        spinConnectionMatrix
          (lorentzSkewConnectionOfBivectorOneForm
            (normalizedAffineBivectorOneForm omega0 target point))
          formDirection by
    ext internalOut internalIn
    rfl]
  rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
  calc
    (Matrix.transpose (spinConnectionMatrix omega0 formDirection) *
          minkowskiInternalMetric +
        Matrix.transpose
            (spinConnectionMatrix
              (lorentzSkewConnectionOfBivectorOneForm
                (normalizedAffineBivectorOneForm omega0 target point))
              formDirection) * minkowskiInternalMetric) +
      (minkowskiInternalMetric * spinConnectionMatrix omega0 formDirection +
        minkowskiInternalMetric *
          spinConnectionMatrix
            (lorentzSkewConnectionOfBivectorOneForm
              (normalizedAffineBivectorOneForm omega0 target point))
            formDirection) =
        (Matrix.transpose (spinConnectionMatrix omega0 formDirection) *
            minkowskiInternalMetric +
          minkowskiInternalMetric * spinConnectionMatrix omega0 formDirection) +
        (Matrix.transpose
              (spinConnectionMatrix
                (lorentzSkewConnectionOfBivectorOneForm
                  (normalizedAffineBivectorOneForm omega0 target point))
                formDirection) * minkowskiInternalMetric +
          minkowskiInternalMetric *
            spinConnectionMatrix
              (lorentzSkewConnectionOfBivectorOneForm
                (normalizedAffineBivectorOneForm omega0 target point))
              formDirection) := by abel
    _ = 0 := by rw [originAt, incrementAt, add_zero]

/-- Embed only the connection into the holonomic carrier so that the actual
curvature definition can be evaluated.  The other fields are irrelevant to
this local curvature readout and are fixed to zero in the probe. -/
def configurationOfLorentzConnection
    (connection : LorentzConnectionField) :
    StageNineHolonomicConfiguration where
  coframe := 0
  gravityConnection := connection
  gravityAuxiliary := 0
  gravitySimplicityMultiplier := 0
  gaugeConnection := 0
  gaugeAuxiliary := 0
  scalar := 0
  matter := 0
  conjugateMatter := 0

def normalizedAffineConfiguration
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) : StageNineHolonomicConfiguration :=
  configurationOfLorentzConnection
    (normalizedAffineLorentzConnectionField omega0 target)

/-- Coordinate derivative of the normalized lower-bivector one-form.  This
is the computational point where the affine formula exposes the oriented
`1/2` coefficient. -/
theorem normalizedAffineBivectorOneForm_directionalDerivative_zero
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          normalizedAffineBivectorOneForm omega0 target point
            formDirection internalPair)
        0 derivativeDirection =
      ∑ spacetimePair : Fin 6,
        normalizedDerivativeBivector omega0 target internalPair spacetimePair *
          orientedLorentzBivectorBasisCoefficient spacetimePair
            derivativeDirection formDirection := by
  unfold fieldDirectionalDerivative normalizedAffineBivectorOneForm
  rw [(normalizedAffineBivectorComponentLinear omega0 target formDirection
    internalPair).hasFDerivAt.fderiv]
  fin_cases derivativeDirection <;> fin_cases formDirection <;>
    simp [normalizedAffineBivectorComponentLinear,
      coordinateDirection, baseCoordinate,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, Fin.sum_univ_four, Fin.sum_univ_six]

/-- The normalized affine one-form has zero symmetric first jet.  Its
source-generated derivative is purely antisymmetric in the base derivative
and one-form directions. -/
theorem normalizedAffineBivectorOneForm_symmetricDerivative_zero
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (first second : LorentzianIndex) (internalPair : Fin 6) :
    fieldDirectionalDerivative
          (fun point =>
            normalizedAffineBivectorOneForm omega0 target point
              first internalPair)
          0 second +
        fieldDirectionalDerivative
          (fun point =>
            normalizedAffineBivectorOneForm omega0 target point
              second internalPair)
          0 first = 0 := by
  rw [normalizedAffineBivectorOneForm_directionalDerivative_zero,
    normalizedAffineBivectorOneForm_directionalDerivative_zero]
  fin_cases first <;> fin_cases second <;>
    simp [orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, Fin.sum_univ_six]

/-- Antisymmetrizing the affine derivative recovers the bracket-subtracted
target.  The two oriented terms each contribute one half. -/
theorem normalizedAffineBivectorOneForm_antisymmetrizedDerivative_zero
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (internalPair spacetimePair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          normalizedAffineBivectorOneForm omega0 target point
            (pairSecond spacetimePair) internalPair)
        0 (pairFirst spacetimePair) -
      fieldDirectionalDerivative
        (fun point =>
          normalizedAffineBivectorOneForm omega0 target point
            (pairFirst spacetimePair) internalPair)
        0 (pairSecond spacetimePair) =
      target internalPair spacetimePair -
        originLorentzBracketCurvature omega0 internalPair spacetimePair := by
  rw [normalizedAffineBivectorOneForm_directionalDerivative_zero,
    normalizedAffineBivectorOneForm_directionalDerivative_zero]
  fin_cases spacetimePair <;>
    simp [normalizedDerivativeBivector,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, Fin.sum_univ_six] <;>
    ring

/-- After lowering the first internal index, the derivative of the lifted
connection is exactly the derivative of the selected six-coordinate affine
one-form. -/
theorem normalizedAffineLorentzConnectionField_loweredDerivative_zero
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative
          (normalizedAffineConfiguration omega0 target) 0
          derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      fieldDirectionalDerivative
        (fun point =>
          normalizedAffineBivectorOneForm omega0 target point
            formDirection internalPair)
        0 derivativeDirection := by
  unfold gravityConnectionDerivative normalizedAffineConfiguration
    configurationOfLorentzConnection
    normalizedAffineLorentzConnectionField
  unfold fieldDirectionalDerivative normalizedAffineBivectorOneForm
  let component :=
    normalizedAffineBivectorComponentLinear omega0 target formDirection
      internalPair
  have componentDerivative :
      fderiv ℝ component (0 : BasePoint) = component :=
    component.hasFDerivAt.fderiv
  fin_cases internalPair <;>
    simp [lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.sum_univ_six]

private theorem normalizedAffineComponent_differentiableAt
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (row : LorentzianIndex) (internalPair : Fin 6) :
    DifferentiableAt ℝ
      (fun point =>
        normalizedAffineBivectorOneForm omega0 target point row internalPair)
      0 := by
  change DifferentiableAt ℝ
    (normalizedAffineBivectorComponentLinear omega0 target row internalPair) 0
  exact
    (normalizedAffineBivectorComponentLinear
      omega0 target row internalPair).differentiableAt

private theorem fieldDirectionalDerivative_const_real
    (constant : ℝ) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun _ : BasePoint => constant) 0 direction = 0 := by
  simp [fieldDirectionalDerivative]

private theorem fieldDirectionalDerivative_const_add_normalized
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (constant : ℝ) (row direction : LorentzianIndex)
    (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point => constant +
          normalizedAffineBivectorOneForm omega0 target point row internalPair)
        0 direction =
      fieldDirectionalDerivative
        (fun point =>
          normalizedAffineBivectorOneForm omega0 target point row internalPair)
        0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add (differentiableAt_const constant)
    (normalizedAffineComponent_differentiableAt
      omega0 target row internalPair)]
  simp

private theorem fieldDirectionalDerivative_const_add_neg_normalized
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (constant : ℝ) (row direction : LorentzianIndex)
    (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point => constant +
          -normalizedAffineBivectorOneForm omega0 target point row internalPair)
        0 direction =
      -fieldDirectionalDerivative
        (fun point =>
          normalizedAffineBivectorOneForm omega0 target point row internalPair)
        0 direction := by
  let field : BasePoint → ℝ := fun point =>
    normalizedAffineBivectorOneForm omega0 target point row internalPair
  change fieldDirectionalDerivative
      (fun point => (fun _ : BasePoint => constant) point + (-field) point)
      0 direction = -fieldDirectionalDerivative field 0 direction
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add (differentiableAt_const constant)
    (normalizedAffineComponent_differentiableAt
      omega0 target row internalPair).neg,
    fderiv_neg]
  simp [field]

/-- Every raised-index component of the normalized affine Lorentz connection
has zero symmetric first jet.  This is the connection-level form of the
source one-form's antisymmetry and does not evaluate the supplied target. -/
theorem normalizedAffineLorentzConnectionField_symmetricDerivative_zero
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (first second internalOut internalIn : LorentzianIndex) :
    fieldDirectionalDerivative
          (fun point =>
            normalizedAffineLorentzConnectionField omega0 target point
              first internalOut internalIn)
          0 second +
        fieldDirectionalDerivative
          (fun point =>
            normalizedAffineLorentzConnectionField omega0 target point
              second internalOut internalIn)
          0 first = 0 := by
  fin_cases internalOut <;> fin_cases internalIn <;>
    simp [normalizedAffineLorentzConnectionField,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      minkowskiInternalSign, pairFirst, pairSecond,
      Fin.sum_univ_six,
      fieldDirectionalDerivative_const_real,
      fieldDirectionalDerivative_const_add_normalized,
      fieldDirectionalDerivative_const_add_neg_normalized,
      normalizedAffineBivectorOneForm_symmetricDerivative_zero] <;>
    linarith
      [normalizedAffineBivectorOneForm_symmetricDerivative_zero
        omega0 target first second 0,
       normalizedAffineBivectorOneForm_symmetricDerivative_zero
        omega0 target first second 1,
       normalizedAffineBivectorOneForm_symmetricDerivative_zero
        omega0 target first second 2,
       normalizedAffineBivectorOneForm_symmetricDerivative_zero
        omega0 target first second 3,
       normalizedAffineBivectorOneForm_symmetricDerivative_zero
        omega0 target first second 4,
       normalizedAffineBivectorOneForm_symmetricDerivative_zero
        omega0 target first second 5]

/-- Generic normalized-germ producer theorem.  The actual holonomic curvature
at the origin is exactly the requested target; neither curvature nor an
equation certificate is a field of the resulting configuration. -/
theorem holonomicGravityCurvature_normalizedAffineConfiguration_zero
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) :
    holonomicGravityCurvature
        (normalizedAffineConfiguration omega0 target) 0 = target := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature
  dsimp only
  have firstDerivative :=
    normalizedAffineLorentzConnectionField_loweredDerivative_zero
      omega0 target (pairFirst spacetimePair) (pairSecond spacetimePair)
        internalPair
  have secondDerivative :=
    normalizedAffineLorentzConnectionField_loweredDerivative_zero
      omega0 target (pairSecond spacetimePair) (pairFirst spacetimePair)
        internalPair
  have antisymmetrized :=
    normalizedAffineBivectorOneForm_antisymmetrizedDerivative_zero
      omega0 target internalPair spacetimePair
  change
    minkowskiInternalSign (pairFirst internalPair) *
      (gravityConnectionDerivative
          (normalizedAffineConfiguration omega0 target) 0
          (pairFirst spacetimePair) (pairSecond spacetimePair)
          (pairFirst internalPair) (pairSecond internalPair) -
        gravityConnectionDerivative
          (normalizedAffineConfiguration omega0 target) 0
          (pairSecond spacetimePair) (pairFirst spacetimePair)
          (pairFirst internalPair) (pairSecond internalPair) +
        ∑ middle : LorentzianIndex,
          ((normalizedAffineConfiguration omega0 target).gravityConnection 0
                (pairFirst spacetimePair) (pairFirst internalPair) middle *
              (normalizedAffineConfiguration omega0 target).gravityConnection 0
                (pairSecond spacetimePair) middle (pairSecond internalPair) -
            (normalizedAffineConfiguration omega0 target).gravityConnection 0
                (pairSecond spacetimePair) (pairFirst internalPair) middle *
              (normalizedAffineConfiguration omega0 target).gravityConnection 0
                (pairFirst spacetimePair) middle (pairSecond internalPair))) =
      target internalPair spacetimePair
  have connectionAtZero :
      (normalizedAffineConfiguration omega0 target).gravityConnection 0 =
        omega0 := by
    exact normalizedAffineLorentzConnectionField_zero omega0 target
  rw [connectionAtZero]
  change
    minkowskiInternalSign (pairFirst internalPair) *
      (gravityConnectionDerivative
          (normalizedAffineConfiguration omega0 target) 0
          (pairFirst spacetimePair) (pairSecond spacetimePair)
          (pairFirst internalPair) (pairSecond internalPair) -
        gravityConnectionDerivative
          (normalizedAffineConfiguration omega0 target) 0
          (pairSecond spacetimePair) (pairFirst spacetimePair)
          (pairFirst internalPair) (pairSecond internalPair) +
        ∑ middle : LorentzianIndex,
          (omega0 (pairFirst spacetimePair) (pairFirst internalPair) middle *
              omega0 (pairSecond spacetimePair) middle
                (pairSecond internalPair) -
            omega0 (pairSecond spacetimePair) (pairFirst internalPair) middle *
              omega0 (pairFirst spacetimePair) middle
                (pairSecond internalPair))) =
      target internalPair spacetimePair
  have bracketReadout :
      originLorentzBracketCurvature omega0 internalPair spacetimePair =
        minkowskiInternalSign (pairFirst internalPair) *
          ∑ middle : LorentzianIndex,
            (omega0 (pairFirst spacetimePair) (pairFirst internalPair) middle *
                omega0 (pairSecond spacetimePair) middle
                  (pairSecond internalPair) -
              omega0 (pairSecond spacetimePair) (pairFirst internalPair) middle *
                omega0 (pairFirst spacetimePair) middle
                  (pairSecond internalPair)) := by
    rfl
  calc
    minkowskiInternalSign (pairFirst internalPair) *
        (gravityConnectionDerivative
            (normalizedAffineConfiguration omega0 target) 0
            (pairFirst spacetimePair) (pairSecond spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair) -
          gravityConnectionDerivative
            (normalizedAffineConfiguration omega0 target) 0
            (pairSecond spacetimePair) (pairFirst spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair) +
          ∑ middle : LorentzianIndex,
            (omega0 (pairFirst spacetimePair) (pairFirst internalPair) middle *
                omega0 (pairSecond spacetimePair) middle
                  (pairSecond internalPair) -
              omega0 (pairSecond spacetimePair) (pairFirst internalPair) middle *
                omega0 (pairFirst spacetimePair) middle
                  (pairSecond internalPair))) =
      (minkowskiInternalSign (pairFirst internalPair) *
          gravityConnectionDerivative
            (normalizedAffineConfiguration omega0 target) 0
            (pairFirst spacetimePair) (pairSecond spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair) -
        minkowskiInternalSign (pairFirst internalPair) *
          gravityConnectionDerivative
            (normalizedAffineConfiguration omega0 target) 0
            (pairSecond spacetimePair) (pairFirst spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair)) +
        minkowskiInternalSign (pairFirst internalPair) *
          ∑ middle : LorentzianIndex,
            (omega0 (pairFirst spacetimePair) (pairFirst internalPair) middle *
                omega0 (pairSecond spacetimePair) middle
                  (pairSecond internalPair) -
              omega0 (pairSecond spacetimePair) (pairFirst internalPair) middle *
                omega0 (pairFirst spacetimePair) middle
                  (pairSecond internalPair)) := by ring
    _ =
      (fieldDirectionalDerivative
          (fun point =>
            normalizedAffineBivectorOneForm omega0 target point
              (pairSecond spacetimePair) internalPair)
          0 (pairFirst spacetimePair) -
        fieldDirectionalDerivative
          (fun point =>
            normalizedAffineBivectorOneForm omega0 target point
              (pairFirst spacetimePair) internalPair)
          0 (pairSecond spacetimePair)) +
        minkowskiInternalSign (pairFirst internalPair) *
          ∑ middle : LorentzianIndex,
            (omega0 (pairFirst spacetimePair) (pairFirst internalPair) middle *
                omega0 (pairSecond spacetimePair) middle
                  (pairSecond internalPair) -
              omega0 (pairSecond spacetimePair) (pairFirst internalPair) middle *
                omega0 (pairFirst spacetimePair) middle
                  (pairSecond internalPair)) := by
      rw [firstDerivative, secondDerivative]
    _ =
      (target internalPair spacetimePair -
          originLorentzBracketCurvature omega0 internalPair spacetimePair) +
        minkowskiInternalSign (pairFirst internalPair) *
          ∑ middle : LorentzianIndex,
            (omega0 (pairFirst spacetimePair) (pairFirst internalPair) middle *
                omega0 (pairSecond spacetimePair) middle
                  (pairSecond internalPair) -
              omega0 (pairSecond spacetimePair) (pairFirst internalPair) middle *
                omega0 (pairFirst spacetimePair) middle
                  (pairSecond internalPair)) := by
      rw [antisymmetrized]
    _ = target internalPair spacetimePair := by
      rw [bracketReadout]
      ring

/-- Explicit normalized carrier: affine, zero symmetric derivative jet, and
zero higher jet are fixed by the displayed constructor rather than stored as
source choices. -/
structure NormalizedAffineLorentzConnectionGermCarrier
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) where
  connection : LorentzConnectionField
  normalized : connection =
    normalizedAffineLorentzConnectionField omega0 target

def generatedNormalizedAffineLorentzConnectionGerm
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) :
    NormalizedAffineLorentzConnectionGermCarrier omega0 target where
  connection := normalizedAffineLorentzConnectionField omega0 target
  normalized := rfl

@[ext] theorem NormalizedAffineLorentzConnectionGermCarrier.ext
    {omega0 : PointwiseLorentzSpinConnection}
    {target : PhysicalBivector}
    (first second :
      NormalizedAffineLorentzConnectionGermCarrier omega0 target)
    (connectionEquality : first.connection = second.connection) :
    first = second := by
  cases first
  cases second
  cases connectionEquality
  rfl

instance normalizedAffineLorentzConnectionGermCarrierSubsingleton
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) :
    Subsingleton
      (NormalizedAffineLorentzConnectionGermCarrier omega0 target) where
  allEq first second := by
    apply NormalizedAffineLorentzConnectionGermCarrier.ext
    rw [first.normalized, second.normalized]

theorem existsUnique_normalizedAffineLorentzConnectionGerm
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) :
    ∃! germ : NormalizedAffineLorentzConnectionGermCarrier omega0 target,
      germ = generatedNormalizedAffineLorentzConnectionGerm omega0 target := by
  exact ⟨generatedNormalizedAffineLorentzConnectionGerm omega0 target, rfl,
    fun candidate _ => Subsingleton.elim _ _⟩

/-! ## Positive-source production integration -/

/-- The origin connection value is an existing source-generated output, not a
new source field. -/
def positiveSourceGravityMouthOriginConnectionValue :
    PointwiseLorentzSpinConnection :=
  generatedLorentzConnectionAt positiveSmoothUnifiedSource 0

def positiveSourceGravityMouthNormalizedAffineConnectionField :
    LorentzConnectionField :=
  normalizedAffineLorentzConnectionField
    positiveSourceGravityMouthOriginConnectionValue
    positiveSourceGravityMouthRequiredCurvature

theorem positiveSourceGravityMouthNormalizedAffineConnectionField_origin :
    positiveSourceGravityMouthNormalizedAffineConnectionField 0 =
      positiveSourceGravityMouthOriginConnectionValue :=
  normalizedAffineLorentzConnectionField_zero _ _

theorem positiveSourceGravityMouthNormalizedAffineConnectionField_smooth :
    SmoothLorentzConnectionField
      positiveSourceGravityMouthNormalizedAffineConnectionField :=
  normalizedAffineLorentzConnectionField_smooth _ _

theorem positiveSourceGravityMouthNormalizedAffineConnectionField_lorentzSkew
    (point : BasePoint) :
    LorentzSkew
      (positiveSourceGravityMouthNormalizedAffineConnectionField point) := by
  exact normalizedAffineLorentzConnectionField_lorentzSkew _ _
    (positive_generatedLorentzConnection_lorentzSkew 0) point

/-- The normalized derivative repair does not disturb the source-generated
origin connection value, so the existing tetrad postulate remains valid at
the local mouth.  No compatibility claim away from the origin is made. -/
theorem positiveSourceGravityMouthNormalizedAffineConnectionField_origin_tetradCompatible :
    TetradCompatible (canonicalPhysicalSource.jetAt 0)
      (canonicalPhysicalSource.jetAt 0).leviCivitaConnection
      (positiveSourceGravityMouthNormalizedAffineConnectionField 0) := by
  rw [positiveSourceGravityMouthNormalizedAffineConnectionField_origin]
  exact positive_generatedLorentzConnection_tetradCompatible 0

def installPositiveSourceGravityMouthNormalizedAffineConnection
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gravityConnection :=
      positiveSourceGravityMouthNormalizedAffineConnectionField }

@[simp] theorem installPositiveSourceGravityMouthNormalizedAffineConnection_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (installPositiveSourceGravityMouthNormalizedAffineConnection configuration).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem installPositiveSourceGravityMouthNormalizedAffineConnection_gravityAuxiliary
    (configuration : StageNineHolonomicConfiguration) :
    (installPositiveSourceGravityMouthNormalizedAffineConnection
      configuration).gravityAuxiliary = configuration.gravityAuxiliary :=
  rfl

/-- The installer changes exactly one primitive field.  In particular it
does not erase gauge, matter, multiplier, or conjugate-matter responsibility
while lifting the gravity-mouth curvature obligation. -/
theorem installPositiveSourceGravityMouthNormalizedAffineConnection_preserves_otherFields
    (configuration : StageNineHolonomicConfiguration) :
    (installPositiveSourceGravityMouthNormalizedAffineConnection
        configuration).coframe = configuration.coframe ∧
      (installPositiveSourceGravityMouthNormalizedAffineConnection
        configuration).gravityAuxiliary = configuration.gravityAuxiliary ∧
      (installPositiveSourceGravityMouthNormalizedAffineConnection
        configuration).gravitySimplicityMultiplier =
          configuration.gravitySimplicityMultiplier ∧
      (installPositiveSourceGravityMouthNormalizedAffineConnection
        configuration).gaugeConnection = configuration.gaugeConnection ∧
      (installPositiveSourceGravityMouthNormalizedAffineConnection
        configuration).gaugeAuxiliary = configuration.gaugeAuxiliary ∧
      (installPositiveSourceGravityMouthNormalizedAffineConnection
        configuration).scalar = configuration.scalar ∧
      (installPositiveSourceGravityMouthNormalizedAffineConnection
        configuration).matter = configuration.matter ∧
      (installPositiveSourceGravityMouthNormalizedAffineConnection
        configuration).conjugateMatter = configuration.conjugateMatter := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem installPositiveSourceGravityMouthNormalizedAffineConnection_nondegenerate_iff
    (configuration : StageNineHolonomicConfiguration) :
    (installPositiveSourceGravityMouthNormalizedAffineConnection
        configuration).Nondegenerate ↔ configuration.Nondegenerate :=
  Iff.rfl

theorem installPositiveSourceGravityMouthNormalizedAffineConnection_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (installPositiveSourceGravityMouthNormalizedAffineConnection
      configuration).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, _gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth,
      positiveSourceGravityMouthNormalizedAffineConnectionField_smooth,
      gravityAuxiliarySmooth, gravityMultiplierSmooth, gaugeConnectionSmooth,
      gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩

theorem installPositiveSourceGravityMouthNormalizedAffineConnection_curvature_origin
    (configuration : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        (installPositiveSourceGravityMouthNormalizedAffineConnection
          configuration) 0 =
      positiveSourceGravityMouthRequiredCurvature := by
  change holonomicGravityCurvature
      (normalizedAffineConfiguration
        positiveSourceGravityMouthOriginConnectionValue
        positiveSourceGravityMouthRequiredCurvature) 0 =
    positiveSourceGravityMouthRequiredCurvature
  exact holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

theorem installPositiveSourceGravityMouthNormalizedAffineConnection_transports_projection
    (configuration : StageNineHolonomicConfiguration)
    (preservesCoframe :
      PreservesPositiveSourceCoframeAtOrigin configuration)
    (simplicityMouth : configuration.gravityAuxiliary 0 =
      physicalIIPlusBivector (configuration.coframe 0)) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (installPositiveSourceGravityMouthNormalizedAffineConnection
          configuration) 0).gravityAuxiliary =
      positiveSourceGravityMouthTransportedResidual := by
  apply (currentGravityAuxiliaryProjection_eq_transported_iff
    (installPositiveSourceGravityMouthNormalizedAffineConnection configuration)
    preservesCoframe simplicityMouth).mpr
  exact
    installPositiveSourceGravityMouthNormalizedAffineConnection_curvature_origin
      configuration

/-- Smooth templates inherit the existing off-shell differential Bianchi
identity after installation.  No Bianchi receipt is stored in the germ. -/
theorem installPositiveSourceGravityMouthNormalizedAffineConnection_bianchi
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantMixedCurvatureDerivative
          (installPositiveSourceGravityMouthNormalizedAffineConnection
            configuration) point first second third +
        covariantMixedCurvatureDerivative
          (installPositiveSourceGravityMouthNormalizedAffineConnection
            configuration) point second third first +
        covariantMixedCurvatureDerivative
          (installPositiveSourceGravityMouthNormalizedAffineConnection
            configuration) point third first second = 0 := by
  exact holonomicGravityGL4Curvature_bianchi
    (installPositiveSourceGravityMouthNormalizedAffineConnection configuration)
    (installPositiveSourceGravityMouthNormalizedAffineConnection_smooth
      configuration smooth) point first second third

/-- The normalized connection closes the requested projection, but the first
transported residual is nonzero, so this one-channel lift is not terminal
joint-shell closure. -/
theorem installPositiveSourceGravityMouthNormalizedAffineConnection_not_jointZeroFiber
    (configuration : StageNineHolonomicConfiguration)
    (preservesCoframe :
      PreservesPositiveSourceCoframeAtOrigin configuration)
    (simplicityMouth : configuration.gravityAuxiliary 0 =
      physicalIIPlusBivector (configuration.coframe 0)) :
    ¬ CurrentJointShellZeroFiber positiveSmoothUnifiedSource
      (installPositiveSourceGravityMouthNormalizedAffineConnection
        configuration) := by
  exact transportedGravityProjection_not_jointZeroFiber
    (installPositiveSourceGravityMouthNormalizedAffineConnection configuration)
    (installPositiveSourceGravityMouthNormalizedAffineConnection_transports_projection
      configuration preservesCoframe simplicityMouth)

/-- Source admission remains separate from the connection construction:
exact P506/L0 lineage and endpoint 11 qualify the same source, while the
connection field and its curvature are derived outputs.  Factor atomhood is
not a physical-source premise here. -/
theorem positiveExactLineage_generates_normalizedAffineGravityConnection :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
          canonicalSource_generatedLineage_height_pos = 11 ∧
      SmoothLorentzConnectionField
        positiveSourceGravityMouthNormalizedAffineConnectionField ∧
      (∀ point,
        LorentzSkew
          (positiveSourceGravityMouthNormalizedAffineConnectionField point)) ∧
      ∀ configuration : StageNineHolonomicConfiguration,
        holonomicGravityCurvature
            (installPositiveSourceGravityMouthNormalizedAffineConnection
              configuration) 0 =
          positiveSourceGravityMouthRequiredCurvature :=
  ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
    positiveSmoothUnifiedSource_generates_endpoint_eleven,
    positiveSourceGravityMouthNormalizedAffineConnectionField_smooth,
    positiveSourceGravityMouthNormalizedAffineConnectionField_lorentzSkew,
    installPositiveSourceGravityMouthNormalizedAffineConnection_curvature_origin⟩

end

end SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
