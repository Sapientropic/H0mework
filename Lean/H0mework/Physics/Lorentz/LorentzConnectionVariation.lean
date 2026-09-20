import H0mework.Physics.Geometry.CompactSupportIntegrationByParts

/-!
# S9-C3b0: primitive Lorentz-skew connection variation

The primitive gravity connection is varied only through six lowered internal
bivector coordinates per spacetime one-form direction.  Their explicit lift
to vector-index connection coefficients is proved Lorentz-skew and is proved
to recover the original six coordinates.  Thus admissibility is generated,
not accepted as a Boolean or equation receipt.

For every compactly supported smooth variation, the actual holonomic
curvature satisfies the exact non-Abelian polynomial

`F(ω + tη) = F(ω) + t Dωη + t²[η,η]`.

The same primitive variation is transported through the actual Dirac spin
connection lift, so it simultaneously generates the matter spin-current jet.
An explicit pair of boost directions has a nonzero quadratic rotation
channel, rejecting an Abelianized Lorentz variation.  No curvature, spin
current, stationarity, or field-equation certificate is supplied.
-/

namespace SaturationMonoid.PhysicsCore.StageNineLorentzConnectionVariation

open ProofFreeRicherAnholonomicSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open PointwiseDiracSpinConnectionLift
open DiracExteriorMatterAction
open DiracCliffordRepresentation
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open scoped ContDiff

noncomputable section

set_option maxHeartbeats 600000

/-- Six lowered internal-bivector coordinates for every spacetime one-form
direction. -/
abbrev LorentzBivectorOneForm := LorentzianIndex → Fin 6 → ℝ

def orientedLorentzBivectorBasisCoefficient
    (pair : Fin 6) (first second : LorentzianIndex) : ℝ :=
  (if first = pairFirst pair ∧ second = pairSecond pair then 1 else 0) -
    if first = pairSecond pair ∧ second = pairFirst pair then 1 else 0

def loweredLorentzBivectorMatrix
    (coordinates : Fin 6 → ℝ) (first second : LorentzianIndex) : ℝ :=
  ∑ pair : Fin 6,
    coordinates pair *
      orientedLorentzBivectorBasisCoefficient pair first second

/-- Raise the first internal index with the fixed Minkowski metric. -/
def lorentzSkewConnectionOfBivectorOneForm
    (variation : LorentzBivectorOneForm) :
    PointwiseLorentzSpinConnection :=
  fun formDirection internalOut internalIn =>
    minkowskiInternalSign internalOut *
      loweredLorentzBivectorMatrix (variation formDirection)
        internalOut internalIn

theorem loweredLorentzConnectionCoefficient_ofBivectorOneForm
    (variation : LorentzBivectorOneForm)
    (formDirection : LorentzianIndex) (pair : Fin 6) :
    loweredLorentzConnectionCoefficient
        (lorentzSkewConnectionOfBivectorOneForm variation)
        formDirection pair =
      variation formDirection pair := by
  fin_cases pair <;>
    simp [loweredLorentzConnectionCoefficient,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      lorentzBivectorFirst, lorentzBivectorSecond,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.sum_univ_six]

theorem lorentzSkewConnectionOfBivectorOneForm_lorentzSkew
    (variation : LorentzBivectorOneForm) :
    LorentzSkew (lorentzSkewConnectionOfBivectorOneForm variation) := by
  intro formDirection
  rw [PointwiseLorentzianCoframeJet.minkowskiInternalMetric_eq_diagonal_sign]
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [spinConnectionMatrix,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, minkowskiInternalSign,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_six]

theorem lorentzSkewConnectionOfBivectorOneForm_add
    (first second : LorentzBivectorOneForm) :
    lorentzSkewConnectionOfBivectorOneForm (first + second) =
      lorentzSkewConnectionOfBivectorOneForm first +
        lorentzSkewConnectionOfBivectorOneForm second := by
  funext formDirection internalOut internalIn
  simp [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix, Finset.sum_add_distrib, add_mul,
    mul_add]

theorem lorentzSkewConnectionOfBivectorOneForm_smul
    (parameter : ℝ) (variation : LorentzBivectorOneForm) :
    lorentzSkewConnectionOfBivectorOneForm (parameter • variation) =
      parameter • lorentzSkewConnectionOfBivectorOneForm variation := by
  funext formDirection internalOut internalIn
  simp [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix, Finset.mul_sum]
  ring_nf

/-- The only Lorentz-connection variation mouth: six actual `so(1,3)`
coordinates are varied, every other primitive field is fixed. -/
def varyLorentzConnection
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm) (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gravityConnection := fun point =>
      configuration.gravityConnection point +
        parameter •
          lorentzSkewConnectionOfBivectorOneForm (variation point) }

@[simp] theorem varyLorentzConnection_zero
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm) :
    varyLorentzConnection configuration variation 0 = configuration := by
  cases configuration
  simp [varyLorentzConnection]

theorem gravityConnection_varyLorentzConnection
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm) (parameter : ℝ)
    (point : BasePoint) :
    (varyLorentzConnection configuration variation parameter).gravityConnection
        point =
      configuration.gravityConnection point +
        parameter •
          lorentzSkewConnectionOfBivectorOneForm (variation point) :=
  rfl

def lorentzConnectionVariationDerivative
    (variation : BasePoint → LorentzBivectorOneForm)
    (point : BasePoint)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) : ℝ :=
  fieldDirectionalDerivative
    (fun candidate =>
      lorentzSkewConnectionOfBivectorOneForm (variation candidate)
        formDirection internalOut internalIn)
    point derivativeDirection

theorem gravityConnectionDerivative_varyLorentzConnection
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (parameter : ℝ) (point : BasePoint)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    gravityConnectionDerivative
        (varyLorentzConnection configuration variation parameter)
        point derivativeDirection formDirection internalOut internalIn =
      gravityConnectionDerivative configuration point derivativeDirection
          formDirection internalOut internalIn +
        parameter * lorentzConnectionVariationDerivative variation point
          derivativeDirection formDirection internalOut internalIn := by
  have backgroundSmooth : ContDiff ℝ ∞ fun candidate =>
      configuration.gravityConnection candidate formDirection
        internalOut internalIn :=
    smooth.2.1 formDirection internalOut internalIn
  have coordinateSmooth : ∀ pair : Fin 6,
      ContDiff ℝ ∞ fun candidate =>
        variation candidate formDirection pair := by
    intro pair
    exact contDiff_pi.mp (contDiff_pi.mp variation.smooth formDirection) pair
  have variationSmooth : ContDiff ℝ ∞ fun candidate =>
      lorentzSkewConnectionOfBivectorOneForm (variation candidate)
        formDirection internalOut internalIn := by
    unfold lorentzSkewConnectionOfBivectorOneForm
      loweredLorentzBivectorMatrix
    exact contDiff_const.mul
      (ContDiff.sum fun pair _ =>
        (coordinateSmooth pair).mul contDiff_const)
  have backgroundDifferentiable : DifferentiableAt ℝ
      (fun candidate =>
        configuration.gravityConnection candidate formDirection
          internalOut internalIn) point :=
    (backgroundSmooth.differentiable (by simp)).differentiableAt
  have variationDifferentiable : DifferentiableAt ℝ
      (fun candidate =>
        lorentzSkewConnectionOfBivectorOneForm (variation candidate)
          formDirection internalOut internalIn) point :=
    (variationSmooth.differentiable (by simp)).differentiableAt
  unfold gravityConnectionDerivative lorentzConnectionVariationDerivative
    fieldDirectionalDerivative
  change
    fderiv ℝ
        (fun candidate =>
          configuration.gravityConnection candidate formDirection
              internalOut internalIn +
            parameter *
              lorentzSkewConnectionOfBivectorOneForm (variation candidate)
                formDirection internalOut internalIn)
        point (coordinateDirection derivativeDirection) = _
  have derivativeEquality :
      fderiv ℝ
          (fun candidate =>
            configuration.gravityConnection candidate formDirection
                internalOut internalIn +
              parameter *
                lorentzSkewConnectionOfBivectorOneForm (variation candidate)
                  formDirection internalOut internalIn)
          point =
        fderiv ℝ
            (fun candidate =>
              configuration.gravityConnection candidate formDirection
                internalOut internalIn)
            point +
          parameter • fderiv ℝ
            (fun candidate =>
              lorentzSkewConnectionOfBivectorOneForm (variation candidate)
                formDirection internalOut internalIn)
            point := by
    exact (backgroundDifferentiable.hasFDerivAt.add
      (variationDifferentiable.hasFDerivAt.const_smul parameter)).fderiv
  rw [derivativeEquality]
  simp

def lorentzConnectionLinearCurvatureVariation
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm)
    (point : BasePoint) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    let internalOut := pairFirst internalPair
    let internalIn := pairSecond internalPair
    let first := pairFirst spacetimePair
    let second := pairSecond spacetimePair
    let varied := lorentzSkewConnectionOfBivectorOneForm (variation point)
    minkowskiInternalSign internalOut *
      (lorentzConnectionVariationDerivative variation point first second
          internalOut internalIn -
        lorentzConnectionVariationDerivative variation point second first
          internalOut internalIn +
        ∑ middle : LorentzianIndex,
          (varied first internalOut middle *
              configuration.gravityConnection point second middle internalIn +
            configuration.gravityConnection point first internalOut middle *
              varied second middle internalIn -
            varied second internalOut middle *
              configuration.gravityConnection point first middle internalIn -
            configuration.gravityConnection point second internalOut middle *
              varied first middle internalIn))

def lorentzConnectionQuadraticCurvatureVariation
    (variation : BasePoint → LorentzBivectorOneForm)
    (point : BasePoint) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    let internalOut := pairFirst internalPair
    let internalIn := pairSecond internalPair
    let first := pairFirst spacetimePair
    let second := pairSecond spacetimePair
    let varied := lorentzSkewConnectionOfBivectorOneForm (variation point)
    minkowskiInternalSign internalOut *
      ∑ middle : LorentzianIndex,
        (varied first internalOut middle * varied second middle internalIn -
          varied second internalOut middle * varied first middle internalIn)

theorem holonomicGravityCurvature_varyLorentzConnection
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (parameter : ℝ) (point : BasePoint) :
    holonomicGravityCurvature
        (varyLorentzConnection configuration variation parameter) point =
      holonomicGravityCurvature configuration point +
        parameter •
          lorentzConnectionLinearCurvatureVariation configuration variation
            point +
        parameter ^ 2 •
          lorentzConnectionQuadraticCurvatureVariation variation point := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature
    lorentzConnectionLinearCurvatureVariation
    lorentzConnectionQuadraticCurvatureVariation
  dsimp only
  rw [gravityConnectionDerivative_varyLorentzConnection configuration smooth,
    gravityConnectionDerivative_varyLorentzConnection configuration smooth]
  simp only [gravityConnection_varyLorentzConnection, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [pairFirst, pairSecond, Fin.sum_univ_four] <;> ring

theorem loweredLorentzConnectionCoefficient_add
    (first second : PointwiseLorentzSpinConnection)
    (formDirection : LorentzianIndex) (pair : Fin 6) :
    loweredLorentzConnectionCoefficient (first + second) formDirection pair =
      loweredLorentzConnectionCoefficient first formDirection pair +
        loweredLorentzConnectionCoefficient second formDirection pair := by
  simp [loweredLorentzConnectionCoefficient]
  ring

theorem loweredLorentzConnectionCoefficient_smul
    (parameter : ℝ) (connection : PointwiseLorentzSpinConnection)
    (formDirection : LorentzianIndex) (pair : Fin 6) :
    loweredLorentzConnectionCoefficient (parameter • connection)
        formDirection pair =
      parameter *
        loweredLorentzConnectionCoefficient connection formDirection pair := by
  simp [loweredLorentzConnectionCoefficient]
  ring

theorem diracSpinConnectionLift_add
    (first second : PointwiseLorentzSpinConnection)
    (formDirection : LorentzianIndex) :
    diracSpinConnectionLift (first + second) formDirection =
      diracSpinConnectionLift first formDirection +
        diracSpinConnectionLift second formDirection := by
  unfold diracSpinConnectionLift
  simp_rw [loweredLorentzConnectionCoefficient_add]
  simp only [Complex.ofReal_add, mul_add, add_smul,
    Finset.sum_add_distrib]

theorem diracSpinConnectionLift_real_smul
    (parameter : ℝ) (connection : PointwiseLorentzSpinConnection)
    (formDirection : LorentzianIndex) :
    diracSpinConnectionLift (parameter • connection) formDirection =
      parameter • diracSpinConnectionLift connection formDirection := by
  unfold diracSpinConnectionLift
  simp_rw [loweredLorentzConnectionCoefficient_smul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  module

theorem diracMatrixMatterAction_add_matrix_local
    (first second : DiracMatrix) (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (first + second) matter =
      diracMatrixMatterAction first matter +
        diracMatrixMatterAction second matter := by
  funext row
  simp [diracMatrixMatterAction, add_smul, Finset.sum_add_distrib]

theorem diracMatrixMatterAction_real_smul_matrix_local
    (parameter : ℝ) (matrix : DiracMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (parameter • matrix) matter =
      parameter • diracMatrixMatterAction matrix matter := by
  funext row
  change
    (∑ column,
      ((parameter : ℂ) * matrix row column) • matter column) =
      (parameter : ℂ) •
        ∑ column, matrix row column • matter column
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro column _
  simp [smul_smul]

def holonomicMatterLorentzConnectionVariation
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm)
    (point : BasePoint) (formDirection : LorentzianIndex) :
    DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
    (diracSpinConnectionLift
      (lorentzSkewConnectionOfBivectorOneForm (variation point))
      formDirection)
    (configuration.matter point)

theorem holonomicMatterCovariantDerivative_lorentzConnection_expansion
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzBivectorOneForm) (parameter : ℝ)
    (point : BasePoint) (formDirection : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (varyLorentzConnection configuration variation parameter)
        point formDirection =
      holonomicMatterCovariantDerivative configuration point formDirection +
        parameter • holonomicMatterLorentzConnectionVariation
          configuration variation point formDirection := by
  unfold holonomicMatterCovariantDerivative
    holonomicMatterLorentzConnectionVariation
  change
    matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun candidate => matterCoordinateEquiv (configuration.matter candidate))
            point formDirection) +
        diracMatrixMatterAction
          (diracSpinConnectionLift
            ((varyLorentzConnection configuration variation parameter).gravityConnection
              point) formDirection)
          (configuration.matter point) +
      diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (configuration.gaugeConnection point formDirection))
        (configuration.matter point) = _
  rw [gravityConnection_varyLorentzConnection,
    diracSpinConnectionLift_add,
    diracSpinConnectionLift_real_smul,
    diracMatrixMatterAction_add_matrix_local,
    diracMatrixMatterAction_real_smul_matrix_local]
  module

/-- One primitive admissible variation generates both the non-Abelian
Lorentz curvature jet and the actual Dirac spin-current jet. -/
theorem lorentzConnectionVariation_generates_curvatureAndSpinJet
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (parameter : ℝ) (point : BasePoint) :
    (∀ candidate,
      LorentzSkew
        (lorentzSkewConnectionOfBivectorOneForm (variation candidate))) ∧
      holonomicGravityCurvature
          (varyLorentzConnection configuration variation parameter) point =
        holonomicGravityCurvature configuration point +
          parameter •
            lorentzConnectionLinearCurvatureVariation configuration variation
              point +
          parameter ^ 2 •
            lorentzConnectionQuadraticCurvatureVariation variation point ∧
      ∀ formDirection,
        holonomicMatterCovariantDerivative
            (varyLorentzConnection configuration variation parameter)
            point formDirection =
          holonomicMatterCovariantDerivative configuration point formDirection +
            parameter • holonomicMatterLorentzConnectionVariation
              configuration variation point formDirection :=
  ⟨fun candidate =>
      lorentzSkewConnectionOfBivectorOneForm_lorentzSkew
        (variation candidate),
    holonomicGravityCurvature_varyLorentzConnection configuration smooth
      variation parameter point,
    holonomicMatterCovariantDerivative_lorentzConnection_expansion
      configuration variation parameter point⟩

def nonAbelianLorentzConnectionOneForm : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    if formDirection = 0 ∧ internalPair = 0 then 1
    else if formDirection = 1 ∧ internalPair = 1 then 1
    else 0

def nonAbelianCompactLorentzConnectionVariation :
    CompactlySupportedSmoothVariation LorentzBivectorOneForm where
  toFun := fun point =>
    nonzeroCompactScalarVariation point •
      nonAbelianLorentzConnectionOneForm
  smooth := nonzeroCompactScalarVariation.smooth.smul contDiff_const
  compactSupport := by
    have scalarCompact := nonzeroCompactScalarVariation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at scalarCompact ⊢
    filter_upwards [scalarCompact] with point scalarZero
    simp [scalarZero]

theorem nonAbelianCompactLorentzConnectionVariation_center :
    nonAbelianCompactLorentzConnectionVariation (0 : BasePoint) =
      nonAbelianLorentzConnectionOneForm := by
  have bumpOne : nonzeroCompactScalarVariation (0 : BasePoint) = 1 := by
    apply unitCompactBump.one_of_mem_closedBall
    exact Metric.mem_closedBall_self unitCompactBump.rIn_pos.le
  change unitCompactBump (0 : BasePoint) •
      nonAbelianLorentzConnectionOneForm =
    nonAbelianLorentzConnectionOneForm
  rw [show unitCompactBump (0 : BasePoint) = 1 by exact bumpOne]
  exact one_smul ℝ nonAbelianLorentzConnectionOneForm

/-- Negative regression against Abelianizing the Lorentz connection: two
actual boost directions generate a nonzero rotation commutator. -/
theorem nonAbelianLorentzConnectionQuadraticCurvature_ne_zero :
    lorentzConnectionQuadraticCurvatureVariation
        nonAbelianCompactLorentzConnectionVariation (0 : BasePoint) 5 0 ≠ 0 := by
  have center := nonAbelianCompactLorentzConnectionVariation_center
  change nonAbelianCompactLorentzConnectionVariation.toFun (0 : BasePoint) =
    nonAbelianLorentzConnectionOneForm at center
  have internalFirst : pairFirst (5 : Fin 6) = 1 := by decide
  have internalSecond : pairSecond (5 : Fin 6) = 2 := by decide
  have spacetimeFirst : pairFirst (0 : Fin 6) = 0 := by decide
  have spacetimeSecond : pairSecond (0 : Fin 6) = 1 := by decide
  unfold lorentzConnectionQuadraticCurvatureVariation
  rw [center]
  simp only [internalFirst, internalSecond, spacetimeFirst, spacetimeSecond]
  simp [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    nonAbelianLorentzConnectionOneForm,
    pairFirst, pairSecond, minkowskiInternalSign]

end

end SaturationMonoid.PhysicsCore.StageNineLorentzConnectionVariation
