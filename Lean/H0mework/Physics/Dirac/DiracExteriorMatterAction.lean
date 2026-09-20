import H0mework.Physics.Dirac.PointwiseDiracSpinConnectionLift
import H0mework.Physics.MatterJets.SU7ExteriorMatterGaugeCovariantJet

/-!
# Pointwise Dirac action for the actual Stage-7 exterior matter carrier

This module forms the finite tensor-product carrier

`C^4_Dirac ⊗ (Λ⁶V ⊕ Λ²V ⊕ Λ⁴V)`

as Dirac-indexed exterior matter.  The generated Lorentz/Dirac connection acts
on the spin index while the same Stage-6 mother connection acts on the
internal index; Lean proves these actions commute.  Their joint first-jet
derivative is contracted with the inverse coframe gamma matrices and paired
with the independent conjugate field to form a pointwise density.  Constant
SU(7) covariance, scalar-density invariance, exact mother-connection use, and
a nonzero density regression are proved.

Boundary: the internal connection contribution here is the finite transport
jet from `SU7ExteriorMatterGaugeCovariantJet`, not yet the infinitesimal
derived exterior Lie action.  Thus the result is an honest pointwise finite
action checkpoint, but local-gauge covariance and full field variation remain
open and are not claimed by this module.
-/

namespace SaturationMonoid.PhysicsCore.DiracExteriorMatterAction

open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open PointwiseLorentzianCoframeJet
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorMatterGaugeCovariantJet
open SU7MotherGaugeTheory

noncomputable section

abbrev DiracExteriorMatterCarrier :=
  DiracSpinorIndex → SU7ExteriorSpinorMatterCarrier

def diracMatrixMatterAction (matrix : DiracMatrix) :
    Module.End ℂ DiracExteriorMatterCarrier where
  toFun field := fun row =>
    ∑ column : DiracSpinorIndex, matrix row column • field column
  map_add' first second := by
    funext row
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' scalar field := by
    funext row
    change
      (∑ column, matrix row column • (scalar • field column)) =
        scalar • ∑ column, matrix row column • field column
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro column _
    simp [smul_smul, mul_comm]

def internalMatterLinearAction
    (action : Module.End ℂ SU7ExteriorSpinorMatterCarrier) :
    Module.End ℂ DiracExteriorMatterCarrier where
  toFun field := fun spinIndex => action (field spinIndex)
  map_add' first second := by
    funext spinIndex
    exact action.map_add (first spinIndex) (second spinIndex)
  map_smul' scalar field := by
    funext spinIndex
    exact action.map_smul scalar (field spinIndex)

def diracExteriorMatterGaugeRepresentation :
    Representation ℂ SU7MotherGroup DiracExteriorMatterCarrier where
  toFun groupElement :=
    internalMatterLinearAction
      (su7ExteriorSpinorMatterRepresentation groupElement)
  map_one' := by
    apply LinearMap.ext
    intro field
    funext spinIndex
    simp [internalMatterLinearAction]
  map_mul' first second := by
    apply LinearMap.ext
    intro field
    funext spinIndex
    change
      su7ExteriorSpinorMatterRepresentation (first * second)
          (field spinIndex) =
        su7ExteriorSpinorMatterRepresentation first
          (su7ExteriorSpinorMatterRepresentation second (field spinIndex))
    rw [map_mul]
    rfl

theorem diracMatrixMatterAction_commutes_internal
    (matrix : DiracMatrix)
    (action : Module.End ℂ SU7ExteriorSpinorMatterCarrier) :
    (diracMatrixMatterAction matrix).comp
        (internalMatterLinearAction action) =
      (internalMatterLinearAction action).comp
        (diracMatrixMatterAction matrix) := by
  apply LinearMap.ext
  intro field
  funext row
  simp [diracMatrixMatterAction, internalMatterLinearAction,
    map_sum]

def diracSpinConnectionMatterAction
    (jet : PointwiseLorentzianCoframeJet)
    (direction : LorentzianIndex) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
    (diracSpinConnectionLift jet.lorentzSpinConnection direction)

def motherGaugeMatterAction
    (connection : SU7MotherGaugeConnection)
    (direction : LorentzianIndex) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  internalMatterLinearAction
    (exteriorSpinorMotherIncrement (connection.potential direction))

theorem diracSpinConnectionMatterAction_commutes_motherGauge
    (jet : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (direction spinDirection : LorentzianIndex) :
    (diracSpinConnectionMatterAction jet direction).comp
        (motherGaugeMatterAction connection spinDirection) =
      (motherGaugeMatterAction connection spinDirection).comp
        (diracSpinConnectionMatterAction jet direction) := by
  exact diracMatrixMatterAction_commutes_internal _ _

structure DiracExteriorMatterFirstJet where
  field : DiracExteriorMatterCarrier
  derivative : LorentzianIndex → DiracExteriorMatterCarrier
  conjugateField : Module.Dual ℂ DiracExteriorMatterCarrier

def constantGaugeTransformDiracMatterJet
    (groupElement : SU7MotherGroup)
    (jet : DiracExteriorMatterFirstJet) : DiracExteriorMatterFirstJet where
  field := diracExteriorMatterGaugeRepresentation groupElement jet.field
  derivative := fun direction =>
    diracExteriorMatterGaugeRepresentation groupElement
      (jet.derivative direction)
  conjugateField := jet.conjugateField.comp
    (diracExteriorMatterGaugeRepresentation groupElement⁻¹)

def diracExteriorMatterCovariantDerivative
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (jet : DiracExteriorMatterFirstJet)
    (direction : LorentzianIndex) : DiracExteriorMatterCarrier :=
  jet.derivative direction +
    diracSpinConnectionMatterAction geometry direction jet.field +
    motherGaugeMatterAction connection direction jet.field

theorem diracExteriorMatterCovariantDerivative_constantGauge_covariant
    (groupElement : SU7MotherGroup)
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (jet : DiracExteriorMatterFirstJet)
    (direction : LorentzianIndex) :
    diracExteriorMatterCovariantDerivative geometry
        (constantGaugeTransformMotherConnection groupElement connection)
        (constantGaugeTransformDiracMatterJet groupElement jet) direction =
      diracExteriorMatterGaugeRepresentation groupElement
        (diracExteriorMatterCovariantDerivative geometry connection jet direction) := by
  funext spinIndex
  have hgauge := LinearMap.congr_fun
    (exteriorSpinorMotherIncrement_covariant groupElement
      (connection.potential direction)) (jet.field spinIndex)
  change
    exteriorSpinorMotherIncrement
        (motherGaugeConjugate groupElement
          (connection.potential direction))
        (su7ExteriorSpinorMatterRepresentation groupElement
          (jet.field spinIndex)) =
      su7ExteriorSpinorMatterRepresentation groupElement
        (exteriorSpinorMotherIncrement (connection.potential direction)
          (jet.field spinIndex)) at hgauge
  change
    su7ExteriorSpinorMatterRepresentation groupElement
          (jet.derivative direction spinIndex) +
        (∑ column : DiracSpinorIndex,
          diracSpinConnectionLift geometry.lorentzSpinConnection direction
              spinIndex column •
            su7ExteriorSpinorMatterRepresentation groupElement
              (jet.field column)) +
        exteriorSpinorMotherIncrement
            (motherGaugeConjugate groupElement
              (connection.potential direction))
          (su7ExteriorSpinorMatterRepresentation groupElement
            (jet.field spinIndex)) =
      su7ExteriorSpinorMatterRepresentation groupElement
        (jet.derivative direction spinIndex +
          (∑ column : DiracSpinorIndex,
            diracSpinConnectionLift geometry.lorentzSpinConnection direction
                spinIndex column • jet.field column) +
          exteriorSpinorMotherIncrement (connection.potential direction)
            (jet.field spinIndex))
  rw [map_add, map_add, map_sum]
  simp_rw [map_smul]
  rw [hgauge]

def inverseCoframeDiracGamma
    (geometry : PointwiseLorentzianCoframeJet)
    (coordinate : LorentzianIndex) : DiracMatrix :=
  ∑ internal : LorentzianIndex,
    (geometry.coframe⁻¹ coordinate internal : ℂ) • diracGamma internal

/-- Coordinate principal after multiplying the Dirac equation by the fixed
internal-time principal. -/
def coframeCoordinateDiracEvolutionPrincipal
    (coframe : LorentzianCoframe)
    (coordinate : LorentzianIndex) : DiracMatrix :=
  diracFramePrincipal 0 *
    (Complex.I • inverseCoframeDiracGamma
      { coframe := coframe, derivative := 0 } coordinate)

/-- Every transformed coordinate coefficient is Hermitian for an arbitrary
real coframe. -/
theorem coframeCoordinateDiracEvolutionPrincipal_isHermitian
    (coframe : LorentzianCoframe)
    (coordinate : LorentzianIndex) :
    Matrix.IsHermitian
      (coframeCoordinateDiracEvolutionPrincipal coframe coordinate) := by
  apply Matrix.IsHermitian.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [coframeCoordinateDiracEvolutionPrincipal,
      diracFramePrincipal, inverseCoframeDiracGamma,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, Matrix.mul_apply,
      Fin.sum_univ_four]

def diracExteriorMatterKineticVector
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (jet : DiracExteriorMatterFirstJet) : DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ coordinate : LorentzianIndex,
      diracMatrixMatterAction (inverseCoframeDiracGamma geometry coordinate)
        (diracExteriorMatterCovariantDerivative geometry connection jet coordinate)

theorem diracExteriorMatterKineticVector_constantGauge_covariant
    (groupElement : SU7MotherGroup)
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (jet : DiracExteriorMatterFirstJet) :
    diracExteriorMatterKineticVector geometry
        (constantGaugeTransformMotherConnection groupElement connection)
        (constantGaugeTransformDiracMatterJet groupElement jet) =
      diracExteriorMatterGaugeRepresentation groupElement
        (diracExteriorMatterKineticVector geometry connection jet) := by
  rw [diracExteriorMatterKineticVector,
    diracExteriorMatterKineticVector, map_smul, map_sum]
  apply congrArg (fun field => Complex.I • field)
  apply Finset.sum_congr rfl
  intro coordinate _
  have hderivative :=
    diracExteriorMatterCovariantDerivative_constantGauge_covariant
      groupElement geometry connection jet coordinate
  rw [hderivative]
  exact LinearMap.congr_fun
    (diracMatrixMatterAction_commutes_internal
      (inverseCoframeDiracGamma geometry coordinate)
      (su7ExteriorSpinorMatterRepresentation groupElement))
    (diracExteriorMatterCovariantDerivative geometry connection jet coordinate)

def diracExteriorMatterActionDensity
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (jet : DiracExteriorMatterFirstJet) : ℂ :=
  ((abs (Matrix.det geometry.coframe) : ℝ) : ℂ) *
    jet.conjugateField
      (diracExteriorMatterKineticVector geometry connection jet)

theorem diracExteriorMatterActionDensity_constantGauge_invariant
    (groupElement : SU7MotherGroup)
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (jet : DiracExteriorMatterFirstJet) :
    diracExteriorMatterActionDensity geometry
        (constantGaugeTransformMotherConnection groupElement connection)
        (constantGaugeTransformDiracMatterJet groupElement jet) =
      diracExteriorMatterActionDensity geometry connection jet := by
  rw [diracExteriorMatterActionDensity,
    diracExteriorMatterActionDensity,
    diracExteriorMatterKineticVector_constantGauge_covariant]
  simp [constantGaugeTransformDiracMatterJet]

theorem diracExteriorMatterAction_uses_same_motherConnection
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (jet : DiracExteriorMatterFirstJet) :
    diracExteriorMatterActionDensity geometry connection jet =
      ((abs (Matrix.det geometry.coframe) : ℝ) : ℂ) *
        jet.conjugateField
          (Complex.I •
            ∑ coordinate : LorentzianIndex,
              diracMatrixMatterAction
                  (inverseCoframeDiracGamma geometry coordinate)
                (jet.derivative coordinate +
                  diracSpinConnectionMatterAction geometry coordinate jet.field +
                  internalMatterLinearAction
                      (exteriorSpinorMotherIncrement
                        (connection.potential coordinate))
                    jet.field)) := by
  rfl

/-! ## Nonzero action-density regression -/

def identityCoframeMatterGeometry : PointwiseLorentzianCoframeJet where
  coframe := 1
  derivative := 0

def zeroMotherGaugeConnection : SU7MotherGaugeConnection where
  potential := 0
  exteriorDerivative := 0

def diracSpinTwoMatterProbe : DiracExteriorMatterCarrier :=
  fun spinIndex =>
    if spinIndex = 2 then p286HyperchargeMatterProbe else 0

def diracSpinZeroMatterProbe : DiracExteriorMatterCarrier :=
  fun spinIndex =>
    if spinIndex = 0 then p286HyperchargeMatterProbe else 0

def hyperchargeDegreeTwoMatterCoordinate :
    Module.Dual ℂ SU7ExteriorSpinorMatterCarrier where
  toFun matter :=
    (su7ExteriorBasis 2).repr matter.2.1 hyperchargeDegreeTwoIndex
  map_add' first second := by simp
  map_smul' scalar matter := by simp

def diracSpinZeroMatterCoordinate :
    Module.Dual ℂ DiracExteriorMatterCarrier where
  toFun field := hyperchargeDegreeTwoMatterCoordinate (field 0)
  map_add' first second := by simp
  map_smul' scalar field := by simp

def nonzeroKineticMatterJet : DiracExteriorMatterFirstJet where
  field := 0
  derivative := fun direction =>
    if direction = 0 then diracSpinTwoMatterProbe else 0
  conjugateField := diracSpinZeroMatterCoordinate

theorem inverseCoframeDiracGamma_identity
    (coordinate : LorentzianIndex) :
    inverseCoframeDiracGamma identityCoframeMatterGeometry coordinate =
      diracGamma coordinate := by
  fin_cases coordinate <;>
    simp [inverseCoframeDiracGamma, identityCoframeMatterGeometry,
      inv_one, Fin.sum_univ_four]

theorem nonzeroKineticMatterJet_covariantDerivative
    (direction : LorentzianIndex) :
    diracExteriorMatterCovariantDerivative identityCoframeMatterGeometry
        zeroMotherGaugeConnection nonzeroKineticMatterJet direction =
      if direction = 0 then diracSpinTwoMatterProbe else 0 := by
  simp [diracExteriorMatterCovariantDerivative, nonzeroKineticMatterJet,
    diracSpinConnectionMatterAction, motherGaugeMatterAction,
    internalMatterLinearAction, zeroMotherGaugeConnection]
  funext spinIndex
  simp

theorem diracGammaZero_maps_spinTwoProbe :
    diracMatrixMatterAction diracGammaZero diracSpinTwoMatterProbe =
      diracSpinZeroMatterProbe := by
  funext spinIndex
  fin_cases spinIndex <;>
    simp [diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracSpinZeroMatterProbe, diracGammaZero, Fin.sum_univ_four]

theorem nonzeroKineticMatterJet_kineticVector :
    diracExteriorMatterKineticVector identityCoframeMatterGeometry
        zeroMotherGaugeConnection nonzeroKineticMatterJet =
      Complex.I • diracSpinZeroMatterProbe := by
  rw [diracExteriorMatterKineticVector]
  simp only [inverseCoframeDiracGamma_identity,
    nonzeroKineticMatterJet_covariantDerivative, Fin.sum_univ_four]
  simp [diracGamma,
    show (1 : LorentzianIndex) ≠ 0 by decide,
    show (2 : LorentzianIndex) ≠ 0 by decide,
    show (3 : LorentzianIndex) ≠ 0 by decide]
  rw [diracGammaZero_maps_spinTwoProbe]

@[simp] theorem hyperchargeDegreeTwoMatterCoordinate_probe :
    hyperchargeDegreeTwoMatterCoordinate p286HyperchargeMatterProbe = 1 := by
  simp [hyperchargeDegreeTwoMatterCoordinate, p286HyperchargeMatterProbe]

@[simp] theorem diracSpinZeroMatterCoordinate_probe :
    diracSpinZeroMatterCoordinate diracSpinZeroMatterProbe = 1 := by
  simp [diracSpinZeroMatterCoordinate, diracSpinZeroMatterProbe]

/-- Positive regression: the pointwise action density is not definitionally
or theorem-wise forced to zero. -/
theorem nonzeroKineticMatterJet_actionDensity :
    diracExteriorMatterActionDensity identityCoframeMatterGeometry
        zeroMotherGaugeConnection nonzeroKineticMatterJet = Complex.I := by
  rw [diracExteriorMatterActionDensity,
    nonzeroKineticMatterJet_kineticVector]
  simp [identityCoframeMatterGeometry, nonzeroKineticMatterJet]

end
end SaturationMonoid.PhysicsCore.DiracExteriorMatterAction
