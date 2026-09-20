import H0mework.Physics.Cartan.CartanAffineConnectionActualization
import H0mework.Physics.Cartan.CartanTorsionThreeFormEquiv
import H0mework.Physics.CartanAction.CartanConnectionLocalActualLift

/-!
# Faithful zero fiber of the Lorentz connection action on `II+`

At a nondegenerate coframe, the action-facing three-form
`omega · II+(e)` retains every Lorentz-skew connection coordinate.  The proof
factors the literal exterior action through the existing Cartan equivalences

`Lorentz contorsion <-> Cartan torsion <-> star_I (T wedge e)`.

This is a kinematic zero-fiber theorem.  It consumes no source, residual,
target connection, or equation receipt and produces no field update.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineLorentzConnectionExteriorActionZeroFiber

open ProofFreeRicherAnholonomicSource
open PointwiseDiracSpinConnectionLift
open StageNineCartanAffineConnectionActualization
open StageNineCartanContorsionTorsionEquiv
open StageNineCartanTangentSimplicityResponse
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCartanTorsionThreeFormEquiv
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineFormNativeLorentzGeometricKinematics
open StageNineLorentzConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private def zeroDerivativeCoframeJet
    (coframe : LorentzianCoframe) : PointwiseLorentzianCoframeJet where
  coframe := coframe
  derivative := 0

private theorem physicalIIPlusCoframeTangent_zero
    (coframe : LorentzianCoframe) :
    physicalIIPlusCoframeTangent coframe 0 = 0 := by
  funext internalPair spacetimePair
  fin_cases internalPair <;>
    simp [physicalIIPlusCoframeTangent, internalBivectorDual,
      coframeWedgeTangent, lorentzianCoframeHodge]

/-- The six lowered coordinates reconstruct any actual Lorentz-skew
connection, including its diagonal zero coordinates and metric signs. -/
theorem connection_eq_lorentzSkewConnectionOfLowered
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection) :
    connection =
      lorentzSkewConnectionOfBivectorOneForm
        (fun direction pair =>
          loweredLorentzConnectionCoefficient connection direction pair) := by
  funext direction internalOut internalIn
  have skewAt := connectionSkew direction
  have skewCoordinate := congrFun (congrFun skewAt internalOut) internalIn
  fin_cases internalOut <;> fin_cases internalIn <;>
    simp [spinConnectionMatrix, minkowskiInternalMetric,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzConnectionCoefficient,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      lorentzBivectorFirst, lorentzBivectorSecond,
      pairFirst, pairSecond,
      minkowskiInternalSign, Matrix.mul_apply,
      Fin.sum_univ_four, Fin.sum_univ_six] at skewCoordinate ⊢ <;>
    linarith

private theorem lorentzSkew_sub
    {first second : PointwiseLorentzSpinConnection}
    (firstSkew : LorentzSkew first)
    (secondSkew : LorentzSkew second) :
    LorentzSkew (first - second) := by
  intro direction
  have firstAt := firstSkew direction
  have secondAt := secondSkew direction
  rw [show spinConnectionMatrix (first - second) direction =
      spinConnectionMatrix first direction -
        spinConnectionMatrix second direction by
    ext internalOut internalIn
    rfl]
  rw [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
  ext internalOut internalIn
  have firstEntry := congrFun (congrFun firstAt internalOut) internalIn
  have secondEntry := congrFun (congrFun secondAt internalOut) internalIn
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply]
    at firstEntry secondEntry ⊢
  linarith

private def intrinsicContorsionCoordinates
    (jet : PointwiseLorentzianCoframeJet)
    (connection : PointwiseLorentzSpinConnection) : LorentzBivectorOneForm :=
  fun direction pair =>
    loweredLorentzConnectionCoefficient
      (connection - jet.lorentzSpinConnection) direction pair

private theorem connection_eq_cartanAffineSpinConnection_intrinsic
    (jet : PointwiseLorentzianCoframeJet)
    (nondegenerate : Matrix.det jet.coframe ≠ 0)
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection) :
    connection = cartanAffineSpinConnection jet
      (intrinsicContorsionCoordinates jet connection) := by
  have differenceSkew :
      LorentzSkew (connection - jet.lorentzSpinConnection) :=
    lorentzSkew_sub connectionSkew
      (jet.lorentzSpinConnection_lorentzSkew nondegenerate)
  calc
    connection = jet.lorentzSpinConnection +
        (connection - jet.lorentzSpinConnection) := by abel
    _ = jet.lorentzSpinConnection +
        lorentzSkewConnectionOfBivectorOneForm
          (intrinsicContorsionCoordinates jet connection) := by
      rw [connection_eq_lorentzSkewConnectionOfLowered
        (connection - jet.lorentzSpinConnection) differenceSkew]
      rfl
    _ = cartanAffineSpinConnection jet
        (intrinsicContorsionCoordinates jet connection) := rfl

/-- At a nondegenerate coframe jet, literal Cartan torsion is a faithful
readout of the complete Lorentz-skew connection. -/
theorem actualPointwiseCartanTorsionTwoForm_injective_on_lorentzSkew
    (jet : PointwiseLorentzianCoframeJet)
    (nondegenerate : Matrix.det jet.coframe ≠ 0)
    (first second : PointwiseLorentzSpinConnection)
    (firstSkew : LorentzSkew first)
    (secondSkew : LorentzSkew second)
    (torsionEqual :
      actualPointwiseCartanTorsionTwoForm jet first =
        actualPointwiseCartanTorsionTwoForm jet second) :
    first = second := by
  rw [connection_eq_cartanAffineSpinConnection_intrinsic jet nondegenerate
      first firstSkew,
    connection_eq_cartanAffineSpinConnection_intrinsic jet nondegenerate
      second secondSkew] at torsionEqual ⊢
  rw [actualPointwiseCartanTorsionTwoForm_cartanAffineSpinConnection
      jet nondegenerate,
    actualPointwiseCartanTorsionTwoForm_cartanAffineSpinConnection
      jet nondegenerate] at torsionEqual
  have coordinatesEqual :=
    (cartanContorsionTorsionLinearEquiv jet.coframe
      nondegenerate).injective torsionEqual
  rw [coordinatesEqual]

/-- The literal connection action on `II+` is the existing action-facing
Cartan three-form of the zero-derivative coframe jet. -/
theorem connectionExteriorAction_physicalIIPlus_eq_cartanTorsionThreeForm
    (coframe : LorentzianCoframe)
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection) :
    pointwisePhysicalBivectorConnectionExteriorAction connection
        (physicalIIPlusBivector coframe) =
      cartanTorsionThreeForm coframe
        (actualPointwiseCartanTorsionTwoForm
          (zeroDerivativeCoframeJet coframe) connection) := by
  rw [cartanTorsionThreeForm_actualPointwiseCartanTorsionTwoForm]
  calc
    pointwisePhysicalBivectorConnectionExteriorAction connection
        (physicalIIPlusBivector coframe) =
      pointwisePhysicalBivectorExteriorCovariantDerivative connection
        (pointwisePhysicalIIPlusJet (zeroDerivativeCoframeJet coframe)) := by
          funext internalPair triple
          simp only [pointwisePhysicalBivectorConnectionExteriorAction,
            pointwisePhysicalBivectorExteriorCovariantDerivative,
            pointwisePhysicalBivectorCovariantDerivative,
            pointwisePhysicalIIPlusJet, zeroDerivativeCoframeJet,
            Pi.zero_apply, zero_add]
          rw [show (fun _ _ => (0 : ℝ)) = (0 : LorentzianCoframe) by rfl,
            physicalIIPlusCoframeTangent_zero]
          simp
    _ = internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm coframe
            (pointwiseCartanTorsion (zeroDerivativeCoframeJet coframe)
              connection)) := by
          simpa [zeroDerivativeCoframeJet] using
            (pointwisePhysicalIIPlus_exteriorCovariantDerivative_eq_torsionCoframe
              (zeroDerivativeCoframeJet coframe) connection connectionSkew)

private theorem actualZeroTorsion_eq_cartanTorsionOfLowered
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection) :
    actualPointwiseCartanTorsionTwoForm
        (zeroDerivativeCoframeJet coframe) connection =
      cartanTorsionOfContorsion coframe
        (fun direction pair =>
          loweredLorentzConnectionCoefficient connection direction pair) := by
  let coordinates : LorentzBivectorOneForm := fun direction pair =>
    loweredLorentzConnectionCoefficient connection direction pair
  calc
    actualPointwiseCartanTorsionTwoForm
        (zeroDerivativeCoframeJet coframe) connection =
      actualPointwiseCartanTorsionTwoForm
        (zeroDerivativeCoframeJet coframe)
        (lorentzSkewConnectionOfBivectorOneForm coordinates) := by
          rw [← connection_eq_lorentzSkewConnectionOfLowered connection
            connectionSkew]
    _ = actualCartanTorsionIncrementTwoForm coframe coordinates := rfl
    _ = cartanTorsionOfContorsion coframe coordinates :=
      actualCartanTorsionIncrementTwoForm_eq_factored coframe nondegenerate _

/-- Faithful zero fiber: on the Lorentz-skew domain and at a nondegenerate
coframe, the complete connection is zero exactly when its action on `II+`
is zero. -/
theorem pointwisePhysicalBivectorConnectionExteriorAction_physicalIIPlus_eq_zero_iff
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (connection : PointwiseLorentzSpinConnection)
    (connectionSkew : LorentzSkew connection) :
    pointwisePhysicalBivectorConnectionExteriorAction connection
        (physicalIIPlusBivector coframe) = 0 ↔
      connection = 0 := by
  rw [connectionExteriorAction_physicalIIPlus_eq_cartanTorsionThreeForm
    coframe connection connectionSkew]
  rw [cartanTorsionThreeForm_eq_zero_iff coframe nondegenerate]
  rw [actualZeroTorsion_eq_cartanTorsionOfLowered coframe nondegenerate
    connection connectionSkew]
  let coordinates : LorentzBivectorOneForm := fun direction pair =>
    loweredLorentzConnectionCoefficient connection direction pair
  change
    (cartanContorsionTorsionLinearEquiv coframe nondegenerate coordinates = 0) ↔
      connection = 0
  rw [(cartanContorsionTorsionLinearEquiv coframe nondegenerate).map_eq_zero_iff]
  constructor
  · intro coordinatesZero
    rw [connection_eq_lorentzSkewConnectionOfLowered connection connectionSkew,
      show (fun direction pair =>
        loweredLorentzConnectionCoefficient connection direction pair) = 0
        from coordinatesZero]
    funext direction internalOut internalIn
    simp [lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix]
  · intro connectionZero
    subst connection
    funext direction pair
    dsimp [coordinates]
    simp [loweredLorentzConnectionCoefficient]

end

end
  SaturationMonoid.PhysicsCore.StageNineLorentzConnectionExteriorActionZeroFiber
