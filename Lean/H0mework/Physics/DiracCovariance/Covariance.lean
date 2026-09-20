import H0mework.Physics.DiracCovariance.MaurerLift

/-!
# Complete local Spin covariance of the primitive Dirac derivative

The same primitive smooth `SL(2,ℂ)` field generates the finite matter
action, the Weyl-dual Lorentz connection write, and its Dirac Maurer lift.
Combining those actual producers proves

`D'_mu (S(g) psi) = S(g) (D_mu psi)`.

No transformed matter jet, connection derivative, lift, covariance receipt,
or zero-residual witness is supplied independently.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracKineticLocalSpinCovariance

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineDiracKineticLocalSpinConnection
open StageNineDiracKineticLocalSpinDifferential
open StageNineDiracKineticLocalSpinLiftCovariance
open StageNineDiracKineticLocalSpinMaurerLift
open StageNineDiracKineticSpinJurisdiction
open StageNineDiracMatterCoordinateCalculus
open StageNineGlobalBundle
open StageNineHolonomicField
open StageNineSpinMatterBundle
open SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra

open scoped ContDiff MatrixGroups Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

@[simp] theorem spinDiracMatterRepresentation_apply
    (groupElement : SpinPlus13)
    (matter : DiracExteriorMatterCarrier) :
    spinDiracMatterRepresentation groupElement matter =
      diracMatrixMatterAction (spinDiracMatrix groupElement) matter :=
  rfl

/-- The primitive connection write is exactly its generated homogeneous
transport minus the generated right Maurer connection. -/
theorem localSpinGravityConnectionAction_eq_homogeneous_sub_maurer
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (localSpinDiracKineticAction spinField configuration).gravityConnection
        point =
      spinWeylDualHomogeneousLorentzConnection (spinField point)
          (configuration.gravityConnection point) -
        localSpinWeylDualMaurerConnection spinField point := by
  ext direction internalOut internalIn
  rfl

/-- The Dirac lift of the actual transformed connection has the complete
finite-homogeneous plus derivative-generated inhomogeneous form. -/
theorem diracSpinConnectionLift_localSpinGravityConnectionAction
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (point : BasePoint) (direction : LorentzianIndex)
    (connectionSkew :
      LorentzSkew (configuration.gravityConnection point)) :
    diracSpinConnectionLift
        ((localSpinDiracKineticAction spinField configuration).gravityConnection
          point) direction =
      spinDiracMatrix (spinField point) *
            diracSpinConnectionLift
              (configuration.gravityConnection point) direction *
          spinDiracMatrix (spinField point)⁻¹ -
        localSpinDiracMatrixDerivative spinField point direction *
          spinDiracMatrix (spinField point)⁻¹ := by
  rw [localSpinGravityConnectionAction_eq_homogeneous_sub_maurer]
  change
    diracSpinConnectionLiftLinear direction
        (spinWeylDualHomogeneousLorentzConnection (spinField point)
            (configuration.gravityConnection point) -
          localSpinWeylDualMaurerConnection spinField point) = _
  rw [map_sub]
  simp only [diracSpinConnectionLiftLinear_apply]
  rw [diracSpinConnectionLift_spinWeylDualHomogeneous_covariant
      (spinField point) (configuration.gravityConnection point)
      connectionSkew direction,
    diracSpinConnectionLift_localSpinWeylDualMaurerConnection
      spinField spinSmooth point direction]

/-- Cancelling the actual inverse finite Spin matrix inside the faithful
Dirac action. -/
theorem diracMatrixMatterAction_mul_spinInverse_cancel
    (left : DiracMatrix) (groupElement : SpinPlus13)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction
        (left * spinDiracMatrix groupElement⁻¹)
        (spinDiracMatterRepresentation groupElement matter) =
      diracMatrixMatterAction left matter := by
  change
    diracMatrixMatterAction
        (left * spinDiracMatrix groupElement⁻¹)
        (diracMatrixMatterAction (spinDiracMatrix groupElement) matter) = _
  calc
    _ = diracMatrixMatterAction
        ((left * spinDiracMatrix groupElement⁻¹) *
          spinDiracMatrix groupElement) matter := by
      exact (LinearMap.congr_fun
        (diracMatrixMatterAction_mul
          (left * spinDiracMatrix groupElement⁻¹)
          (spinDiracMatrix groupElement)) matter).symm
    _ = diracMatrixMatterAction left matter := by
      have inverseProduct :
          spinDiracMatrix groupElement⁻¹ *
              spinDiracMatrix groupElement = (1 : DiracMatrix) := by
        rw [← spinDiracMatrix_mul]
        simp
      rw [Matrix.mul_assoc, inverseProduct, Matrix.mul_one]

/-- The infinitesimal mother action commutes with the actual finite Spin
action because the two act on independent tensor factors. -/
theorem diracExteriorMotherLieAction_spinDiracMatter_commutes
    (motherMatrix : SU7MotherLieMatrix)
    (groupElement : SpinPlus13)
    (matter : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction motherMatrix
        (spinDiracMatterRepresentation groupElement matter) =
      spinDiracMatterRepresentation groupElement
        (diracExteriorMotherLieAction motherMatrix matter) := by
  change
    internalMatterLinearAction (exteriorSpinorMotherLieAction motherMatrix)
        (diracMatrixMatterAction (spinDiracMatrix groupElement) matter) =
      diracMatrixMatterAction (spinDiracMatrix groupElement)
        (internalMatterLinearAction
          (exteriorSpinorMotherLieAction motherMatrix) matter)
  exact (LinearMap.congr_fun
    (diracMatrixMatterAction_commutes_internal
      (spinDiracMatrix groupElement)
      (exteriorSpinorMotherLieAction motherMatrix)) matter).symm

/-- Complete generic covariance of the actual primitive matter covariant
derivative under an arbitrary smooth local Spin field.  Every term on both
sides is computed from the same configuration, local action, and point. -/
theorem holonomicMatterCovariantDerivative_localSpin_covariant
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (matterSmooth : ContDiff ℝ ∞ fun candidate =>
      matterCoordinateEquiv (configuration.matter candidate))
    (point : BasePoint) (direction : LorentzianIndex)
    (connectionSkew :
      LorentzSkew (configuration.gravityConnection point)) :
    holonomicMatterCovariantDerivative
        (localSpinDiracKineticAction spinField configuration) point direction =
      spinDiracMatterRepresentation (spinField point)
        (holonomicMatterCovariantDerivative configuration point direction) := by
  unfold holonomicMatterCovariantDerivative
  simp only [localSpinDiracKineticAction_matter]
  change
    matterCoordinateEquiv.symm
          (fieldDirectionalDerivative
            (fun candidate =>
              matterCoordinateEquiv
                (spinDiracMatterRepresentation (spinField candidate)
                  (configuration.matter candidate))) point direction) +
        diracMatrixMatterAction
          (diracSpinConnectionLift
            ((localSpinDiracKineticAction spinField configuration).gravityConnection
              point) direction)
          (spinDiracMatterRepresentation (spinField point)
            (configuration.matter point)) +
      diracExteriorMotherLieAction
        (p286LieBlockEmbed (configuration.gaugeConnection point direction))
        (spinDiracMatterRepresentation (spinField point)
          (configuration.matter point)) =
      spinDiracMatterRepresentation (spinField point)
        (matterCoordinateEquiv.symm
            (fieldDirectionalDerivative
              (fun candidate => matterCoordinateEquiv
                (configuration.matter candidate)) point direction) +
          diracMatrixMatterAction
            (diracSpinConnectionLift
              (configuration.gravityConnection point) direction)
            (configuration.matter point) +
          diracExteriorMotherLieAction
            (p286LieBlockEmbed (configuration.gaugeConnection point direction))
            (configuration.matter point))
  rw [fieldDirectionalDerivative_localSpinMatterAction
      spinField configuration.matter spinSmooth matterSmooth point direction,
    diracSpinConnectionLift_localSpinGravityConnectionAction
      spinField configuration spinSmooth point direction connectionSkew,
    diracMatrixMatterAction_sub_matrix,
    diracMatrixMatterAction_mul_spinInverse_cancel,
    diracMatrixMatterAction_mul_spinInverse_cancel,
    diracExteriorMotherLieAction_spinDiracMatter_commutes]
  rw [diracMatrixMatterAction_mul]
  simp only [LinearMap.comp_apply, map_add,
    spinDiracMatterRepresentation_apply]
  abel

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracKineticLocalSpinCovariance
