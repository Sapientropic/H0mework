import H0mework.Physics.DiracCovariance.Connection

/-!
# Primitive local Spin action for the Dirac-dual form-native root

This is the proof-free source/action-side operator.  It extends the existing
primitive Dirac kinetic action only on the two additional primitive gravity
fields consumed by the form-native root: auxiliary bivector and simplicity
multiplier.  Both follow the already generated Weyl-dual Lorentz
representation.

No curvature, covariant derivative, action-invariance receipt, shell,
stationarity witness, or branch choice is stored by this operator.  Those
quantities must be regenerated from the transformed primitive fields.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeLocalSpinAction

open ProofFreeRicherAnholonomicSource
open StageNineCoframeSpinRepresentation
open StageNineDiracKineticLocalSpinConnection
open StageNineDiracKineticSpinJurisdiction
open StageNineGlobalBundle
open StageNineHolonomicField
open StageNinePhysicalBivectorSpinRepresentation
open StageNineSpinMatterBundle

open scoped MatrixGroups

noncomputable section

set_option autoImplicit false

/-- Complete primitive local Spin write for the repaired form-native root.
Derived jets remain absent from this carrier by construction. -/
def localSpinDiracDualFormNativeAction
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { localSpinDiracKineticAction spinField configuration with
      gravityAuxiliary := fun point =>
        spinLorentzPhysicalBivectorRepresentation
          (spinWeylDual (spinField point))
          (configuration.gravityAuxiliary point)
      gravitySimplicityMultiplier := fun point =>
        spinLorentzPhysicalBivectorRepresentation
          (spinWeylDual (spinField point))
          (configuration.gravitySimplicityMultiplier point) }

@[simp] theorem localSpinDiracDualFormNativeAction_coframe
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (localSpinDiracDualFormNativeAction spinField configuration).coframe point =
      spinLorentzCoframeRepresentation
        (spinWeylDual (spinField point)) (configuration.coframe point) :=
  rfl

@[simp] theorem localSpinDiracDualFormNativeAction_gravityConnection
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration) :
    (localSpinDiracDualFormNativeAction spinField configuration).gravityConnection =
      (localSpinDiracKineticAction spinField configuration).gravityConnection :=
  rfl

@[simp] theorem localSpinDiracDualFormNativeAction_gravityAuxiliary
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (localSpinDiracDualFormNativeAction spinField configuration).gravityAuxiliary
        point =
      spinLorentzPhysicalBivectorRepresentation
        (spinWeylDual (spinField point))
        (configuration.gravityAuxiliary point) :=
  rfl

@[simp] theorem localSpinDiracDualFormNativeAction_gravitySimplicityMultiplier
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (localSpinDiracDualFormNativeAction spinField configuration).gravitySimplicityMultiplier
        point =
      spinLorentzPhysicalBivectorRepresentation
        (spinWeylDual (spinField point))
        (configuration.gravitySimplicityMultiplier point) :=
  rfl

@[simp] theorem localSpinDiracDualFormNativeAction_gaugeConnection
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration) :
    (localSpinDiracDualFormNativeAction spinField configuration).gaugeConnection =
      configuration.gaugeConnection :=
  rfl

@[simp] theorem localSpinDiracDualFormNativeAction_gaugeAuxiliary
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration) :
    (localSpinDiracDualFormNativeAction spinField configuration).gaugeAuxiliary =
      configuration.gaugeAuxiliary :=
  rfl

@[simp] theorem localSpinDiracDualFormNativeAction_scalar
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration) :
    (localSpinDiracDualFormNativeAction spinField configuration).scalar =
      configuration.scalar :=
  rfl

@[simp] theorem localSpinDiracDualFormNativeAction_matter
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (localSpinDiracDualFormNativeAction spinField configuration).matter point =
      spinDiracMatterRepresentation (spinField point)
        (configuration.matter point) :=
  rfl

@[simp] theorem localSpinDiracDualFormNativeAction_conjugateMatter
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (localSpinDiracDualFormNativeAction spinField configuration).conjugateMatter
        point =
      (configuration.conjugateMatter point).comp
        (spinDiracMatterRepresentation ((spinField point)⁻¹)) :=
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeLocalSpinAction
