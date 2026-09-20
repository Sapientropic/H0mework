import H0mework.Physics.MotherProgrammesFormationMatter.ActionMatrix
import H0mework.Physics.MotherProgrammesFormationCoordinates.WholeConsumption

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMatterActions

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineDiracDualFormNativeJointResidualCarrier
open StageNineP286SourceNativeCenteredReducedEntropySafeStep StageNineP286SourceNativeReducedEntropyDescent
open Stage9C.Revision Stage9C.Reduction Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open MotherFamilyOccurrence
open scoped Matrix

noncomputable section

/-- Full operator recovery and its action accompany the occupied 8×8
quantum response of the same source-indexed physical writer. -/
theorem native_consumed (visit : MotherVisit) (sourceData : WholePointFormation.Carrier)
    (value : Carrier) (center : BasePoint) (epoch : ℕ) (point : BasePoint) :
    let ambient := operator value
    let formed := WholePointFormation.source visit sourceData
    let current := GeneralSourceEvolution.stateAt formed center epoch
    let target := GeneralSourceEvolution.stateAt formed center (epoch + 1)
    operatorEquiv.symm ambient = value ∧
      readMatrix ambient = matrix value ∧
      (∀ matter : DiracExteriorMatterCarrier,
        (matterBasis.repr (ambient matter) : Index → ℂ) = matrix value *ᵥ matterBasis.repr matter) ∧
      target = GeneralSourceEvolution.next formed center current ∧
      target.current = p286CartanNext formed current.current current.smooth current.nondegenerate center ∧
      target.current = WholePointFormation.field visit sourceData ∧
      DiracDualFormNativeJointZeroFiber formed target.current ∧
      target.current.coframe point = homogeneousCoframe (sourceClock formed) ∧
      actualRelativeAction formed current.current target.current =
        p286CenteredReducedRelativeAction formed current.current current.smooth current.nondegenerate center ∧
      actualRelativeAction formed current.current target.current = 0 ∧
      target.current.conjugateMatter point (ambient (target.current.matter point)) =
        4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
          (Stage9DEF.Source.restrict target.current point) (Stage9DEF.Compatibility.responseMatrix ambient) :=
  ⟨operatorEquiv.symm_apply_apply value, operator_matrix value, actual_action value,
    (WholePointFormation.native_consumed visit sourceData center epoch point (operator value)).2.2.2⟩

/-- This current-prefix consumer has no operator or operator-coordinate
input: all entries of its full ambient action come from the same mother visit. -/
theorem finite_native_consumed (visit : MotherVisit) (sourceData : WholePointFormation.Carrier)
    (center : BasePoint) (epoch : ℕ) (point : BasePoint) :
    let ambient := operatorAt visit
    let formed := WholePointFormation.source visit sourceData
    let current := GeneralSourceEvolution.stateAt formed center epoch
    let target := GeneralSourceEvolution.stateAt formed center (epoch + 1)
    (∀ row column : Index, ∀ part : Fin 2,
      temporalDepth (MotherCoordinateCompletion.sample coordinateCount visit
        (address (row, column, part))).history ≤ temporalDepth visit.history) ∧
      operatorEquiv.symm ambient = finiteData visit ∧
      readMatrix ambient = matrix (finiteData visit) ∧
      (∀ matter : DiracExteriorMatterCarrier,
        (matterBasis.repr (ambient matter) : Index → ℂ) =
          matrix (finiteData visit) *ᵥ matterBasis.repr matter) ∧
      target = GeneralSourceEvolution.next formed center current ∧
      target.current = p286CartanNext formed current.current current.smooth current.nondegenerate center ∧
      target.current = WholePointFormation.field visit sourceData ∧
      DiracDualFormNativeJointZeroFiber formed target.current ∧
      target.current.coframe point = homogeneousCoframe (sourceClock formed) ∧
      actualRelativeAction formed current.current target.current =
        p286CenteredReducedRelativeAction formed current.current current.smooth current.nondegenerate center ∧
      actualRelativeAction formed current.current target.current = 0 ∧
      target.current.conjugateMatter point (ambient (target.current.matter point)) =
        4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
          (Stage9DEF.Source.restrict target.current point) (Stage9DEF.Compatibility.responseMatrix ambient) :=
  ⟨finite_samples_are_past visit, native_consumed visit sourceData (finiteData visit) center epoch point⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMatterActions
