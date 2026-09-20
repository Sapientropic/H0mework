import H0mework.Physics.SafeCauchy.FixedJointGlobalDevelopment
import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorP286Readback

/-!
# SafeFinal dynamic scalar source contact

The current Cauchy-safe scalar is a genuine time-dependent source write.  Its
canonical second primitive nevertheless vanishes on the initial Cauchy slice,
so the same generated current meets the source vacuum at every zero-slice
contact, in particular at the canonical origin.

This is the positive S9-C contact producer.  It does not claim that the whole
scalar field is static, and it stores no acceptance, residual, or future
state.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore
namespace StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeDynamicScalarSourceContact

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointCauchySafeScalarTemporalDevelopment
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafePreparedActual

private abbrev Base : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source Prepared

private abbrev SafeFinal : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeJointGlobalActual

private abbrev PriorPath : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev PriorCarry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source PriorPath

private abbrev PriorCoupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source PriorPath

private abbrev FixedCarry : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual

private abbrev Vacuum : ScalarCoordinateCarrier :=
  sourceGeneratedVacuumCoordinates Source

private abbrev SafeScalarProfile : BasePoint → ScalarCoordinateCarrier :=
  completeJointCauchySafeScalarAccelerationProfile Source Base

/-- The current scalar is the source-generated second-primitive write. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_scalar_exactWrite :
    SafeFinal.scalar =
      Base.scalar + canonicalTimeSecondPrimitive SafeScalarProfile :=
  rfl

private theorem base_scalar_eq_priorCoupled :
    Base.scalar = PriorCoupled.scalar :=
  rfl

theorem positive_generatedLocalVacuumCoordinates_zero_eq_constant :
    generatedLocalVacuumCoordinates Source 0 = fun _ => Vacuum := by
  funext point
  rw [generatedLocalVacuumCoordinates, generatedScalarFrame,
    generatedTransition_normalized]
  exact scalarCoordinateAction_one _

/-- The dynamic scalar lands on the same source vacuum at every canonical
initial contact. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_scalar_generatedVacuum_zeroSlice
    (space : StageNineSpatialPoint) :
    SafeFinal.scalar (canonicalCauchySlicePoint 0 space) =
      generatedLocalVacuumCoordinates Source 0
        (canonicalCauchySlicePoint 0 space) := by
  calc
    SafeFinal.scalar (canonicalCauchySlicePoint 0 space) =
        Base.scalar (canonicalCauchySlicePoint 0 space) := by
      rw [congrFun
        fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_scalar_exactWrite
        (canonicalCauchySlicePoint 0 space)]
      simp
    _ = PriorCoupled.scalar (canonicalCauchySlicePoint 0 space) :=
      congrFun base_scalar_eq_priorCoupled (canonicalCauchySlicePoint 0 space)
    _ = PriorCarry.scalar (canonicalCauchySlicePoint 0 space) := by
      exact
        sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
          Source PriorCarry space
    _ = FixedCarry.scalar (canonicalCauchySlicePoint 0 space) := by
      exact congrFun actionSelectedCarry_scalar_eq_u6RadialQuarticCarry
        (canonicalCauchySlicePoint 0 space)
    _ = Vacuum := by
      rw [fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_normalForm]
      simp
    _ = generatedLocalVacuumCoordinates Source 0
        (canonicalCauchySlicePoint 0 space) := by
      rw [positive_generatedLocalVacuumCoordinates_zero_eq_constant]

/-- The exact source contact consumed by the current S9-C key. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_scalar_origin_generatedVacuum :
    SafeFinal.scalar 0 = generatedLocalVacuumCoordinates Source 0 0 := by
  have canonicalSliceZero :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) =
        (0 : BasePoint) := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  rw [← canonicalSliceZero]
  exact
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_scalar_generatedVacuum_zeroSlice
      (0 : StageNineSpatialPoint)

#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_scalar_origin_generatedVacuum

end
end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeDynamicScalarSourceContact
end SaturationMonoid.PhysicsCore
