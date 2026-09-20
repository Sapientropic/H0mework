import H0mework.Physics.DualVariation.P286CanonicalJointActionProducerCore
import H0mework.Physics.FixedJoint.FixedP286CanonicalJointActionWrite
import H0mework.Physics.ConstitutiveAction.SpatialSectionOperator

/-!
# Fixed P506/L0 recentered canonical P286 section producer

At every source-owned spatial occurrence, this module feeds the already
generated fixed P506/L0 final common local actual into the canonical
Dirac-dual form-native P286 producer.  The resulting contact family is then
assembled into one four-dimensional holonomic configuration by the existing
time-axis diagonal.

The construction is source/action first: neither a residual value nor its
support is an input.  The existing fixed-origin canonical actual is recovered
definitionally at spatial contact zero.  Whole-action-jet naturality of the
diagonal is intentionally left as the next acceptance theorem.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionProducer

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000

/-- The fixed final-common action input recentered at one source-owned spatial
occurrence. -/
def fixedP506L0P286CanonicalRecenteredContactInput
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  fixedP506L0FinalCommonActionActual space

/-- Canonical mother-action response at one recentered occurrence. -/
def fixedP506L0P286CanonicalRecenteredContactActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalGeneratedActual positiveSmoothUnifiedSource
    (fixedP506L0P286CanonicalRecenteredContactInput space)

/-- One global four-dimensional actual assembled from the complete
source-owned contact family. -/
def fixedP506L0P286CanonicalRecenteredSectionActual :
    StageNineHolonomicConfiguration :=
  spatialContactTimeAxisDiagonal
    fixedP506L0P286CanonicalRecenteredContactActual

/-- The recentered producer genuinely extends the already certified
fixed-origin canonical write. -/
theorem fixedP506L0P286CanonicalRecenteredContactActual_zero :
    fixedP506L0P286CanonicalRecenteredContactActual 0 =
      fixedP506L0P286CanonicalGeneratedActual :=
  rfl

@[simp] theorem fixedP506L0P286CanonicalRecenteredSectionActual_coframe_slice
    (time : ℝ) (space : StageNineSpatialPoint) :
    fixedP506L0P286CanonicalRecenteredSectionActual.coframe
        (canonicalCauchySlicePoint time space) =
      (fixedP506L0P286CanonicalRecenteredContactActual space).coframe
        (canonicalCauchySlicePoint time 0) := by
  simp [fixedP506L0P286CanonicalRecenteredSectionActual,
    spatialContactTimeAxisDiagonal]

@[simp] theorem
    fixedP506L0P286CanonicalRecenteredSectionActual_gaugeConnection_slice
    (time : ℝ) (space : StageNineSpatialPoint) :
    fixedP506L0P286CanonicalRecenteredSectionActual.gaugeConnection
        (canonicalCauchySlicePoint time space) =
      (fixedP506L0P286CanonicalRecenteredContactActual space).gaugeConnection
        (canonicalCauchySlicePoint time 0) := by
  simp [fixedP506L0P286CanonicalRecenteredSectionActual,
    spatialContactTimeAxisDiagonal]

@[simp] theorem
    fixedP506L0P286CanonicalRecenteredSectionActual_gaugeAuxiliary_slice
    (time : ℝ) (space : StageNineSpatialPoint) :
    fixedP506L0P286CanonicalRecenteredSectionActual.gaugeAuxiliary
        (canonicalCauchySlicePoint time space) =
      (fixedP506L0P286CanonicalRecenteredContactActual space).gaugeAuxiliary
        (canonicalCauchySlicePoint time 0) := by
  simp [fixedP506L0P286CanonicalRecenteredSectionActual,
    spatialContactTimeAxisDiagonal]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionProducer
