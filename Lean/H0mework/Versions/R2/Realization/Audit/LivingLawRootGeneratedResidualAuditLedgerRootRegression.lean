import H0mework.Versions.R2.Realization.Audit.LedgerRoot
import H0mework.Versions.R2.Realization.Audit.LivingLawRootGeneratedResidualWorldCofaceRegression

/-!
# Regression for the residual audit ledger root

The old world has one live row and an empty obstruction vocabulary.  The
audit root adds one residual row, selects only that row in its size-one finite
patch, folds every old row through the identity remainder and emits its exact
target occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedResidualAuditLedgerRegression

open RootGeneratedResidualAdmission
open RootGeneratedResidualAdmissionRegression
open RootGeneratedResidualAuditLedger

abbrev N := RootGeneratedResidualAdmissionRegression.OldN

def oldLiveEntry : OpenResponsibilityAt N () := ⟨(), ()⟩

abbrev root := auditLedgerRoot N () PUnit PUnit.unit

theorem finite_patch_contains_exactly_one_generated_row :
    (auditRows N () PUnit PUnit.unit
      (initialOccurrence N () PUnit)).size = 1 :=
  rfl

theorem finite_patch_is_identity_remainder :
    auditPatch N () PUnit PUnit.unit (initialOccurrence N () PUnit) =
      .identityRemainder
        (auditRows N () PUnit PUnit.unit (initialOccurrence N () PUnit))
        (auditCoverage N () PUnit PUnit.unit
          (initialOccurrence N () PUnit)) :=
  rfl

def generatedResidualRow := residualGeneratedRow N () PUnit PUnit.unit

theorem generated_residual_row_commutes :
    generatedResidualRow.CommutesWithWorld :=
  residualGeneratedRow_commutes_with_world N () PUnit PUnit.unit

theorem inherited_row_is_not_promoted :
    sourceNativeFiniteLedgerPatchGeneratedEntry?
      (auditSource N () PUnit)
      (auditCompiler N () PUnit PUnit.unit).ExactTransitionAt
      (auditCompiler N () PUnit PUnit.unit).writeRowSource
      (auditCompiler N () PUnit PUnit.unit).terminalRowSource
      ((auditCompiler N () PUnit PUnit.unit).compile
        (initialOccurrence N () PUnit))
      ((auditCompiler N () PUnit PUnit.unit).compilePatch
        (initialOccurrence N () PUnit))
      (oldEntry oldLiveEntry) = none :=
  oldEntry_is_identity_remainder N () PUnit PUnit.unit oldLiveEntry

theorem compiler_emits_exact_target :
    (root.generatedLedgerAt (ULift.up false)).CommutesWith root.emitted :=
  root.compiler_commutes (ULift.up false)

theorem audit_next_is_generated :
    (root.toRoot.evolutionAt (ULift.up false)).nextCurrent? =
      some (ULift.up true) :=
  rfl

#print axioms finite_patch_contains_exactly_one_generated_row
#print axioms finite_patch_is_identity_remainder
#print axioms generated_residual_row_commutes
#print axioms inherited_row_is_not_promoted
#print axioms compiler_emits_exact_target
#print axioms audit_next_is_generated

end RootGeneratedResidualAuditLedgerRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
