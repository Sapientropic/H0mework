/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M11.BoundaryFailureRegression

/-!
# M11 whole-program sink

One certificate consumes the generated crossing fold, topology, flow and
boundary readouts; the fixed cross-season observer; the pre-emitter actual
maintenance debit; the actual two-event settled-service count; the canonical
failing boundary lineage; and the existing living-root whole-ledger next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M11WholeProgramRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Capacity Space CrossingCost

structure M11WholeProgramCertificate where
  socialSpace :
    M11GeneratedSocialSpaceRegression.GeneratedSocialSpaceConsumerCertificate
  aprilResidualClassNonempty :
    Regression.Society.M11.Empirical.CitiBike.aprilResiduals ≠ []
  februaryResidualClassNonempty :
    Regression.Society.M11.Empirical.CitiBike.februaryResiduals ≠ []
  maintenance : SourceInstalledBoundaryMaintenanceAt
    M11BoundaryMaintenanceRegression.installedRenewal
  maintenance_eq : maintenance = M11BoundaryMaintenanceRegression.maintenance
  maintenanceConsumer : BoundaryMaintenanceConsumerAt maintenance
  exactBoundaryDebitRootConsumer :
    M11BoundaryMaintenanceRegression.consumer.certificate =
        M11BoundaryMaintenanceRegression.firstBoundaryCertificate ∧
      M11BoundaryMaintenanceRegression.consumer.exactCrossing =
        M11BoundaryMaintenanceRegression.firstCrossing ∧
      M11BoundaryMaintenanceRegression.consumer.actualDebit =
        M10OccurrenceCapacityDebitedRunFixture.firstDebit ∧
      M11BoundaryMaintenanceRegression.consumer.debitedRun.length = 1 ∧
      M11BoundaryMaintenanceRegression.maintenance.restriction.edge.target.slots[
        M11BoundaryMaintenanceRegression.consumer.actualDebit.slot]? =
          some (.live
            M11BoundaryMaintenanceRegression.consumer.boundaryStanding) ∧
      M11BoundaryMaintenanceRegression.installedRenewal.RootAnswerAndNextFactorizes ∧
      M11BoundaryMaintenanceRegression.consumer.generatedNext =
        M11BoundaryMaintenanceRegression.root.generatedNextCurrentAt
          M11BoundaryMaintenanceRegression.visit
  boundaryFailure :
    M11BoundaryFailureRegression.BoundaryFailureWholeCertificate
  actualSettledCount :
    M11BoundaryFailureRegression.actualAnomieSettlement.actualResidualSettled = 2
  maintenanceDebtCount :
    maintenanceDebt
      (phase := M11BoundaryFailureRegression.maintenanceAnomiePhase) = 3
  exactWholeLedgerWriteBack :
    SourceNativeLedgerEvolutionAt
      M11BoundaryMaintenanceRegression.root.toAuthoritativeRoot.toLedgerRoot.source.source
      (M11BoundaryMaintenanceRegression.root.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          M11BoundaryMaintenanceRegression.visit).occurrence
  generatedNext :
    maintenance.generatedNext =
      M11BoundaryMaintenanceRegression.root.generatedNextCurrentAt
        M11BoundaryMaintenanceRegression.visit

def m11WholeProgramConsumer : M11WholeProgramCertificate where
  socialSpace :=
    M11GeneratedSocialSpaceRegression.generatedSocialSpaceDirectConsumer
  aprilResidualClassNonempty :=
    Regression.Society.M11.Empirical.CitiBike.april_residual_class_nonempty
  februaryResidualClassNonempty :=
    Regression.Society.M11.Empirical.CitiBike.february_residual_class_nonempty
  maintenance := M11BoundaryMaintenanceRegression.maintenance
  maintenance_eq := rfl
  maintenanceConsumer := M11BoundaryMaintenanceRegression.consumer
  exactBoundaryDebitRootConsumer :=
    M11BoundaryMaintenanceRegression.exact_boundary_debit_whole_root_consumer
  boundaryFailure :=
    M11BoundaryFailureRegression.boundaryFailureWholeConsumer
  actualSettledCount :=
    M11BoundaryFailureRegression.actualResidualSettled_eq_two
  maintenanceDebtCount :=
    M11BoundaryFailureRegression.maintenanceDebt_eq_three
  exactWholeLedgerWriteBack :=
    M11BoundaryMaintenanceRegression.exactWholeLedgerWriteBack
  generatedNext :=
    M11BoundaryMaintenanceRegression.local_run_reads_only_root_generated_next.1

end
end M11WholeProgramRegression
end Society
end ProcessGame
end SaturationMonoid
