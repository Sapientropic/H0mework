import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Unit.Authority
import H0mework.Realization.Audit.DebtFirstWrite
import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Registered

/-! The original raw Fock occurrence owns the actual first mathematical
step and the complete born source before its authority is emitted. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission

open SourceOperationEffects DebtActivationWorld DebtActivationLedger
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock

namespace Joint
export RootGeneratedDebtActivationJointSource.Unit
  (World JointV Current source emitted ledgerSource patch patch_destination targetCurrent
    authoritySource authoritativeRoot originalOccurrence MathReadout mathReadout)
end Joint

noncomputable section

variable (runtime : LivingRuntimeState process)

abbrev registered := SourcePhysicalCalculationRegistered.registered runtime

def initialCurrent : Joint.Current (registered runtime) := (Joint.source (registered runtime)).initial

def initialOccurrence := Joint.emitted (registered runtime) (initialCurrent runtime)

def initialPatch := Joint.patch (registered runtime) (initialCurrent runtime)

def stepEvent : DebtAdmissionFirstWrite.SourceFixedDebtAdmissionEventAt
    (SourcePhysicalCalculationRegistered.worldLaw runtime) (SourcePhysicalCalculation.initial runtime) :=
  .ofStep (SourcePhysicalCalculation.firstStep runtime).2

def birth := DebtAdmissionFirstWrite.generate
  (N := CanonicalUnitArithmeticRoot.N) (SourcePhysicalCalculation.baseCurrent runtime) (stepEvent runtime)

theorem source_environment : (registered runtime).input.environment =
    SourcePhysicalCalculation.rawEnvironment runtime := rfl

theorem source_expression : (registered runtime).input.expression = SourcePhysicalCalculation.rawExpression := rfl

theorem step_target : (stepEvent runtime).target = SourcePhysicalCalculation.paidState runtime := rfl

theorem initial_support :
    (Joint.source (registered runtime)).toRootSource.account.supportOf (initialOccurrence runtime) =
      (SourcePhysicalCalculation.baseCurrent runtime, some (SourcePhysicalCalculation.initial runtime)) := rfl

theorem original_initial_occurrence :
    Joint.originalOccurrence (registered runtime) (initialOccurrence runtime) = runtime.emittedOccurrence :=
  canonicalOccurrence_unique _ _

theorem initial_patch_destination :
    (initialPatch runtime).toLedgerWriteEvolution.destination =
      (RootGeneratedDebtActivationJointSource.Unit.wholeEvolution
        (registered runtime) (initialCurrent runtime)).destination :=
  Joint.patch_destination (registered runtime) (initialCurrent runtime)

theorem first_joint_next :
    (Joint.targetCurrent (registered runtime) (initialCurrent runtime)).1 =
      SourcePhysicalCalculation.baseCurrent runtime.tick.next ∧
    (Joint.targetCurrent (registered runtime) (initialCurrent runtime)).2.state =
      SourcePhysicalCalculation.paidState runtime :=
  ⟨SourcePhysicalCalculationRegistered.native_next runtime,
    SourcePhysicalCalculationRegistered.native_next_state runtime⟩

end
end SourcePhysicalCalculationAdmission
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
