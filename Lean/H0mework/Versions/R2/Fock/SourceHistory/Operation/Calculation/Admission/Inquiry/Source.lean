import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Target
import H0mework.Foundation.Inquiry.EmptyObstruction
import H0mework.Versions.R2.Foundation.Runtime.Inquiry

/-! The query coordinates are produced from the registered raw input and the
current source state before either source emitter is installed. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalCalculationAdmission.Inquiry

open SourceOperationEffects RootInquiryCompletion DebtActivationWorld
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

abbrev OldN := CanonicalUnitArithmeticRoot.N
abbrev NewN (runtime : LivingRuntimeState process) := Joint.World (registered runtime)

def oldU7 := RootGeneratedEmptyObstructionU7.producer OldN
  CanonicalUnitArithmeticRoot.rootObstructionAt_isEmpty

def oldCalculus := RootGeneratedEmptyObstructionU7.calculus OldN
  CanonicalUnitArithmeticRoot.rootObstructionAt_isEmpty

private theorem newObstruction_empty (runtime : LivingRuntimeState process) (support : (NewN runtime).Support) :
    IsEmpty ((NewN runtime).ObstructionAt support) := by
  rcases support with ⟨old, state⟩
  constructor
  intro obstruction
  cases obstruction with
  | inl impossible => exact nomatch impossible
  | inr impossible =>
      cases state <;> exact nomatch impossible

def newU7 (runtime : LivingRuntimeState process) :=
  RootGeneratedEmptyObstructionU7.producer (NewN runtime) (newObstruction_empty runtime)

def newCalculus (runtime : LivingRuntimeState process) :=
  RootGeneratedEmptyObstructionU7.calculus (NewN runtime) (newObstruction_empty runtime)

variable (runtime : LivingRuntimeState process)

abbrev OldLedger := Target.sourceRoot.toAuthoritativeRoot.toLedgerRoot.source

abbrev SourceTokenAt {current : CanonicalUnitArithmeticRoot.Current}
    (occurrence : OldLedger.source.toRootSource.actual.OccurrenceAt current) : Type :=
  SourceNativeInquiryCompilationTokenAt (U7 := oldU7) (calculus := oldCalculus)
    (oldTheory := TheoryState.rootSemantic OldN)
    (CanonicalUnitArithmeticRoot.occurrenceLedgerEntry occurrence) PUnit.unit
    (ULift.up.{1, 0} occurrence) .answered (Joint.MathReadout (registered runtime))

def sourceToken {current : CanonicalUnitArithmeticRoot.Current}
    (occurrence : OldLedger.source.toRootSource.actual.OccurrenceAt current) : SourceTokenAt runtime occurrence :=
  .canonical (Joint.mathReadout (registered runtime) (initialCurrent runtime))

def sourceTokenLaw : SourceNativeProjectionLaw OldLedger where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => SourceTokenAt runtime occurrence
  project := fun _ {_current} occurrence _ => sourceToken runtime occurrence

def sourceAuthoritySource := Target.sourceRoot.source.base.withProjectionCoface (sourceTokenLaw runtime)

def sourceRoot : SourceNativeLivingRootClosure OldN CanonicalUnitArithmeticRoot.V :=
  (show SourceNativeAuthoritativeRootClosure OldN CanonicalUnitArithmeticRoot.V from
    { source := sourceAuthoritySource runtime
      emitted := CanonicalUnitArithmeticRoot.emitted
      compiler_commutes := Target.sourceRoot.compiler_commutes }).toLivingWithoutFaithfulTerminal
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

def sourceTokenInstallation : SourceNativeProjectionLaw.InstallationAt
    (sourceTokenLaw runtime) (sourceAuthoritySource runtime).projectionLaw :=
  .componentCoface Target.sourceRoot.source.base (sourceTokenLaw runtime)

def sourceOldInstallation : SourceNativeProjectionLaw.InstallationAt
    Target.sourceRoot.source.base.projectionLaw (sourceAuthoritySource runtime).projectionLaw :=
  .inheritedCoface Target.sourceRoot.source.base (sourceTokenLaw runtime)

abbrev BornLedger := (SourcePhysicalCalculationAdmission.authoritySource runtime).restructuringSource.toLedgerSource

def targetOldTokenLaw : SourceNativeProjectionLaw (BornLedger runtime) where
  Projection := PUnit
  ActiveAt := fun _ {_current} occurrence =>
    (sourceTokenLaw runtime).ActiveAt PUnit.unit (Joint.originalOccurrence (registered runtime) occurrence)
  InactiveAt := fun _ {_current} occurrence =>
    (sourceTokenLaw runtime).InactiveAt PUnit.unit (Joint.originalOccurrence (registered runtime) occurrence)
  classify := fun _ {_current} occurrence =>
    (sourceTokenLaw runtime).classify PUnit.unit (Joint.originalOccurrence (registered runtime) occurrence)
  PayloadAt := fun _ {_current} occurrence active =>
    (sourceTokenLaw runtime).PayloadAt PUnit.unit (Joint.originalOccurrence (registered runtime) occurrence) active
  project := fun _ {_current} occurrence active =>
    (sourceTokenLaw runtime).project PUnit.unit (Joint.originalOccurrence (registered runtime) occurrence) active

def targetOldSource :=
  (SourcePhysicalCalculationAdmission.authoritySource runtime).withProjectionCoface (targetOldTokenLaw runtime)

def mathEntryAt {current : Joint.Current (registered runtime)}
    (occurrence : (Joint.source (registered runtime)).toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt (NewN runtime) ((Joint.source (registered runtime)).toRootSource.account.supportOf occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact RootGeneratedDebtActivationJointSource.Unit.sourceRow (registered runtime) current 1

abbrev MathConsumerTokenAt {current : Joint.Current (registered runtime)}
    (occurrence : (Joint.source (registered runtime)).toRootSource.actual.OccurrenceAt current) : Type :=
  SourceNativeInquiryAnswerConsumerTokenAt PUnit.unit (ULift.up.{1, 0} occurrence)
    (mathEntryAt runtime occurrence) (Joint.mathReadout (registered runtime) current)

def mathConsumerTokenLaw : SourceNativeProjectionLaw (BornLedger runtime) where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => MathConsumerTokenAt runtime occurrence
  project := fun _ {_current} _occurrence _ => .canonical

def targetConsumerSource := (targetOldSource runtime).withProjectionCoface (mathConsumerTokenLaw runtime)

abbrev MathCompilationTokenAt {current : Joint.Current (registered runtime)}
    (occurrence : (Joint.source (registered runtime)).toRootSource.actual.OccurrenceAt current) : Type :=
  SourceNativeInquiryCompilationTokenAt (U7 := newU7 runtime) (calculus := newCalculus runtime)
    (oldTheory := TheoryState.rootSemantic (NewN runtime)) (mathEntryAt runtime occurrence)
    PUnit.unit (ULift.up.{1, 0} occurrence) .answered (Joint.MathReadout (registered runtime))

def mathCompilationTokenLaw : SourceNativeProjectionLaw (BornLedger runtime) where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => MathCompilationTokenAt runtime occurrence
  project := fun _ {current} _occurrence _ => .canonical (Joint.mathReadout (registered runtime) current)

def targetAuthoritySource := (targetConsumerSource runtime).withProjectionCoface (mathCompilationTokenLaw runtime)

def targetRoot : SourceNativeLivingRootClosure (NewN runtime) (Joint.JointV (registered runtime)) :=
  (show SourceNativeAuthoritativeRootClosure (NewN runtime) (Joint.JointV (registered runtime)) from
    { source := targetAuthoritySource runtime
      emitted := Joint.emitted (registered runtime)
      compiler_commutes := (SourcePhysicalCalculationAdmission.livingRoot runtime).compiler_commutes
    }).toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

def targetOldInstallation : SourceNativeProjectionLaw.InstallationAt
    (SourcePhysicalCalculationAdmission.authoritySource runtime).projectionLaw
      (targetAuthoritySource runtime).projectionLaw :=
  ((SourceNativeProjectionLaw.InstallationAt.inheritedCoface (SourcePhysicalCalculationAdmission.authoritySource runtime) (targetOldTokenLaw runtime)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (targetOldSource runtime) (mathConsumerTokenLaw runtime))).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (targetConsumerSource runtime) (mathCompilationTokenLaw runtime))

def targetSourceTokenInstallation : SourceNativeProjectionLaw.InstallationAt
    (targetOldTokenLaw runtime) (targetAuthoritySource runtime).projectionLaw :=
  ((SourceNativeProjectionLaw.InstallationAt.componentCoface (SourcePhysicalCalculationAdmission.authoritySource runtime) (targetOldTokenLaw runtime)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (targetOldSource runtime) (mathConsumerTokenLaw runtime))).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (targetConsumerSource runtime) (mathCompilationTokenLaw runtime))

def targetConsumerInstallation : SourceNativeProjectionLaw.InstallationAt
    (mathConsumerTokenLaw runtime) (targetAuthoritySource runtime).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface (targetOldSource runtime) (mathConsumerTokenLaw runtime)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (targetConsumerSource runtime) (mathCompilationTokenLaw runtime))

def targetCompilationInstallation : SourceNativeProjectionLaw.InstallationAt
    (mathCompilationTokenLaw runtime) (targetAuthoritySource runtime).projectionLaw :=
  .componentCoface (targetConsumerSource runtime) (mathCompilationTokenLaw runtime)

end
end SourcePhysicalCalculationAdmission.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
