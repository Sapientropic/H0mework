import H0mework.Versions.R2.Physics.Actual.RuntimeEnergyFace
import H0mework.Versions.R2.Physics.Actual.HistoryRuntime

/-! The named runtime consumes the source-rooted uniqueness key at its
exact weak inquiry and retains the same full classical field and native next. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Runtime

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision
open StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineCClassicalWorldAcceptance

noncomputable section

def uniquenessTick := physicalInquiryRuntime.tickAt 8

theorem uniquenessTick_resolution : uniquenessTick.resolution =
    .directlyAnswered (weakFace 2) (weakConsumer 2) := rfl

theorem uniquenessTick_answer : uniquenessTick.answer = Weak.canonical := rfl

def activatedConfiguration :=
  materialConfiguration (SpinPair.support (SpinPair.visit 2).current)

theorem activatedConfiguration_eq_firstWrite :
    activatedConfiguration = History.configuration 7 :=
  (History.configuration_add_seven_eq_runtime 1).symm.trans
    (History.configuration_add_seven_eq_firstWrite 1)

theorem activatedConfiguration_classicalWorldAcceptance :
    ClassicalWorldAcceptance positiveSmoothUnifiedSource activatedConfiguration := by
  rw [activatedConfiguration_eq_firstWrite]
  exact Stage9C.Material.SpinPair.actual_classicalWorldAcceptance

theorem activatedDensity_reads_whole_configuration :
    Weak.density uniquenessTick.answer =
      Fields.compactCoordinates activatedConfiguration
        activatedConfiguration_classicalWorldAcceptance.smooth := by
  rw [uniquenessTick_answer, Weak.canonical_density]
  have same :
      (⟨History.configuration 7, History.configuration_smooth 7⟩ :
        {configuration : StageNineHolonomicConfiguration // configuration.Smooth}) =
      ⟨activatedConfiguration, activatedConfiguration_classicalWorldAcceptance.smooth⟩ :=
    Subtype.ext activatedConfiguration_eq_firstWrite.symm
  exact congrArg (fun configuration :
      {configuration : StageNineHolonomicConfiguration // configuration.Smooth} ↦
    Fields.compactCoordinates configuration.1 configuration.2) same

theorem candidate_configuration_eq_activated
    {configuration : StageNineHolonomicConfiguration} (smooth : configuration.Smooth)
    (admitted : ∃ candidate : Weak.Candidate,
      Weak.density candidate = Fields.compactCoordinates configuration smooth) :
    configuration = activatedConfiguration :=
  (Weak.configuration_eq_firstWrite_of_candidate smooth admitted).trans
    activatedConfiguration_eq_firstWrite.symm

theorem uniquenessTick_next :
    uniquenessTick.next.node.erase = (SpinPair.readPresentation 2).erase := rfl

def activatedEvent :=
  SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (SpinPair.visit 2)

set_option linter.defProp false in
def activatedClassicalUniqueness :=
  let compilation := (weakPresentation 1).state.generatedCompilation_factorizes PUnit.unit
  let ledger := activatedEvent.wholeLedgerWriteBack_eq
  And.intro sourceRootedUniquenessUnlock
    (And.intro compilation
      (And.intro ledger
        (And.intro activatedDensity_reads_whole_configuration
          (And.intro activatedConfiguration_classicalWorldAcceptance uniquenessTick_next))))

def nineActivations : SourceNativeInquiryRuntime.HistoryAt physicalInquiryRuntime 9
    physicalInquiryRuntime.initialState := physicalInquiryRuntime.run 9

theorem nineActivations_target :
    (physicalInquiryRuntime.stateAt 9).engine.node.erase =
      (SpinPair.readPresentation 2).erase := rfl

end
end SaturationMonoid.PhysicsCore.Stage9CU.Runtime
