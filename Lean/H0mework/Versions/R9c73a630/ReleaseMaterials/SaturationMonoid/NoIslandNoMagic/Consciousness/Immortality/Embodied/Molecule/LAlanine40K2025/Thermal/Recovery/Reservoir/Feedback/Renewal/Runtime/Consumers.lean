import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Runtime.Invariants

/-! # Direct consumers of the supplied state, executed state, and retained resource account -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Resource Propagation.Producer
noncomputable section

/-- Read the actual material delivered by the next face of the fixed renewal facade. -/
def readNext (runtime : LivingRuntimeState process) : Live.State :=
  match facade.readoutAt runtime .next with
  | .inl ⟨_, material⟩ => material
  | .inr inactive => PEmpty.elim inactive

theorem read_next_exact (runtime : LivingRuntimeState process) :
    readNext runtime = currentState (nextCurrent runtime.state.current) := rfl

theorem actual_execution_consumer :
    bodyRead (readNext afterFirst).joint =
      Quantum.conjugation (Current.loadPulse (nativeClockStep : ℝ))
        (bodyRead (readNext seed).joint) :=
  renewal_certificate.2.executionBody

theorem actual_execution_remainder :
    donorRemainingOf (suppliedBlock (readNext afterFirst)) + supplyTransfer received =
      donorRemainingOf (suppliedBlock received) :=
  renewal_certificate.2.executionRemainder

theorem actual_execution_donor : donorMatrixOf (bodyRead (readNext afterFirst).joint) =
    Quantum.conjugation (Native.freePCUnitary (nativeClockStep : ℝ))
      (donorMatrixOf (bodyRead (readNext seed).joint)) :=
  renewal_certificate.2.donorMaterial

theorem same_generated_visit : afterFirst.current.visit = generatedAction.target.targetVisit := rfl

theorem clocks : (currentState seed.state.current).localClock = 7 * nativeClockStep ∧
    (readNext seed).localClock = 8 * nativeClockStep ∧
    (readNext afterFirst).localClock = 9 * nativeClockStep :=
  ⟨renewal_certificate.2.inputClock, renewal_certificate.2.supplyClock,
    renewal_certificate.2.executionClock⟩

/-- Installed source and independent consumers share the whole row and both literal nexts. -/
structure InstalledRemainingRenewal : Prop where
  sourceClosure : RemainingRenewalClosure
  allCoverage : ∀ runtime projection, type_of% (face_factorizes runtime projection)
  allInstalled : ∀ runtime projection, type_of% (face_is_installed runtime projection)
  parentRetained : ∀ runtime, type_of% (parent_is_installed runtime)
  fullLedger : ∀ runtime, type_of% (whole_ledger_installed runtime)
  sameParent : type_of% received_is_parent
  actualAction : type_of% first_is_generated
  actualVisit : type_of% same_generated_visit
  literalNext : type_of% generated_action_next
  execution : type_of% actual_execution_consumer
  executionDonor : type_of% actual_execution_donor
  executionRemainder : type_of% actual_execution_remainder
  actualClocks : type_of% clocks
  receiptConsumed : type_of% renewal_certificate
  receiptOnce : ∀ runtime, type_of% (renewal_receipt_not_reissued runtime)
  completeEnergy : ∀ runtime, type_of% (runtime_complete_account runtime)
  completeDebit : ∀ runtime, type_of% (runtime_complete_debit runtime)
  finiteBudget : ∀ runtime, type_of% (runtime_finite_budget runtime)
  allFinite : ∀ depth, type_of% (all_finite_paid depth)

theorem sourceGeneratedRemainingRenewalAtNext : InstalledRemainingRenewal where
  sourceClosure := renewal_certificate.2
  allCoverage := face_factorizes
  allInstalled := face_is_installed
  parentRetained := parent_is_installed
  fullLedger := whole_ledger_installed
  sameParent := received_is_parent
  actualAction := first_is_generated
  actualVisit := same_generated_visit
  literalNext := generated_action_next
  execution := actual_execution_consumer
  executionDonor := actual_execution_donor
  executionRemainder := actual_execution_remainder
  actualClocks := clocks
  receiptConsumed := renewal_certificate
  receiptOnce := renewal_receipt_not_reissued
  completeEnergy := runtime_complete_account
  completeDebit := runtime_complete_debit
  finiteBudget := runtime_finite_budget
  allFinite := all_finite_paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
