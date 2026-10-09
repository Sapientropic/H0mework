import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Runtime.Facade

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open FiniteContinuation
open Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
noncomputable section

theorem first_same_current : readCurrent afterFirst=sourceMaterial := rfl

theorem first_same_visit : afterFirst.current.visit=FiniteContinuation.Runtime.afterFirst.current.visit := rfl

theorem native_tick_preserved (runtime : LivingRuntimeState process) : runtime.tick.structuralKind=.nativeWrite := rfl

theorem work_is_paid (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .work)) ∧
    (readWork runtime).receiverBeforeJoule-(readWork runtime).receiverAfterJoule=(readWork runtime).debitJoule ∧
    (readWork runtime).bodyAfterJoule-(readWork runtime).bodyBeforeJoule=(readWork runtime).debitJoule ∧
    0 < (readWork runtime).debitJoule ∧ 0 < (readWork runtime).elapsedSecond :=
  ⟨face_factorizes runtime _,(certificate_read runtime).2.work⟩

theorem actual_next_account (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    wholeAccountJoule (readCurrent runtime.tick.next)=wholeAccountJoule (readCurrent runtime) :=
  ⟨(certificate_read runtime).1,(certificate_read runtime).2.account⟩

theorem actual_work_integral (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    energyJoule*(readCurrent runtime.tick.next).body.resource.momentum-energyJoule*(readCurrent runtime).body.resource.momentum=
      (∫ second in (0 : ℝ)..segmentSeconds, receiverPower (readCurrent runtime) .enter second)+
      (∫ second in (0 : ℝ)..segmentSeconds, receiverPower (readCurrent runtime) .drive second)+
      (∫ second in (0 : ℝ)..segmentSeconds, receiverPower (readCurrent runtime) .leave second) :=
  ⟨(certificate_read runtime).1,(certificate_read runtime).2.receiverUpdate⟩

theorem actual_momentum_integral (runtime : LivingRuntimeState process) (i : Coordinate) :
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    momentumSI*((readCurrent runtime.tick.next).body.frame.momentum i.1 i.2 : ℝ)-
      momentumSI*((readCurrent runtime).body.frame.momentum i.1 i.2 : ℝ)=
      (∫ second in (0 : ℝ)..segmentSeconds, forceNewton (readCurrent runtime) .enter second i)+
      (∫ second in (0 : ℝ)..segmentSeconds, forceNewton (readCurrent runtime) .drive second i)+
      (∫ second in (0 : ℝ)..segmentSeconds, forceNewton (readCurrent runtime) .leave second i) :=
  ⟨(certificate_read runtime).1,(certificate_read runtime).2.momentumUpdate i⟩

theorem actual_engine_residual (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    (engineHartreeJouleQ : ℝ)*(((readCurrent runtime.tick.next).body.frame.total : ℝ)-((readCurrent runtime).body.frame.total : ℝ))=
      (readWork runtime).debitJoule+engineEnergyResidual*
        (((readCurrent runtime.tick.next).body.frame.total : ℝ)-((readCurrent runtime).body.frame.total : ℝ)) :=
  ⟨(certificate_read runtime).1,(certificate_read runtime).2.engineWork⟩

theorem whole_ledger_installed (runtime : LivingRuntimeState process) :
    facade.readoutAt runtime (.component .work)=
      (.inl ⟨PUnit.unit,(ParentLedger.ledgerCompiler.compile runtime.emittedOccurrence,workOf (readCurrent runtime))⟩ :
        SourceNativeProjectionFiberAt projectionLaw .work runtime.emittedOccurrence) := rfl

theorem actual_history_account (depth : Nat) :
    type_of% (history_factorizes depth) ∧
    wholeAccountJoule (readCurrent (atDepth depth))=wholeAccountJoule initialMaterial := by
  refine ⟨history_factorizes depth,?_⟩
  induction depth with
  | zero => rfl
  | succ depth prior => rw [depth_succ,(actual_next_account (atDepth depth)).2,prior]

theorem actual_original_history (depth : Nat) :
    type_of% (history_factorizes depth) ∧
    wholeAccountJoule (readCurrent (atDepth depth))=
      energyJoule*(Live.entropyProduction Live.initial+Live.freeEnergy Live.initial+Live.measurementWork Live.initial+
        responseWork receivedState+responseWork received+Weak.pulseWork Weak.origin+
        Extract.pulseWork Weak.execution+responseWork Replenish.origin+
        (Reentry.Source.stepReadout.nuclear.target.total : ℝ)-(Reentry.Producer.targetKineticResidual : ℝ)) := by
  refine ⟨history_factorizes depth,?_⟩
  rw [current_history_unchanged]
  exact (original_historical_account_si depth).2

theorem actual_stock_floor (depth : Nat) :
    type_of% (face_factorizes (atDepth depth) (.inherited .current)) ∧
    0 < energyJoule*unreserved initialMaterial ∧
    energyJoule*unreserved initialMaterial < energyJoule*(readCurrent (atDepth depth)).body.resource.momentum := by
  refine ⟨face_factorizes _ _,?_⟩
  rw [current_history_unchanged]
  exact uniform_stock_joule depth

theorem actual_clocks_si (depth : Nat) :
    type_of% (history_factorizes depth) ∧
    ((readCurrent (atDepth depth)).body.resource.quantum.localClock : ℝ)*timeSecond=(22+3*(depth : ℝ))*segmentSeconds ∧
    ((readCurrent (atDepth depth)).body.bodyClock : ℝ)*timeSecond=(7+3*(depth : ℝ))*segmentSeconds := by
  refine ⟨history_factorizes depth,?_⟩
  rw [current_history_unchanged]
  have clocks := FiniteContinuation.Runtime.clocks_at_depth depth
  constructor
  · rw [clocks.1]
    push_cast
    unfold segmentSeconds duration
    ring
  · rw [clocks.2]
    push_cast
    unfold segmentSeconds duration
    ring

structure InstalledSIWork : Prop where
  parent : FiniteContinuation.Runtime.InstalledFiniteContinuation
  first : type_of% first_same_current
  visit : type_of% first_same_visit
  source : type_of% source_and_law_unchanged
  rootCompiler : type_of% rootCompiler_unchanged
  seed : type_of% seed_same_occurrence
  sameNext : type_of% generated_same_next
  native : type_of% native_tick_preserved
  action : type_of% certificate_read
  paid : type_of% work_is_paid
  integral : type_of% actual_work_integral
  momentum : type_of% actual_momentum_integral
  account : type_of% actual_next_account
  engineResidual : type_of% actual_engine_residual
  history : type_of% actual_history_account
  originalHistory : type_of% actual_original_history
  sameHistory : type_of% current_history_unchanged
  stock : type_of% actual_stock_floor
  clocks : type_of% actual_clocks_si
  wholeLedger : type_of% whole_ledger_installed
  inherited : type_of% all_parent_faces
  factorizes : type_of% face_factorizes
  allFaces : Nonempty (Face ≃ Fin 289)

theorem sourceGeneratedSIWork : InstalledSIWork :=
  ⟨FiniteContinuation.Runtime.sourceGeneratedFiniteContinuation,first_same_current,first_same_visit,
   source_and_law_unchanged,rootCompiler_unchanged,seed_same_occurrence,generated_same_next,native_tick_preserved,
   certificate_read,work_is_paid,actual_work_integral,actual_momentum_integral,actual_next_account,actual_engine_residual,
   actual_history_account,actual_original_history,current_history_unchanged,actual_stock_floor,actual_clocks_si,
   whole_ledger_installed,all_parent_faces,face_factorizes,⟨faceEquiv⟩⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SIWork.Runtime
