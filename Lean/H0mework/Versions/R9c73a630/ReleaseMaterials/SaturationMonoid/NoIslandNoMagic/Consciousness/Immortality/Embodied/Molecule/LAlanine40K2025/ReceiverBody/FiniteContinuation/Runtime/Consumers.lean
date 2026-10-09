import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime.Runtime

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open Thermal.Recovery.Reservoir Thermal.Recovery.Reservoir.Pointer
open Thermal.Recovery.Reservoir.Pointer.Feedback
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
noncomputable section

def faceSumEquiv : Projection ≃ Fin 8 ⊕ FiniteActuation.Runtime.Projection where
  toFun := fun face => match face with
    | .current => .inl 0 | .next => .inl 1 | .clocks => .inl 2 | .actuation => .inl 3
    | .account => .inl 4 | .capacity => .inl 5 | .realization => .inl 6 | .wholeLedger => .inl 7
    | .parent face => .inr face
  invFun := fun index => match index with
    | .inl i => ![.current,.next,.clocks,.actuation,.account,.capacity,.realization,.wholeLedger] i
    | .inr face => .parent face
  left_inv := by intro face; cases face <;> rfl
  right_inv := by
    intro index
    rcases index with i | face
    · fin_cases i <;> rfl
    · rfl

def faceEquiv : Projection ≃ Fin 287 :=
  faceSumEquiv.trans ((Equiv.sumCongr (Equiv.refl _) FiniteActuation.Runtime.faceEquiv).trans finSumFinEquiv)

def wholeAccount (current : Material) : ℝ :=
  Live.freeEnergy current.body.resource.quantum+Live.entropyProduction current.body.resource.quantum+
    Extract.Port.kinetic current.body.resource.momentum+(current.body.frame.total : ℝ)

theorem actual_account (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime .account) ∧
    wholeAccount (readCurrent runtime.tick.next)=wholeAccount (readCurrent runtime) := by
  refine ⟨face_factorizes runtime .account,?_⟩
  rcases facade.readoutAt runtime .account with ⟨_,delivered⟩ | inactive
  · exact delivered.down
  · exact PEmpty.elim inactive

theorem actual_capacity (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime .capacity) ∧
    unreserved (readCurrent runtime)<unreserved (readCurrent runtime.tick.next) := by
  refine ⟨face_factorizes runtime .capacity,?_⟩
  rcases facade.readoutAt runtime .capacity with ⟨_,delivered⟩ | inactive
  · exact delivered.2.down
  · exact PEmpty.elim inactive

theorem actual_integrated_update (runtime : LivingRuntimeState process) (i : Coordinate) :
    type_of% (face_factorizes runtime .actuation) ∧
    ((readCurrent runtime.tick.next).body.frame.momentum i.1 i.2 : ℝ)-
      ((readCurrent runtime).body.frame.momentum i.1 i.2 : ℝ)=
      (∫ t in (0 : ℝ)..duration, nuclearForce (readCurrent runtime) .enter t i)+
      (∫ t in (0 : ℝ)..duration, nuclearForce (readCurrent runtime) .drive t i)+
      (∫ t in (0 : ℝ)..duration, nuclearForce (readCurrent runtime) .leave t i) :=
  ⟨(action_certificate runtime).1,(action_certificate runtime).2.momentumUpdate i⟩

theorem actual_receiver_update (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime .actuation) ∧
    (readCurrent runtime.tick.next).body.resource.momentum-(readCurrent runtime).body.resource.momentum=
      (∫ t in (0 : ℝ)..duration, receiverForce (readCurrent runtime) .enter t)+
      (∫ t in (0 : ℝ)..duration, receiverForce (readCurrent runtime) .drive t)+
      (∫ t in (0 : ℝ)..duration, receiverForce (readCurrent runtime) .leave t) :=
  ⟨(action_certificate runtime).1,(action_certificate runtime).2.receiverUpdate⟩

theorem actual_change (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime .actuation) ∧
    (readCurrent runtime.tick.next).body.frame.momentum ≠ (readCurrent runtime).body.frame.momentum ∧
    (readCurrent runtime.tick.next).body.resource.momentum < (readCurrent runtime).body.resource.momentum :=
  ⟨(action_certificate runtime).1,(action_certificate runtime).2.actualChange,
    next_receiver_decreases _ (current_admissible runtime)⟩

theorem actual_residual_flow (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime .realization) ∧
    type_of% (gamma_residual_retained (readCurrent runtime) (current_admissible runtime)) := by
  refine ⟨face_factorizes runtime .realization,?_⟩
  rcases facade.readoutAt runtime .realization with ⟨_,delivered⟩ | inactive
  · exact delivered.down
  · exact PEmpty.elim inactive

-- Every induction step consumes the same installed action and its canonical next.
theorem account_at_depth (depth : Nat) :
    type_of% (history_factorizes depth) ∧
    wholeAccount (readCurrent (atDepth depth))=wholeAccount initialMaterial := by
  refine ⟨history_factorizes depth,?_⟩
  induction depth with
  | zero => rfl
  | succ depth prior =>
      rw [depth_succ,(actual_account (atDepth depth)).2,prior]

theorem unreserved_at_depth (depth : Nat) :
    type_of% (history_factorizes depth) ∧
    unreserved initialMaterial ≤ unreserved (readCurrent (atDepth depth)) := by
  refine ⟨history_factorizes depth,?_⟩
  induction depth with
  | zero => exact le_refl _
  | succ depth prior =>
      rw [depth_succ]
      exact prior.trans (actual_capacity (atDepth depth)).2.le

theorem uniform_positive_stock (depth : Nat) :
    type_of% (face_factorizes (atDepth depth) .current) ∧
    0 < unreserved initialMaterial ∧
    unreserved initialMaterial < (readCurrent (atDepth depth)).body.resource.momentum := by
  refine ⟨face_factorizes (atDepth depth) .current,unreserved_positive _ initial_admissible,?_⟩
  have reserve : (0 : ℝ)<((readCurrent (atDepth depth)).reserve : ℝ) :=
    Rat.cast_pos.mpr (current_admissible (atDepth depth)).positiveReserve
  have below := (unreserved_at_depth depth).2
  unfold unreserved at below ⊢
  linarith only [reserve,below]

theorem reserve_at_depth (depth : Nat) :
    (readCurrent (atDepth depth)).reserve=initialMaterial.reserve/(2 : ℚ)^depth := by
  induction depth with
  | zero => change initialMaterial.reserve=initialMaterial.reserve/(2 : ℚ)^0; simp
  | succ depth prior =>
      rw [depth_succ,next_current]
      change (readCurrent (atDepth depth)).reserve/2=_
      rw [prior,pow_succ,div_div]

theorem complete_historical_account (depth : Nat) :
    type_of% (history_factorizes depth) ∧
    wholeAccount (readCurrent (atDepth depth))=
    Live.entropyProduction Live.initial+Live.freeEnergy Live.initial+Live.measurementWork Live.initial+
      responseWork receivedState+responseWork received+Weak.pulseWork Weak.origin+
      Extract.pulseWork Weak.execution+responseWork Replenish.origin+
      (Reentry.Source.stepReadout.nuclear.target.total : ℝ)-(Reentry.Producer.targetKineticResidual : ℝ) := by
  refine ⟨history_factorizes depth,?_⟩
  rw [(account_at_depth depth).2]
  exact FiniteActuation.complete_historical_account

theorem retained_configuration (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime .current) ∧
    (readCurrent runtime).body.frame.position=sourceBody.frame.position ∧
    (readCurrent runtime).body.frame.force=sourceBody.frame.force ∧
    (readCurrent runtime).body.frame.potential=sourceBody.frame.potential ∧
    (readCurrent runtime).body.held=sourceBody.held ∧
    (readCurrent runtime).body.realized=sourceBody.realized ∧
    (readCurrent runtime).body.inheritedResidual=sourceBody.inheritedResidual ∧
    (readCurrent runtime).body.newNumericalResidual=sourceBody.newNumericalResidual := by
  have valid := current_admissible runtime
  exact ⟨face_factorizes runtime .current,valid.position,valid.force,valid.potential,
    valid.held,valid.realized,valid.inheritedResidual,valid.newNumericalResidual⟩

theorem next_is_not_transport (runtime : LivingRuntimeState process) : readCurrent runtime.tick.next ≠ readCurrent runtime := by
  intro same
  exact (actual_change runtime).2.1 (congrArg (fun material : Material => material.body.frame.momentum) same)

structure InstalledFiniteContinuation : Prop where
  parent : FiniteActuation.Runtime.InstalledFiniteActuation
  input : type_of% input_is_parent
  answer : type_of% generated_action_answer
  next : type_of% generated_action_next
  visit : type_of% generated_visit
  first : type_of% first_generated
  native : type_of% native_every_tick
  actions : type_of% action_certificate
  integrated : type_of% actual_integrated_update
  receiver : type_of% actual_receiver_update
  change : type_of% actual_change
  capacity : type_of% actual_capacity
  positive : type_of% uniform_positive_stock
  reserve : type_of% reserve_at_depth
  clocks : type_of% clocks_at_depth
  account : type_of% account_at_depth
  historical : type_of% complete_historical_account
  retained : type_of% retained_configuration
  residuals : type_of% actual_residual_flow
  materialHistory : type_of% history_factorizes
  factorization : type_of% face_factorizes
  inherited : type_of% parent_is_installed
  wholeLedger : type_of% whole_ledger_installed
  noTransport : type_of% next_is_not_transport
  allFaces : Nonempty (Projection ≃ Fin 287)

theorem sourceGeneratedFiniteContinuation : InstalledFiniteContinuation :=
  ⟨FiniteActuation.Runtime.sourceGeneratedFiniteActuation,input_is_parent,
    generated_action_answer,generated_action_next,generated_visit,first_generated,native_every_tick,
    action_certificate,actual_integrated_update,actual_receiver_update,actual_change,actual_capacity,
    uniform_positive_stock,reserve_at_depth,clocks_at_depth,account_at_depth,complete_historical_account,
    retained_configuration,actual_residual_flow,history_factorizes,face_factorizes,parent_is_installed,
    whole_ledger_installed,next_is_not_transport,⟨faceEquiv⟩⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime
