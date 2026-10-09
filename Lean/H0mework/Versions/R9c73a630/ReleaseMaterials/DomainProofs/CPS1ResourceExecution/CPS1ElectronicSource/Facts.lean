import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Consumer

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section
open CPS1ResourceExecution
variable {frame : CPS1Recycling.Frame}

def GoodStock (stock : Stock frame) : Prop :=
  ∀ state, Species.quantum state ∈ stock → CPS1ElectronicEvolution.Consumer.Good state

def NoGuardStock (stock : Stock frame) : Prop :=
  (∀ failure, Species.guard failure ∉ stock) ∧ Species.missingCarrier ∉ stock

theorem prepare_good (joint : CPS1EnzymeBath.Joint.State frame) (state : State frame)
    (actual : State.fromJoint? frame joint = .ok state) : CPS1ElectronicEvolution.Consumer.Good state := by
  unfold State.fromJoint? at actual
  cases gathered : Geometry.fromJoint? frame joint with
  | error failure =>
    rw [gathered] at actual
    change (Except.error failure : Except Failure (State frame)) = .ok state at actual
    cases actual
  | ok geometry =>
    rw [gathered] at actual
    exact CPS1ElectronicEvolution.Consumer.source_capture geometry state actual

theorem quantum_report_same (state next : State frame) (address : CPS1AtomicDynamics.Charged.Address)
    (row : CPS1AtomicDynamics.Body.Row) (actual : quantumReport? state address row = .ok next) :
    next = state := by
  unfold quantumReport? at actual
  cases reported : CPS1EnzymeBath.Joint.report? frame state.geometry.originJoint address row with
  | error failure => simp [reported] at actual
  | ok joint =>
    simp only [reported] at actual
    split at actual
    · exact (Except.ok.inj actual).symm
    · cases actual

theorem reaction_products_good (reaction : Reaction frame) (input : GoodStock (reaction.reactants frame)) :
    GoodStock (reaction.products frame) := by
  intro state member
  cases reaction with
  | prepare joint =>
    cases prepared : State.fromJoint? frame joint with
    | error failure => simp [Reaction.products,prepared] at member
    | ok next =>
      simp only [Reaction.products,prepared,List.mem_singleton,Species.quantum.injEq] at member
      subst state
      exact prepare_good joint next prepared
  | quantumReport before address row =>
    have generated := input before (by simp [Reaction.reactants])
    cases reported : quantumReport? before address row with
    | error failure => simp [Reaction.products,reported] at member
    | ok next =>
      simp only [Reaction.products,reported,List.mem_singleton,Species.quantum.injEq] at member
      subst state
      simpa only [quantum_report_same before next address row reported] using generated
  | quantumDeposit before amount =>
    have generated := input before (by simp [Reaction.reactants])
    cases deposited : before.deposit? amount with
    | error failure => simp [Reaction.products,deposited] at member
    | ok next =>
      simp only [Reaction.products,deposited,List.mem_singleton,Species.quantum.injEq] at member
      subst state
      exact CPS1ElectronicEvolution.Consumer.actual_deposit before next amount deposited generated
  | quantumPulse before time =>
    have generated := input before (by simp [Reaction.reactants])
    cases pulsed : before.pulse? time with
    | error failure => simp [Reaction.products,pulsed] at member
    | ok next =>
      simp [Reaction.products,pulsed] at member
      subst state
      exact CPS1ElectronicEvolution.Consumer.actual_pulse before next time pulsed generated
  | keepQuantum before =>
    simp only [Reaction.products,List.mem_singleton,Species.quantum.injEq] at member
    subst state
    exact input before (by simp [Reaction.reactants])
  | jointAttach joint kind => simp [Reaction.products] at member
  | jointReport joint address row =>
    cases reported : CPS1EnzymeBath.Joint.report? frame joint address row <;>
      simp [Reaction.products,reported] at member
  | jointDeposit joint amount =>
    cases deposited : CPS1EnzymeBath.Joint.deposit? frame joint amount <;>
      simp [Reaction.products,deposited] at member
  | jointPulse joint time =>
    cases pulsed : jointPulse? frame joint time <;> simp [Reaction.products,pulsed] at member
  | requireCarrier => simp [Reaction.products] at member

theorem reaction_products_noGuard (reaction : Reaction frame) : NoGuardStock (reaction.products frame) := by
  cases reaction <;> simp [Reaction.products,NoGuardStock]
  all_goals split <;> simp_all

theorem lift_material_safe (old : CPS1EnzymeBath.Species frame) :
    GoodStock [Source.liftMaterial frame old] ∧ NoGuardStock [Source.liftMaterial frame old] := by
  cases old <;> simp [Source.liftMaterial,GoodStock,NoGuardStock]

theorem raw_material_safe (action : Source.RawAction) :
    GoodStock (action.material frame) ∧ NoGuardStock (action.material frame) := by
  cases action with
  | old action =>
    cases action <;> simp [Source.RawAction.material,CPS1EnzymeBath.Source.RawAction.material,
      Source.liftMaterial,GoodStock,NoGuardStock]
  | _ => simp [Source.RawAction.material,GoodStock,NoGuardStock]

theorem goodStock_of_subset {left right : Stock frame}
    (contained : ∀ species ∈ right, species ∈ left) (generated : GoodStock left) : GoodStock right :=
  fun state member => generated state (contained _ member)

theorem noGuardStock_of_subset {left right : Stock frame}
    (contained : ∀ species ∈ right, species ∈ left) (generated : NoGuardStock left) : NoGuardStock right := by
  constructor
  · intro failure member
    exact generated.1 failure (contained _ member)
  · intro member
    exact generated.2 (contained _ member)

theorem goodStock_append {left right : Stock frame} (a : GoodStock left) (b : GoodStock right) :
    GoodStock (left ++ right) := by
  intro state member
  exact (List.mem_append.mp member).elim (a state) (b state)

theorem noGuardStock_append {left right : Stock frame} (a : NoGuardStock left) (b : NoGuardStock right) :
    NoGuardStock (left ++ right) := by
  constructor
  · intro failure member
    exact (List.mem_append.mp member).elim (a.1 failure) (b.1 failure)
  · intro member
    exact (List.mem_append.mp member).elim a.2 b.2

theorem lifted_stock_safe (old : CPS1EnzymeBath.Stock frame) :
    GoodStock (old.map (Source.liftMaterial frame)) ∧ NoGuardStock (old.map (Source.liftMaterial frame)) := by
  induction old with
  | nil => simp [GoodStock,NoGuardStock]
  | cons species rest ih =>
    exact ⟨goodStock_append (lift_material_safe species).1 ih.1,
      noGuardStock_append (lift_material_safe species).2 ih.2⟩

theorem raw_actions_safe (actions : List Source.RawAction) :
    GoodStock (actions.flatMap (Source.RawAction.material frame)) ∧
      NoGuardStock (actions.flatMap (Source.RawAction.material frame)) := by
  induction actions with
  | nil => simp [GoodStock,NoGuardStock]
  | cons action rest ih =>
    exact ⟨goodStock_append (raw_material_safe action).1 ih.1,
      noGuardStock_append (raw_material_safe action).2 ih.2⟩

theorem component_feed_safe (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    GoodStock (feed.map (fun kind => Species.retained (CPS1EnzymeBath.componentSpecies frame kind))) ∧
      NoGuardStock (feed.map (fun kind => Species.retained (CPS1EnzymeBath.componentSpecies frame kind))) := by
  induction feed with
  | nil => simp [GoodStock,NoGuardStock]
  | cons kind rest ih =>
    have single : GoodStock [Species.retained (CPS1EnzymeBath.componentSpecies frame kind)] ∧
        NoGuardStock [Species.retained (CPS1EnzymeBath.componentSpecies frame kind)] := by
      simp [GoodStock,NoGuardStock]
    exact ⟨goodStock_append single.1 ih.1,noGuardStock_append single.2 ih.2⟩

theorem fire_safe (reaction : Reaction frame) (stock next : Stock frame)
    (actual : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock = .ok next)
    (good : GoodStock stock) (unguarded : NoGuardStock stock) : GoodStock next ∧ NoGuardStock next := by
  unfold Inventory.fire at actual
  cases consumed : Inventory.consume (reaction.reactants frame) stock with
  | error missing => simp [consumed] at actual
  | ok remainder =>
    simp only [consumed,Except.ok.injEq] at actual
    subst next
    have inventory := Inventory.consume_perm _ _ _ consumed
    have requiredSubset : ∀ species ∈ reaction.reactants frame, species ∈ stock :=
      fun species member => inventory.mem_iff.mpr (List.mem_append.mpr (Or.inl member))
    have remainderSubset : ∀ species ∈ remainder, species ∈ stock :=
      fun species member => inventory.mem_iff.mpr (List.mem_append.mpr (Or.inr member))
    exact ⟨goodStock_append (reaction_products_good reaction (goodStock_of_subset requiredSubset good))
        (goodStock_of_subset remainderSubset good),
      noGuardStock_append (reaction_products_noGuard reaction) (noGuardStock_of_subset remainderSubset unguarded)⟩

theorem execute_safe (program : List (Reaction frame)) (stock : Stock frame)
    (good : GoodStock stock) (unguarded : NoGuardStock stock) :
    GoodStock (execute frame program stock).stock ∧ NoGuardStock (execute frame program stock).stock := by
  induction program generalizing stock with
  | nil => exact ⟨good,unguarded⟩
  | cons reaction rest ih =>
    cases action : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock with
    | error missing => simpa only [execute,Inventory.execute,action] using And.intro good unguarded
    | ok next =>
      have step := fire_safe reaction stock next action good unguarded
      simpa only [execute,Inventory.execute,action] using ih next step.1 step.2

theorem start_safe (frame : CPS1Recycling.Frame) (previous : CPS1EnzymeBath.Source.Occurrence frame) :
    GoodStock (Source.start frame previous).stock ∧ NoGuardStock (Source.start frame previous).stock := by
  dsimp only [Source.start]
  exact execute_safe _ _ (lifted_stock_safe previous.current.stock).1 (lifted_stock_safe previous.current.stock).2

theorem advance_safe (frame : CPS1Recycling.Frame) (cursor : Source.Cursor frame)
    (actions : List Source.RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind)
    (good : GoodStock cursor.stock) (unguarded : NoGuardStock cursor.stock) :
    GoodStock (Source.advance frame cursor actions feed).stock ∧
      NoGuardStock (Source.advance frame cursor actions feed).stock := by
  have provided := component_feed_safe (frame := frame) feed
  have raw := raw_actions_safe (frame := frame) actions
  dsimp only [Source.advance]
  exact execute_safe _ _ (goodStock_append (goodStock_append good provided.1) raw.1)
    (noGuardStock_append (noGuardStock_append unguarded provided.2) raw.2)

theorem fromActual_safe (frame : CPS1Recycling.Frame) (previous : CPS1EnzymeBath.Source.Occurrence frame) :
    GoodStock (Source.fromActual frame previous).current.stock ∧
      NoGuardStock (Source.fromActual frame previous).current.stock := start_safe frame previous

theorem generated_stage_safe (frame : CPS1Recycling.Frame) (previous : CPS1EnzymeBath.Source.Occurrence frame)
    (actions : List Source.RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    GoodStock (Source.advance frame (Source.start frame previous) actions feed).stock ∧
      NoGuardStock (Source.advance frame (Source.start frame previous) actions feed).stock :=
  advance_safe frame _ actions feed (start_safe frame previous).1 (start_safe frame previous).2

theorem resume_safe (frame : CPS1Recycling.Frame) (current : Source.Occurrence frame)
    (actions : List Source.RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind)
    (good : GoodStock current.current.stock) (unguarded : NoGuardStock current.current.stock) :
    GoodStock (Source.resume frame current actions feed).current.stock ∧
      NoGuardStock (Source.resume frame current actions feed).current.stock :=
  advance_safe frame current.current actions feed good unguarded

theorem generated_stage_quantum_good (frame : CPS1Recycling.Frame)
    (previous : CPS1EnzymeBath.Source.Occurrence frame) (actions : List Source.RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) (state : State frame)
    (member : Species.quantum state ∈ (Source.advance frame (Source.start frame previous) actions feed).stock) :
    CPS1ElectronicEvolution.Consumer.Good state :=
  (generated_stage_safe frame previous actions feed).1 state member

theorem whole_inventory (frame : CPS1Recycling.Frame) (program : List (Reaction frame))
    (stock : Stock frame) (species : Species frame) :
    stock.count species + (Inventory.credit (Reaction.products frame)
      (execute frame program stock).fired).count species =
    (execute frame program stock).stock.count species +
      (Inventory.debit (Reaction.reactants frame) (execute frame program stock).fired).count species :=
  Inventory.execution_balance _ _ _ _ _

theorem whole_potential (frame : CPS1Recycling.Frame) (program : List (Reaction frame))
    (stock : Stock frame) (measure : Species frame → ℚ) :
    Inventory.value measure stock = Inventory.value measure (execute frame program stock).stock +
      Inventory.affinity measure (Reaction.reactants frame) (Reaction.products frame)
        (execute frame program stock).fired := Inventory.execution_potential _ _ _ _ _

theorem actual_cut (frame : CPS1Recycling.Frame) (program : List (Reaction frame))
    (stock : Stock frame) (missing : Species frame) (cut : (execute frame program stock).missing = some missing) :
    ∃ reaction rest, (execute frame program stock).remaining = reaction :: rest ∧
      (execute frame program stock).stock.count missing < (reaction.reactants frame).count missing :=
  Inventory.execution_cut _ _ _ _ _ cut

def ReactionFailure (reaction : Reaction frame) (failure : Failure) : Prop :=
  match reaction with
  | .prepare joint => State.fromJoint? frame joint = .error failure
  | .jointReport joint address row =>
      (CPS1EnzymeBath.Joint.report? frame joint address row).mapError Failure.body = .error failure
  | .jointDeposit joint amount =>
      (CPS1EnzymeBath.Joint.deposit? frame joint amount).mapError Failure.body = .error failure
  | .jointPulse joint time => jointPulse? frame joint time = .error failure
  | .quantumReport state address row => quantumReport? state address row = .error failure
  | .quantumDeposit state amount => state.deposit? amount = .error failure
  | .quantumPulse state time => state.pulse? time = .error failure
  | _ => False

theorem reaction_guard_failure (reaction : Reaction frame) (failure : Failure)
    (member : Species.guard failure ∈ reaction.reactants frame) : ReactionFailure reaction failure := by
  cases reaction <;> simp [Reaction.reactants,ReactionFailure,guards] at member ⊢
  all_goals split at member <;> simp_all

theorem true_guard_cut (frame : CPS1Recycling.Frame) (program : List (Reaction frame))
    (stock : Stock frame) (failure : Failure)
    (cut : (execute frame program stock).missing = some (.guard failure)) :
    ∃ reaction rest, (execute frame program stock).remaining = reaction :: rest ∧
      ReactionFailure reaction failure ∧
      (execute frame program stock).stock.count (.guard failure) <
        (reaction.reactants frame).count (.guard failure) := by
  rcases actual_cut frame program stock (.guard failure) cut with ⟨reaction,rest,remaining,shortage⟩
  have positive : 0 < (reaction.reactants frame).count (.guard failure) :=
    (Nat.zero_le _).trans_lt shortage
  exact ⟨reaction,rest,remaining,reaction_guard_failure reaction failure (List.count_pos_iff.mp positive),shortage⟩

theorem reaction_missingCarrier (reaction : Reaction frame)
    (member : Species.missingCarrier ∈ reaction.reactants frame) : reaction = .requireCarrier := by
  cases reaction <;> simp [Reaction.reactants,guards] at member ⊢
  all_goals split at member <;> simp_all

theorem legacy_requireCarrier_cut (frame : CPS1Recycling.Frame) (program : List (Reaction frame))
    (stock : Stock frame) (cut : (execute frame program stock).missing = some .missingCarrier) :
    ∃ rest, (execute frame program stock).remaining = Reaction.requireCarrier :: rest := by
  rcases actual_cut frame program stock .missingCarrier cut with ⟨reaction,rest,remaining,shortage⟩
  have positive : 0 < (reaction.reactants frame).count Species.missingCarrier :=
    (Nat.zero_le _).trans_lt shortage
  have required := reaction_missingCarrier reaction (List.count_pos_iff.mp positive)
  subst reaction
  exact ⟨rest,remaining⟩

end
end CPS1ElectronicSource
