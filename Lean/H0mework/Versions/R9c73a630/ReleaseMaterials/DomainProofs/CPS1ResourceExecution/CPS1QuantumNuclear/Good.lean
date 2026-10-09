import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Actual

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1QuantumNuclear
noncomputable section
open CPS1ResourceExecution
variable {frame : CPS1Recycling.Frame}

def GoodStock (stock : Stock frame) : Prop :=
  ∀ state, Species.retained (.quantum state) ∈ stock → CPS1ElectronicEvolution.Consumer.Good state

def NoGuardStock (stock : Stock frame) : Prop :=
  (∀ failure, Species.guard failure ∉ stock) ∧
    (∀ failure, Species.retained (.guard failure) ∉ stock) ∧
      Species.retained .missingCarrier ∉ stock

theorem reaction_good (reaction : Reaction frame) (good : GoodStock (reaction.reactants frame)) :
    GoodStock (reaction.products frame) := by
  intro state member
  cases reaction with
  | retained old =>
    have prior : CPS1ElectronicSource.GoodStock (old.reactants frame) := by
      intro state member
      exact good state (List.mem_map.mpr ⟨_,member,rfl⟩)
    apply CPS1ElectronicSource.reaction_products_good old prior state
    rcases List.mem_map.mp member with ⟨species,present,same⟩
    have identified := Species.retained.inj same
    rwa [identified] at present
  | nuclearPulse before time =>
    have prior := good before (by simp [Reaction.reactants])
    cases updated : pulse? before time with
    | error failure => simp [Reaction.products,updated] at member
    | ok next =>
      simp [Reaction.products,updated] at member
      subst state
      exact pulse_good before time next updated prior

theorem good_of_subset {left right : Stock frame} (subset : ∀ species ∈ right, species ∈ left)
    (good : GoodStock left) : GoodStock right := fun state member => good state (subset _ member)

theorem fire_good (reaction : Reaction frame) (stock next : Stock frame)
    (good : GoodStock stock) (actual : Inventory.fire (Reaction.reactants frame) (Reaction.products frame)
      reaction stock = .ok next) : GoodStock next := by
  unfold Inventory.fire at actual
  cases consumed : Inventory.consume (reaction.reactants frame) stock with
  | error missing => simp [consumed] at actual
  | ok remainder =>
    simp only [consumed,Except.ok.injEq] at actual
    subst next
    have decomposition := Inventory.consume_perm _ _ _ consumed
    have input : GoodStock (reaction.reactants frame) := good_of_subset
      (fun species member => decomposition.mem_iff.mpr (List.mem_append_left _ member)) good
    have remaining : GoodStock remainder := good_of_subset
      (fun species member => decomposition.mem_iff.mpr (List.mem_append_right _ member)) good
    intro state member
    rcases List.mem_append.mp member with product | retained
    · exact reaction_good reaction input state product
    · exact remaining state retained

theorem products_noGuard (reaction : Reaction frame) : NoGuardStock (reaction.products frame) := by
  cases reaction with
  | retained old =>
    have safe := CPS1ElectronicSource.reaction_products_noGuard old
    refine ⟨?_,?_,?_⟩
    · intro failure member
      rcases List.mem_map.mp member with ⟨species,_,same⟩
      cases same
    · intro failure member
      rcases List.mem_map.mp member with ⟨species,present,same⟩
      have identified := Species.retained.inj same
      rw [identified] at present
      exact safe.1 failure present
    · intro member
      rcases List.mem_map.mp member with ⟨species,present,same⟩
      have identified := Species.retained.inj same
      rw [identified] at present
      exact safe.2 present
  | nuclearPulse state time =>
    cases updated : pulse? state time <;> simp [Reaction.products,updated,NoGuardStock]

theorem raw_good (action : Source.RawAction) : GoodStock (action.material frame) := by
  cases action with
  | old action =>
    have safe := (CPS1ElectronicSource.raw_material_safe (frame := frame) action).1
    intro state member
    apply safe state
    rcases List.mem_map.mp member with ⟨species,present,same⟩
    have identified := Species.retained.inj same
    rwa [identified] at present
  | nuclearPulse time => simp [GoodStock,Source.RawAction.material]

theorem raw_noGuard (action : Source.RawAction) : NoGuardStock (action.material frame) := by
  cases action with
  | old action =>
    have safe := (CPS1ElectronicSource.raw_material_safe (frame := frame) action).2
    refine ⟨?_,?_,?_⟩
    · intro failure member
      rcases List.mem_map.mp member with ⟨species,_,same⟩
      cases same
    · intro failure member
      rcases List.mem_map.mp member with ⟨species,present,same⟩
      have identified := Species.retained.inj same
      rw [identified] at present
      exact safe.1 failure present
    · intro member
      rcases List.mem_map.mp member with ⟨species,present,same⟩
      have identified := Species.retained.inj same
      rw [identified] at present
      exact safe.2 present
  | nuclearPulse time => simp [NoGuardStock,Source.RawAction.material]

theorem good_append {left right : Stock frame} (a : GoodStock left) (b : GoodStock right) :
    GoodStock (left ++ right) := fun state member => (List.mem_append.mp member).elim (a state) (b state)

theorem execute_good (program : List (Reaction frame)) (stock : Stock frame) (good : GoodStock stock) :
    GoodStock (execute frame program stock).stock := by
  induction program generalizing stock with
  | nil => exact good
  | cons reaction rest ih =>
    change GoodStock (Inventory.execute (Reaction.reactants frame) (Reaction.products frame)
      (reaction :: rest) stock).stock
    cases fired : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock with
    | error missing =>
      rw [Inventory.execute_cons,fired]
      exact good
    | ok next =>
      rw [Inventory.execute_cons,fired]
      exact ih next (fire_good reaction stock next good fired)

theorem fromActual_good (previous : CPS1ElectronicSource.Source.Occurrence frame)
    (good : CPS1ElectronicSource.GoodStock previous.current.stock) : GoodStock (Source.fromActual frame previous).current.stock := by
  intro state member
  apply good state
  rcases List.mem_map.mp member with ⟨species,present,same⟩
  have identified := Species.retained.inj same
  rwa [identified] at present

theorem actions_good (actions : List Source.RawAction) : GoodStock (actions.flatMap (Source.RawAction.material frame)) := by
  induction actions with
  | nil => simp [GoodStock]
  | cons action rest ih => exact good_append (raw_good action) ih

theorem feed_good (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    GoodStock (feed.map (fun kind => Species.retained (.retained (CPS1EnzymeBath.componentSpecies frame kind)))) := by
  intro state member
  simp at member

theorem advance_good (cursor : Source.Cursor frame) (actions : List Source.RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) (good : GoodStock cursor.stock) :
    GoodStock (Source.advance frame cursor actions feed).stock :=
  execute_good _ _ (good_append (good_append good (feed_good feed)) (actions_good actions))

theorem noGuard_subset {left right : Stock frame} (subset : ∀ species ∈ right, species ∈ left)
    (safe : NoGuardStock left) : NoGuardStock right :=
  ⟨fun failure member => safe.1 failure (subset _ member),
    fun failure member => safe.2.1 failure (subset _ member),fun member => safe.2.2 (subset _ member)⟩

theorem noGuard_append {left right : Stock frame} (a : NoGuardStock left) (b : NoGuardStock right) :
    NoGuardStock (left ++ right) := by
  refine ⟨?_,?_,?_⟩
  · intro failure member
    exact (List.mem_append.mp member).elim (a.1 failure) (b.1 failure)
  · intro failure member
    exact (List.mem_append.mp member).elim (a.2.1 failure) (b.2.1 failure)
  · intro member
    exact (List.mem_append.mp member).elim a.2.2 b.2.2

theorem fire_noGuard (reaction : Reaction frame) (stock next : Stock frame) (safe : NoGuardStock stock)
    (actual : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock = .ok next) :
    NoGuardStock next := by
  unfold Inventory.fire at actual
  cases consumed : Inventory.consume (reaction.reactants frame) stock with
  | error missing => simp [consumed] at actual
  | ok remainder =>
    simp only [consumed,Except.ok.injEq] at actual
    subst next
    have decomposition := Inventory.consume_perm _ _ _ consumed
    have remaining := noGuard_subset
      (fun species member => decomposition.mem_iff.mpr (List.mem_append_right _ member)) safe
    exact noGuard_append (products_noGuard reaction) remaining

theorem execute_noGuard (program : List (Reaction frame)) (stock : Stock frame) (safe : NoGuardStock stock) :
    NoGuardStock (execute frame program stock).stock := by
  induction program generalizing stock with
  | nil => exact safe
  | cons reaction rest ih =>
    change NoGuardStock (Inventory.execute (Reaction.reactants frame) (Reaction.products frame)
      (reaction :: rest) stock).stock
    cases fired : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock with
    | error missing =>
      rw [Inventory.execute_cons,fired]
      exact safe
    | ok next =>
      rw [Inventory.execute_cons,fired]
      exact ih next (fire_noGuard reaction stock next safe fired)

theorem retained_noGuard (stock : CPS1ElectronicSource.Stock frame) (safe : CPS1ElectronicSource.NoGuardStock stock) :
    NoGuardStock (stock.map Species.retained) := by
  refine ⟨?_,?_,?_⟩
  · intro failure member
    rcases List.mem_map.mp member with ⟨species,_,same⟩
    cases same
  · intro failure member
    rcases List.mem_map.mp member with ⟨species,present,same⟩
    have identified := Species.retained.inj same
    rw [identified] at present
    exact safe.1 failure present
  · intro member
    rcases List.mem_map.mp member with ⟨species,present,same⟩
    have identified := Species.retained.inj same
    rw [identified] at present
    exact safe.2 present

theorem actions_noGuard (actions : List Source.RawAction) :
    NoGuardStock (actions.flatMap (Source.RawAction.material frame)) := by
  induction actions with
  | nil => simp [NoGuardStock]
  | cons action rest ih => exact noGuard_append (raw_noGuard action) ih

theorem feed_noGuard (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    NoGuardStock (feed.map (fun kind => Species.retained (.retained (CPS1EnzymeBath.componentSpecies frame kind)))) := by
  have prior := (CPS1ElectronicSource.component_feed_safe (frame := frame) feed).2
  have same : (feed.map (fun kind => Species.retained (.retained (CPS1EnzymeBath.componentSpecies frame kind)))) =
      (feed.map (fun kind => CPS1ElectronicSource.Species.retained (CPS1EnzymeBath.componentSpecies frame kind))).map
        Species.retained := by rw [List.map_map]; rfl
  rw [same]
  exact retained_noGuard _ prior

theorem fromActual_noGuard (previous : CPS1ElectronicSource.Source.Occurrence frame)
    (safe : CPS1ElectronicSource.NoGuardStock previous.current.stock) :
    NoGuardStock (Source.fromActual frame previous).current.stock := retained_noGuard _ safe

theorem advance_noGuard (cursor : Source.Cursor frame) (actions : List Source.RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) (safe : NoGuardStock cursor.stock) :
    NoGuardStock (Source.advance frame cursor actions feed).stock :=
  execute_noGuard _ _ (noGuard_append (noGuard_append safe (feed_noGuard feed)) (actions_noGuard actions))

theorem resume_good (current : Source.Occurrence frame) (actions : List Source.RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) (good : GoodStock current.current.stock) :
    GoodStock (Source.resume frame current actions feed).current.stock := advance_good _ actions feed good

theorem resume_noGuard (current : Source.Occurrence frame) (actions : List Source.RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) (safe : NoGuardStock current.current.stock) :
    NoGuardStock (Source.resume frame current actions feed).current.stock := advance_noGuard _ actions feed safe

theorem source_stock
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (electronicActions : List CPS1ElectronicSource.Source.RawAction) (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List Source.RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind)
    (current : Σ frame : CPS1Recycling.Frame, Source.Occurrence frame)
    (actual : Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed actions feed = some current) :
    GoodStock current.2.current.stock ∧ NoGuardStock current.2.current.stock := by
  unfold Source.execution at actual
  cases prior : CPS1ElectronicSource.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed with
  | none => simp [prior] at actual
  | some previous =>
    simp only [prior] at actual
    have same := Option.some.inj actual
    cases same
    have paid := CPS1ElectronicSource.execution_safe edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed previous prior
    exact ⟨advance_good _ actions feed (fromActual_good previous.2 paid.1),
      advance_noGuard _ actions feed (fromActual_noGuard previous.2 paid.2)⟩

def ReactionFailure (reaction : Reaction frame) (failure : Failure) : Prop :=
  match reaction with
  | .nuclearPulse state time => pulse? state time = .error failure
  | .retained _ => False

theorem reaction_guard_failure (reaction : Reaction frame) (failure : Failure)
    (member : Species.guard failure ∈ reaction.reactants frame) : ReactionFailure reaction failure := by
  cases reaction with
  | retained old =>
    rcases List.mem_map.mp member with ⟨species,_,same⟩
    cases same
  | nuclearPulse state time =>
    cases updated : pulse? state time with
    | ok next => simp [Reaction.reactants,guards,updated] at member
    | error missing =>
      have same : failure = missing := by simpa [Reaction.reactants,guards,updated] using member
      cases same
      exact updated

theorem true_guard_cut (program : List (Reaction frame)) (stock : Stock frame) (failure : Failure)
    (cut : (execute frame program stock).missing = some (.guard failure)) :
    ∃ reaction rest, (execute frame program stock).remaining = reaction :: rest ∧
      ReactionFailure reaction failure ∧
      (execute frame program stock).stock.count (.guard failure) < (reaction.reactants frame).count (.guard failure) := by
  rcases actual_cut program stock (.guard failure) cut with ⟨reaction,rest,remaining,shortage⟩
  have positive := (Nat.zero_le _).trans_lt shortage
  exact ⟨reaction,rest,remaining,reaction_guard_failure reaction failure (List.count_pos_iff.mp positive),shortage⟩

theorem reaction_old_guard (reaction : Reaction frame) (failure : CPS1ElectronicSource.Failure)
    (member : Species.retained (.guard failure) ∈ reaction.reactants frame) :
    ∃ old, reaction = .retained old ∧ CPS1ElectronicSource.ReactionFailure old failure := by
  cases reaction with
  | retained old =>
    rcases List.mem_map.mp member with ⟨species,present,same⟩
    have identified := Species.retained.inj same
    rw [identified] at present
    exact ⟨old,rfl,CPS1ElectronicSource.reaction_guard_failure old failure present⟩
  | nuclearPulse state time =>
    cases updated : pulse? state time <;> simp [Reaction.reactants,guards,updated] at member

theorem inherited_guard_cut (program : List (Reaction frame)) (stock : Stock frame)
    (failure : CPS1ElectronicSource.Failure)
    (cut : (execute frame program stock).missing = some (.retained (.guard failure))) :
    ∃ old rest, (execute frame program stock).remaining = Reaction.retained old :: rest ∧
      CPS1ElectronicSource.ReactionFailure old failure := by
  rcases actual_cut program stock (.retained (.guard failure)) cut with ⟨reaction,rest,remaining,shortage⟩
  have positive := (Nat.zero_le _).trans_lt shortage
  rcases reaction_old_guard reaction failure (List.count_pos_iff.mp positive) with ⟨old,same,failed⟩
  cases same
  exact ⟨old,rest,remaining,failed⟩

theorem reaction_missingCarrier (reaction : Reaction frame)
    (member : Species.retained .missingCarrier ∈ reaction.reactants frame) : reaction = .retained .requireCarrier := by
  cases reaction with
  | retained old =>
    rcases List.mem_map.mp member with ⟨species,present,same⟩
    have identified := Species.retained.inj same
    rw [identified] at present
    rw [CPS1ElectronicSource.reaction_missingCarrier old present]
  | nuclearPulse state time =>
    cases updated : pulse? state time <;> simp [Reaction.reactants,guards,updated] at member

theorem legacy_requireCarrier_cut (program : List (Reaction frame)) (stock : Stock frame)
    (cut : (execute frame program stock).missing = some (.retained .missingCarrier)) :
    ∃ rest, (execute frame program stock).remaining = Reaction.retained .requireCarrier :: rest := by
  rcases actual_cut program stock (.retained .missingCarrier) cut with ⟨reaction,rest,remaining,shortage⟩
  have positive := (Nat.zero_le _).trans_lt shortage
  have same := reaction_missingCarrier reaction (List.count_pos_iff.mp positive)
  cases same
  exact ⟨rest,remaining⟩

end
end CPS1QuantumNuclear
