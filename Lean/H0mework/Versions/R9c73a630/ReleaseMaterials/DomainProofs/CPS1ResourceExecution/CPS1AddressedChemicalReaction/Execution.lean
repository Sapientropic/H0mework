import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedChemicalReaction.Reservation

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace CPS1AddressedChemicalReaction
variable {S R : Type} [DecidableEq S]

def generatedProducts (event : Nat) (reaction : R) (consumed : List (Material S R))
    (products : List S) : List (Material S R) :=
  products.zipIdx.map (fun item => .product event item.2 reaction item.1 consumed)

omit [DecidableEq S] in
theorem generated_products_forget (event : Nat) (reaction : R)
    (consumed : List (Material S R)) (products : List S) :
    forget (generatedProducts event reaction consumed products) = products := by
  simp only [forget,generatedProducts,List.map_map]
  exact List.zipIdx_map_fst 0 products

structure Event (S R : Type) where
  index : Nat
  reaction : R
  before : List (Material S R)
  consumed : List (Material S R)
  remainder : List (Material S R)

def Event.created (products : R → List S) (event : Event S R) : List (Material S R) :=
  generatedProducts event.index event.reaction event.consumed (products event.reaction)

def Event.after (products : R → List S) (event : Event S R) : List (Material S R) :=
  event.created products ++ event.remainder

def fire? (reactants : R → List S) (index : Nat) (reaction : R)
    (stock : List (Material S R)) : Except S (Event S R) :=
  match reserve? (reactants reaction) stock with
  | .error missing => .error missing
  | .ok paid => .ok ⟨index,reaction,stock,paid.1,paid.2⟩

def Event.Valid (reactants products : R → List S) (event : Event S R) : Prop :=
  forget event.consumed = reactants event.reaction ∧
    event.before.Perm (event.consumed ++ event.remainder) ∧
    CPS1ResourceExecution.Inventory.fire reactants products event.reaction (forget event.before) =
      .ok (forget (event.after products))

theorem fire_paid (reactants products : R → List S) (index : Nat) (reaction : R)
    (stock : List (Material S R)) (event : Event S R)
    (actual : fire? reactants index reaction stock = .ok event) :
    event.index = index ∧ event.reaction = reaction ∧ event.before = stock ∧
      event.Valid reactants products := by
  unfold fire? at actual
  cases reserved : reserve? (reactants reaction) stock with
  | error missing => simp [reserved] at actual
  | ok paid =>
    rcases paid with ⟨consumed,remainder⟩
    simp only [reserved,Except.ok.injEq] at actual
    subst event
    have selected := reserve_paid _ _ _ _ reserved
    refine ⟨rfl,rfl,rfl,selected.1,selected.2,?_⟩
    have projected := reserve_project (reactants reaction) stock
    rw [reserved] at projected
    simp only [Except.map] at projected
    unfold CPS1ResourceExecution.Inventory.fire
    rw [← projected]
    simp only [Event.after,Event.created,forget_append,generated_products_forget]

theorem fire_project (reactants products : R → List S) (index : Nat) (reaction : R)
    (stock : List (Material S R)) :
    (fire? reactants index reaction stock).map (fun event => forget (event.after products)) =
      CPS1ResourceExecution.Inventory.fire reactants products reaction (forget stock) := by
  unfold fire?
  have projected := reserve_project (reactants reaction) stock
  cases reserved : reserve? (reactants reaction) stock with
  | error missing =>
    rw [reserved] at projected
    simp only [Except.map] at projected
    simp only [CPS1ResourceExecution.Inventory.fire,← projected,Except.map]
  | ok paid =>
    rw [reserved] at projected
    simp only [Except.map] at projected
    simp only [CPS1ResourceExecution.Inventory.fire,← projected,Except.map,Event.after,
      Event.created,forget_append,generated_products_forget]

structure Execution (S R : Type) where
  fired : List (Event S R)
  remaining : List R
  stock : List (Material S R)
  missing : Option S
  nextEvent : Nat

def run (reactants products : R → List S) (index : Nat) (program : List R)
    (stock : List (Material S R)) : Execution S R :=
  List.rec (motive := fun _ => Nat → List (Material S R) → Execution S R)
    (fun index available => ⟨[],[],available,none,index⟩)
    (fun reaction rest recur index available =>
      match fire? reactants index reaction available with
      | .error missing => ⟨[],reaction :: rest,available,some missing,index⟩
      | .ok event =>
        let after := recur (index+1) (event.after products)
        ⟨event :: after.fired,after.remaining,after.stock,after.missing,after.nextEvent⟩) program index stock

theorem run_nil (reactants products : R → List S) (index : Nat) (stock : List (Material S R)) :
    run reactants products index [] stock = ⟨[],[],stock,none,index⟩ := rfl

theorem run_cons (reactants products : R → List S) (index : Nat) (reaction : R)
    (rest : List R) (stock : List (Material S R)) :
    run reactants products index (reaction :: rest) stock =
      match fire? reactants index reaction stock with
      | .error missing => ⟨[],reaction :: rest,stock,some missing,index⟩
      | .ok event =>
        let after := run reactants products (index+1) rest (event.after products)
        ⟨event :: after.fired,after.remaining,after.stock,after.missing,after.nextEvent⟩ := rfl

def Execution.forget (execution : Execution S R) : CPS1ResourceExecution.Inventory.Execution S R :=
  ⟨execution.fired.map Event.reaction,execution.remaining,
    CPS1AddressedChemicalReaction.forget execution.stock,execution.missing⟩

theorem run_project (reactants products : R → List S) (index : Nat)
    (program : List R) (stock : List (Material S R)) :
    (run reactants products index program stock).forget =
      CPS1ResourceExecution.Inventory.execute reactants products program (forget stock) := by
  induction program generalizing index stock with
  | nil => rfl
  | cons reaction rest ih =>
    have projected := fire_project reactants products index reaction stock
    cases fired : fire? reactants index reaction stock with
    | error missing =>
      rw [fired] at projected
      simp only [Except.map] at projected
      rw [CPS1ResourceExecution.Inventory.execute_cons,← projected]
      simp only [run_cons,fired,Execution.forget]
      rfl
    | ok event =>
      have same := (fire_paid reactants products index reaction stock event fired).2.1
      rw [fired] at projected
      simp only [Except.map] at projected
      rw [CPS1ResourceExecution.Inventory.execute_cons,← projected]
      simp only [run_cons,fired]
      change _ =
        (⟨reaction :: (CPS1ResourceExecution.Inventory.execute reactants products rest
          (forget (event.after products))).fired,
         (CPS1ResourceExecution.Inventory.execute reactants products rest (forget (event.after products))).remaining,
         (CPS1ResourceExecution.Inventory.execute reactants products rest (forget (event.after products))).stock,
         (CPS1ResourceExecution.Inventory.execute reactants products rest (forget (event.after products))).missing⟩ :
          CPS1ResourceExecution.Inventory.Execution S R)
      have later := ih (index+1) (event.after products)
      cases completed : run reactants products (index+1) rest (event.after products) with
      | mk trace remaining final missing next =>
        rw [completed] at later
        rw [← later]
        simp only [Execution.forget,List.map_cons,same]

inductive Path (reactants products : R → List S) :
    Nat → List (Material S R) → List (Event S R) → List (Material S R) → Prop
  | nil (index stock) : Path reactants products index stock [] stock
  | cons {index stock event trace final}
      (actual : fire? reactants index event.reaction stock = .ok event)
      (rest : Path reactants products (index+1) (event.after products) trace final) :
      Path reactants products index stock (event :: trace) final

theorem run_path (reactants products : R → List S) (index : Nat)
    (program : List R) (stock : List (Material S R)) :
    Path reactants products index stock (run reactants products index program stock).fired
      (run reactants products index program stock).stock := by
  induction program generalizing index stock with
  | nil => exact .nil _ _
  | cons reaction rest ih =>
    cases fired : fire? reactants index reaction stock with
    | error missing => simpa only [run_cons,fired] using (Path.nil (reactants := reactants) (products := products) index stock)
    | ok event =>
      have same := (fire_paid reactants products index reaction stock event fired).2.1
      simpa only [run_cons,fired] using
        (Path.cons (same ▸ fired) (ih (index+1) (event.after products)))

theorem run_next_event (reactants products : R → List S) (index : Nat)
    (program : List R) (stock : List (Material S R)) :
    (run reactants products index program stock).nextEvent =
      index + (run reactants products index program stock).fired.length := by
  induction program generalizing index stock with
  | nil => rfl
  | cons reaction rest ih =>
    cases fired : fire? reactants index reaction stock with
    | error missing => simp only [run_cons,fired,List.length_nil,Nat.add_zero]
    | ok event =>
      simpa only [run_cons,fired,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih (index+1) (event.after products)

theorem path_events_valid (reactants products : R → List S) (index : Nat)
    (initial : List (Material S R)) (trace : List (Event S R)) (final : List (Material S R))
    (path : Path reactants products index initial trace final) :
    ∀ event ∈ trace, event.Valid reactants products := by
  induction path with
  | nil => simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | @cons index stock event trace final actual rest ih =>
    intro selected member
    rcases List.mem_cons.mp member with same | later
    · subst selected
      exact (fire_paid reactants products _ _ _ _ actual).2.2.2
    · exact ih _ later

theorem path_event_indices (reactants products : R → List S) (index : Nat)
    (initial : List (Material S R)) (trace : List (Event S R)) (final : List (Material S R))
    (path : Path reactants products index initial trace final) :
    trace.map Event.index = List.range' index trace.length := by
  induction path with
  | nil => rfl
  | @cons index stock event trace final actual rest ih =>
    have atIndex := (fire_paid reactants products _ _ _ _ actual).1
    simp only [List.map_cons,List.length_cons,List.range'_succ,atIndex,ih]

/-- Equality of individual material occurrences, rather than only molecular
species counts, pays every consumed object and all unused residual material. -/
theorem path_whole (reactants products : R → List S) (index : Nat)
    (initial : List (Material S R)) (trace : List (Event S R)) (final : List (Material S R))
    (path : Path reactants products index initial trace final) :
    (initial ++ trace.flatMap (Event.created products)).Perm
      (final ++ trace.flatMap Event.consumed) := by
  classical
  induction path with
  | nil => exact List.Perm.refl _
  | @cons index stock event trace final actual rest ih =>
    have facts := fire_paid reactants products _ _ _ _ actual
    have selected := facts.2.2.2.2.1
    rw [facts.2.2.1] at selected
    apply List.perm_iff_count.mpr
    intro material
    have step := selected.count_eq material
    have later := ih.count_eq material
    simp only [Event.after,List.count_append] at step later
    simp only [List.flatMap_cons,List.count_append]
    omega

end CPS1AddressedChemicalReaction
