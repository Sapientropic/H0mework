import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ResourceExecution.Reactions
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace CPS1ResourceExecution

abbrev Stock := List Species

/- One reservation/execution kernel serves both the original chemistry and source-indexed compounds. -/
namespace Inventory
variable {S R : Type} [DecidableEq S]

abbrev value (μ : S → ℚ) (stock : List S) : ℚ := (stock.map μ).sum

/-- Failed reservation rolls back the entire reaction, including a shortage
of the second copy of a repeated reactant. -/
abbrev consume (required : List S) (stock : List S) : Except S (List S) :=
  List.rec (motive := fun _ => List S → Except S (List S))
    (fun available => .ok available)
    (fun a _ recur available =>
      if a ∈ available then recur (available.erase a) else .error a) required stock

abbrev fire (reactants products : R → List S) (reaction : R) (stock : List S) : Except S (List S) :=
  match consume (reactants reaction) stock with
  | .error missing => .error missing
  | .ok remainder => .ok (products reaction ++ remainder)

theorem consume_perm (required stock remainder : List S)
    (paid : consume required stock = .ok remainder) :
    stock.Perm (required ++ remainder) := by
  induction required generalizing stock with
  | nil =>
    simp only [consume, Except.ok.injEq] at paid
    subst remainder
    exact List.Perm.refl stock
  | cons a rest ih =>
    by_cases present : a ∈ stock
    · simp only [consume, if_pos present] at paid
      exact (List.perm_cons_erase present).trans ((ih _ paid).cons a)
    · simp [consume, present] at paid

theorem consume_shortage (required stock : List S) (missing : S)
    (cut : consume required stock = .error missing) :
    stock.count missing < required.count missing := by
  induction required generalizing stock with
  | nil => simp [consume] at cut
  | cons a rest ih =>
    by_cases present : a ∈ stock
    · simp only [consume, if_pos present] at cut
      have shortage := ih _ cut
      by_cases same : a = missing
      · subst a
        have positive : 0 < stock.count missing := List.count_pos_iff.mpr present
        simp only [List.count_erase_self, List.count_cons_self] at shortage ⊢
        omega
      · simpa [List.count_erase_of_ne (Ne.symm same), List.count_cons, same,
          beq_iff_eq] using shortage
    · simp only [consume, if_neg present, Except.error.injEq] at cut
      subst a
      have zero : stock.count missing = 0 := List.count_eq_zero.mpr present
      simp [zero]

abbrev reactionAffinity (μ : S → ℚ) (reactants products : R → List S) (reaction : R) : ℚ :=
  value μ (reactants reaction) - value μ (products reaction)

theorem fire_balance (reactants products : R → List S) (reaction : R) (stock next : List S)
    (paid : fire reactants products reaction stock = .ok next) (s : S) :
    stock.count s + (products reaction).count s =
      next.count s + (reactants reaction).count s := by
  unfold fire at paid
  cases consumed : consume (reactants reaction) stock with
  | error missing => simp [consumed] at paid
  | ok remainder =>
    simp only [consumed, Except.ok.injEq] at paid
    subst next
    have balance := (consume_perm _ _ _ consumed).count_eq s
    simp only [List.count_append] at balance ⊢
    omega

theorem fire_potential (reactants products : R → List S) (reaction : R) (stock next : List S)
    (paid : fire reactants products reaction stock = .ok next) (μ : S → ℚ) :
    value μ stock = value μ next + reactionAffinity μ reactants products reaction := by
  unfold fire at paid
  cases consumed : consume (reactants reaction) stock with
  | error missing => simp [consumed] at paid
  | ok remainder =>
    simp only [consumed, Except.ok.injEq] at paid
    subst next
    have balance := ((consume_perm _ _ _ consumed).map μ).sum_eq
    simp only [List.map_append, List.sum_append] at balance
    change value μ stock = value μ (reactants reaction) + value μ remainder at balance
    rw [balance]
    simp only [value, List.map_append, List.sum_append, reactionAffinity]
    ring

structure Execution (S R : Type) where
  fired : List R
  remaining : List R
  stock : List S
  missing : Option S
  deriving Repr

abbrev execute (reactants products : R → List S) (program : List R) (stock : List S) : Execution S R :=
  List.rec (motive := fun _ => List S → Execution S R)
    (fun available => ⟨[], [], available, none⟩)
    (fun reaction rest recur available =>
      match fire reactants products reaction available with
      | .error missing => ⟨[], reaction :: rest, available, some missing⟩
      | .ok next =>
        let after := recur next
        ⟨reaction :: after.fired, after.remaining, after.stock, after.missing⟩) program stock

abbrev debit (reactants : R → List S) (trace : List R) : List S := trace.flatMap reactants
abbrev credit (products : R → List S) (trace : List R) : List S := trace.flatMap products
abbrev affinity (μ : S → ℚ) (reactants products : R → List S) (trace : List R) : ℚ :=
  (trace.map (reactionAffinity μ reactants products)).sum

theorem execution_decomposes (reactants products : R → List S) (program : List R) (stock : List S) :
    (execute reactants products program stock).fired ++ (execute reactants products program stock).remaining = program := by
  induction program generalizing stock with
  | nil => rfl
  | cons reaction rest ih =>
    cases fired : fire reactants products reaction stock with
    | error missing => simp [execute, fired]
    | ok next => simpa [execute, fired] using congrArg (reaction :: ·) (ih next)

theorem execution_balance (reactants products : R → List S) (program : List R) (stock : List S) (s : S) :
    stock.count s + (credit products (execute reactants products program stock).fired).count s =
      (execute reactants products program stock).stock.count s + (debit reactants (execute reactants products program stock).fired).count s := by
  induction program generalizing stock with
  | nil => simp [credit, debit]
  | cons reaction rest ih =>
    cases fired : fire reactants products reaction stock with
    | error missing => simp [execute, fired, credit, debit]
    | ok next =>
      have step := fire_balance _ _ _ _ _ fired s
      have later := ih next
      simp only [credit, debit] at later
      simp only [execute, fired, credit, debit, List.flatMap_cons, List.count_append]
      change stock.count s +
        ((products reaction).count s + (credit products (execute reactants products rest next).fired).count s) =
        (execute reactants products rest next).stock.count s +
          ((reactants reaction).count s + (debit reactants (execute reactants products rest next).fired).count s)
      simp only [credit, debit]
      omega

theorem execution_potential (reactants products : R → List S) (program : List R) (stock : List S) (μ : S → ℚ) :
    value μ stock = value μ (execute reactants products program stock).stock +
      affinity μ reactants products (execute reactants products program stock).fired := by
  induction program generalizing stock with
  | nil => simp [affinity]
  | cons reaction rest ih =>
    cases fired : fire reactants products reaction stock with
    | error missing => simp [execute, fired, affinity]
    | ok next =>
      have step := fire_potential _ _ _ _ _ fired μ
      have later := ih next
      simp only [execute, fired, affinity, List.map_cons, List.sum_cons]
      change value μ stock = value μ (execute reactants products rest next).stock +
        (reactionAffinity μ reactants products reaction + affinity μ reactants products (execute reactants products rest next).fired)
      rw [later] at step
      simpa [affinity, add_assoc, add_comm, add_left_comm] using step

theorem execution_cut (reactants products : R → List S) (program : List R) (stock : List S) (missing : S)
    (cut : (execute reactants products program stock).missing = some missing) :
    ∃ reaction rest, (execute reactants products program stock).remaining = reaction :: rest ∧
      (execute reactants products program stock).stock.count missing < (reactants reaction).count missing := by
  induction program generalizing stock with
  | nil => simp at cut
  | cons reaction rest ih =>
    cases fired : fire reactants products reaction stock with
    | error s =>
      simp only [execute, fired, Option.some.injEq] at cut
      subst s
      refine ⟨reaction, rest, by simp [execute, fired], ?_⟩
      simp only [execute, fired]
      unfold fire at fired
      cases consumed : consume (reactants reaction) stock with
      | ok remainder => simp [consumed] at fired
      | error s =>
        simp only [consumed, Except.error.injEq] at fired
        subst s
        exact consume_shortage _ _ _ consumed
    | ok next =>
      simpa [execute, fired] using ih next (by simpa [execute, fired] using cut)


theorem consume_available (required remainder stock : List S)
    (inventory : stock.Perm (required ++ remainder)) :
    ∃ next, consume required stock = .ok next ∧ next.Perm remainder := by
  induction required generalizing stock with
  | nil => exact ⟨stock,rfl,inventory⟩
  | cons a required ih =>
      have present : a ∈ stock := inventory.mem_iff.mpr (by simp)
      have residual : (stock.erase a).Perm (required ++ remainder) := by
        simpa using inventory.erase a
      rcases ih (stock.erase a) residual with ⟨next,paid,aligned⟩
      exact ⟨next,by simp only [consume,if_pos present]; exact paid,aligned⟩

theorem fire_available (reactants products : R → List S) (reaction : R)
    (remainder stock : List S) (inventory : stock.Perm (reactants reaction ++ remainder)) :
    ∃ next, fire reactants products reaction stock = .ok next ∧
      next.Perm (products reaction ++ remainder) := by
  rcases consume_available (reactants reaction) remainder stock inventory with ⟨next,paid,aligned⟩
  exact ⟨products reaction ++ next,by simp only [fire,paid],aligned.append_left _⟩


theorem fire_measure_preserved (reactants products : R → List S) (reaction : R)
    (stock next : List S) (paid : fire reactants products reaction stock = .ok next)
    (measure : S → Nat)
    (balanced : ((reactants reaction).map measure).sum = ((products reaction).map measure).sum) :
    (stock.map measure).sum = (next.map measure).sum := by
  unfold fire at paid
  cases consumed : consume (reactants reaction) stock with
  | error missing => simp [consumed] at paid
  | ok remainder =>
      simp only [consumed,Except.ok.injEq] at paid
      subst next
      have perm := ((consume_perm _ _ _ consumed).map measure).sum_eq
      simpa only [List.map_append,List.sum_append,balanced] using perm

theorem execute_cons (reactants products : R → List S) (reaction : R) (rest : List R)
    (stock : List S) : execute reactants products (reaction :: rest) stock =
      match fire reactants products reaction stock with
      | .error missing => ⟨[],reaction :: rest,stock,some missing⟩
      | .ok next =>
          let after := execute reactants products rest next
          ⟨reaction :: after.fired,after.remaining,after.stock,after.missing⟩ := rfl

theorem execution_measure_preserved (reactants products : R → List S)
    (program : List R) (stock : List S) (measure : S → Nat)
    (balanced : ∀ reaction ∈ program,
      ((reactants reaction).map measure).sum = ((products reaction).map measure).sum) :
    (stock.map measure).sum = ((execute reactants products program stock).stock.map measure).sum := by
  induction program generalizing stock with
  | nil => rfl
  | cons reaction rest ih =>
      cases fired : fire reactants products reaction stock with
      | error missing => simp [execute,fired]
      | ok next =>
          have step : (stock.map measure).sum = (next.map measure).sum := by
            unfold fire at fired
            cases consumed : consume (reactants reaction) stock with
            | error missing => simp [consumed] at fired
            | ok remainder =>
                simp only [consumed,Except.ok.injEq] at fired
                subst next
                have perm := ((consume_perm _ _ _ consumed).map measure).sum_eq
                simpa only [List.map_append,List.sum_append,balanced reaction (by simp)] using perm
          have later := ih next (fun r member => balanced r (by simp [member]))
          simp only [execute,fired]
          exact step.trans later

end Inventory

def consume (required : Stock) (stock : Stock) : Except Species Stock :=
  Inventory.consume required stock

abbrev fire (reaction : Reaction) (stock : Stock) : Except Species Stock :=
  Inventory.fire Reaction.reactants Reaction.products reaction stock

theorem consume_perm (required stock remainder : Stock)
    (paid : consume required stock = .ok remainder) : stock.Perm (required ++ remainder) :=
  Inventory.consume_perm required stock remainder paid

theorem consume_shortage (required stock : Stock) (missing : Species)
    (cut : consume required stock = .error missing) : stock.count missing < required.count missing :=
  Inventory.consume_shortage required stock missing cut

def reactionAffinity (μ : Species → ℚ) (reaction : Reaction) : ℚ :=
  Inventory.reactionAffinity μ Reaction.reactants Reaction.products reaction

theorem fire_balance (reaction : Reaction) (stock next : Stock)
    (paid : fire reaction stock = .ok next) (s : Species) :
    stock.count s + reaction.products.count s = next.count s + reaction.reactants.count s :=
  Inventory.fire_balance Reaction.reactants Reaction.products reaction stock next paid s

theorem fire_potential (reaction : Reaction) (stock next : Stock)
    (paid : fire reaction stock = .ok next) (μ : Species → ℚ) :
    speciesValue μ stock = speciesValue μ next + reactionAffinity μ reaction :=
  Inventory.fire_potential Reaction.reactants Reaction.products reaction stock next paid μ

abbrev Execution := Inventory.Execution Species Reaction

namespace Execution
abbrev mk (fired remaining : List Reaction) (stock : Stock) (missing : Option Species) : Execution :=
  Inventory.Execution.mk fired remaining stock missing
abbrev fired (execution : Execution) : List Reaction := Inventory.Execution.fired execution
abbrev remaining (execution : Execution) : List Reaction := Inventory.Execution.remaining execution
abbrev stock (execution : Execution) : Stock := Inventory.Execution.stock execution
abbrev missing (execution : Execution) : Option Species := Inventory.Execution.missing execution
end Execution

def execute (program : List Reaction) (stock : Stock) : Execution :=
  Inventory.execute Reaction.reactants Reaction.products program stock

def debit (trace : List Reaction) : Stock := Inventory.debit Reaction.reactants trace
def credit (trace : List Reaction) : Stock := Inventory.credit Reaction.products trace
def affinity (μ : Species → ℚ) (trace : List Reaction) : ℚ :=
  Inventory.affinity μ Reaction.reactants Reaction.products trace

theorem execution_decomposes (program : List Reaction) (stock : Stock) :
    (execute program stock).fired ++ (execute program stock).remaining = program :=
  Inventory.execution_decomposes Reaction.reactants Reaction.products program stock

theorem execution_balance (program : List Reaction) (stock : Stock) (s : Species) :
    stock.count s + (credit (execute program stock).fired).count s =
      (execute program stock).stock.count s + (debit (execute program stock).fired).count s :=
  Inventory.execution_balance Reaction.reactants Reaction.products program stock s

theorem execution_potential (program : List Reaction) (stock : Stock) (μ : Species → ℚ) :
    speciesValue μ stock = speciesValue μ (execute program stock).stock +
      affinity μ (execute program stock).fired :=
  Inventory.execution_potential Reaction.reactants Reaction.products program stock μ

theorem execution_cut (program : List Reaction) (stock : Stock) (missing : Species)
    (cut : (execute program stock).missing = some missing) :
    ∃ reaction rest, (execute program stock).remaining = reaction :: rest ∧
      (execute program stock).stock.count missing < reaction.reactants.count missing :=
  Inventory.execution_cut Reaction.reactants Reaction.products program stock missing cut

end CPS1ResourceExecution
