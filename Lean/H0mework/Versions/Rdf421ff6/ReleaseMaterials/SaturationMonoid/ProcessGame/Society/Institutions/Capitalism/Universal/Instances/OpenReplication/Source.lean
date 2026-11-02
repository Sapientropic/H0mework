import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Necessity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Retiming

/-!
# A paid opening of a replicable service

Fuel (`false`) and service copies (`true`) have separate inventories.  The
source recipe fixes a private batch-management overhead of n+2 fuel, a public
opening cost of 1 fuel, and mandatory upkeep of 1 fuel.  Both routes use the
same law, initial stock and recipient demand n+1.  These costs are explicit
model inputs; theorems derive execution rather than assuming its result.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.OpenReplication
open Source.Program
open Exit

abbrev Current := RawCurrent Bool Bool Bool Unit
abbrev Input := Request Bool Bool (Option Bool) Bool Unit

def law (n : Nat) : RawLaw Bool Bool (Option Bool) Bool Unit where
  technique := fun shared operator =>
    ⟨if operator then [] else [(false, 1)], [(true, (n : ℚ) + 1)],
      if shared then [] else [(false, (n : ℚ) + 2)], [none]⟩
  controller := fun _ port => port.getD false
  allowed := fun shared port signer => match port with
    | none => shared || !signer
    | some holder => decide (holder = signer)
  stockPort := fun _ holder _ => some holder
  revisionPort := fun _ => none
  revisionCost := fun old new => if old = new then [] else [(false, 1)]
  settlementUnit := fun _ => false
  settlementRate := fun _ => 1
  issuerPort := fun _ => none
  necessities := fun _ person => if person then [(true, (n : ℚ) + 1)] else []
  mandatoryMaintenance := fun _ person => if person then [] else [(false, 1)]
  duration := fun _ => 1

def state (fuel copies received : ℚ) (shared : Bool) : Current where
  stock := fun person good => if person then (if good then received else 0) else if good then copies else fuel
  claims := fun _ _ _ => 0
  technology := shared
  clock := 0
  round := 0

def initial (n : Nat) := state ((n : ℚ) + 5) 0 0 false

def openAccess : Input := ⟨false, [], none, [], .revise false true⟩
def produce : Input := ⟨false, [], none, [], .produce false⟩
def deliver (n : Nat) : Input :=
  ⟨false, [], none, [], .transfer false true [(true, (n : ℚ) + 1)]⟩
def consume (n : Nat) : Input :=
  ⟨true, [], some true, [], .use true [(true, (n : ℚ) + 1)] .necessity⟩
def maintain : Input := ⟨false, [], some false, [], .use false [(false, 1)] .maintenance⟩

def exclusive (n : Nat) : List Input := [produce, deliver n, consume n, maintain]
def publicRoute (n : Nat) : List Input := openAccess :: exclusive n

private theorem produce_valid (n : Nat) (fuel : ℚ) (shared : Bool)
    (enough : (if shared then 1 else (n : ℚ) + 3) ≤ fuel) :
    (law n).Valid (state fuel 0 0 shared) produce := by
  cases shared <;>
    simp [RawLaw.Valid, RawLaw.SignerMatches, RawLaw.ClaimGuard, RawLaw.operationAllowed,
      RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit,
      NonnegativeBundle, flowAt, amount, locate, law, state, produce] at * <;>
    (repeat' apply And.intro) <;> first | positivity | linarith


private theorem produce_step (n : Nat) (fuel : ℚ) (shared : Bool)
    (enough : (if shared then 1 else (n : ℚ) + 3) ≤ fuel) :
    (law n).step (state fuel 0 0 shared) produce =
      state (fuel - (if shared then 1 else (n : ℚ) + 3)) ((n : ℚ) + 1) 0 shared := by
  rw [RawLaw.step, if_pos (produce_valid n fuel shared enough)]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> cases shared <;>
      simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, produce, law,
        state, flowAt, amount, locate]; ring
  all_goals rfl

private theorem open_valid (n : Nat) (fuel : ℚ) (enough : 1 ≤ fuel) :
    (law n).Valid (state fuel 0 0 false) openAccess := by
  simpa [RawLaw.Valid, RawLaw.SignerMatches, RawLaw.ClaimGuard, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit,
    NonnegativeBundle, flowAt, amount, locate, law, state, openAccess] using enough

private theorem open_step (n : Nat) (fuel : ℚ) (enough : 1 ≤ fuel) :
    (law n).step (state fuel 0 0 false) openAccess = state (fuel - 1) 0 0 true := by
  rw [RawLaw.step, if_pos (open_valid n fuel enough)]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;>
      simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, openAccess, law,
        state, flowAt, amount, locate]
  all_goals rfl

private theorem deliver_valid (n : Nat) (fuel : ℚ) (shared : Bool) :
    (law n).Valid (state fuel ((n : ℚ) + 1) 0 shared) (deliver n) := by
  simp [RawLaw.Valid, RawLaw.SignerMatches, RawLaw.ClaimGuard, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit,
    NonnegativeBundle, flowAt, amount, locate, law, state, deliver]
  positivity

private theorem deliver_step (n : Nat) (fuel : ℚ) (shared : Bool) :
    (law n).step (state fuel ((n : ℚ) + 1) 0 shared) (deliver n) =
      state fuel 0 ((n : ℚ) + 1) shared := by
  rw [RawLaw.step, if_pos (deliver_valid n fuel shared)]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;>
      simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, deliver,
        state, flowAt, amount, locate]
  all_goals rfl

private theorem consume_valid (n : Nat) (fuel : ℚ) (shared : Bool) :
    (law n).Valid (state fuel 0 ((n : ℚ) + 1) shared) (consume n) := by
  simp [RawLaw.Valid, RawLaw.SignerMatches, RawLaw.ClaimGuard, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit,
    NonnegativeBundle, flowAt, amount, locate, law, state, consume]
  positivity

private theorem consume_step (n : Nat) (fuel : ℚ) (shared : Bool) :
    (law n).step (state fuel 0 ((n : ℚ) + 1) shared) (consume n) =
      state fuel 0 0 shared := by
  rw [RawLaw.step, if_pos (consume_valid n fuel shared)]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;>
      simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, consume,
        state, flowAt, amount, locate]
  all_goals rfl

private theorem maintain_valid (n : Nat) (fuel : ℚ) (shared : Bool) (enough : 1 ≤ fuel) :
    (law n).Valid (state fuel 0 0 shared) maintain := by
  simpa [RawLaw.Valid, RawLaw.SignerMatches, RawLaw.ClaimGuard, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit,
    NonnegativeBundle, flowAt, amount, locate, law, state, maintain] using enough

private theorem maintain_step (n : Nat) (fuel : ℚ) (shared : Bool) (enough : 1 ≤ fuel) :
    (law n).step (state fuel 0 0 shared) maintain = state (fuel - 1) 0 0 shared := by
  rw [RawLaw.step, if_pos (maintain_valid n fuel shared enough)]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;>
      simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, maintain,
        state, flowAt, amount, locate]
  all_goals rfl

private theorem exclusive_production (n : Nat) :
    (law n).step (initial n) produce = state 2 ((n : ℚ) + 1) 0 false := by
  change (law n).step (state ((n : ℚ) + 5) 0 0 false) produce = _
  rw [produce_step n _ false (by simp; linarith)]
  congr 1
  norm_num

private theorem public_opening (n : Nat) :
    (law n).step (initial n) openAccess = state ((n : ℚ) + 4) 0 0 true := by
  change (law n).step (state ((n : ℚ) + 5) 0 0 false) openAccess = _
  rw [open_step n _ (by have h := Nat.cast_nonneg (α := ℚ) n; linarith)]
  congr 1
  ring

private theorem public_production (n : Nat) :
    (law n).step (state ((n : ℚ) + 4) 0 0 true) produce =
      state ((n : ℚ) + 3) ((n : ℚ) + 1) 0 true := by
  rw [produce_step n _ true (by simp; have h := Nat.cast_nonneg (α := ℚ) n; linarith)]
  congr 1
  change (n : ℚ) + 4 - 1 = (n : ℚ) + 3
  ring

theorem exclusive_execution (n : Nat) :
    (law n).execute (initial n) 0 (exclusive n) =
      ⟨state 1 0 0 false,
        [⟨0, initial n, produce⟩,
         ⟨1, state 2 ((n : ℚ) + 1) 0 false, deliver n⟩,
         ⟨2, state 2 0 ((n : ℚ) + 1) false, consume n⟩,
         ⟨3, state 2 0 0 false, maintain⟩]⟩ := by
  simp only [exclusive, RawLaw.execute, exclusive_production, deliver_step, consume_step,
    maintain_step n 2 false (by norm_num)]
  norm_num

theorem public_execution (n : Nat) :
    (law n).execute (initial n) 0 (publicRoute n) =
      ⟨state ((n : ℚ) + 2) 0 0 true,
        [⟨0, initial n, openAccess⟩,
         ⟨1, state ((n : ℚ) + 4) 0 0 true, produce⟩,
         ⟨2, state ((n : ℚ) + 3) ((n : ℚ) + 1) 0 true, deliver n⟩,
         ⟨3, state ((n : ℚ) + 3) 0 ((n : ℚ) + 1) true, consume n⟩,
         ⟨4, state ((n : ℚ) + 3) 0 0 true, maintain⟩]⟩ := by
  simp only [publicRoute, exclusive, RawLaw.execute, public_opening, public_production,
    deliver_step, consume_step, maintain_step n ((n : ℚ) + 3) true (by have h := Nat.cast_nonneg (α := ℚ) n; linarith)]
  congr 1
  congr 1
  ring

theorem exclusive_accepted (n : Nat) :
    ∀ item ∈ (law n).rawItems (initial n) (exclusive n),
      (law n).Valid item.before item.request := by
  rw [RawLaw.rawItems, exclusive_execution]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨produce_valid n _ false (by simp; linarith), deliver_valid n 2 false,
    consume_valid n 2 false, maintain_valid n 2 false (by norm_num)⟩

theorem public_accepted (n : Nat) :
    ∀ item ∈ (law n).rawItems (initial n) (publicRoute n),
      (law n).Valid item.before item.request := by
  rw [RawLaw.rawItems, public_execution]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨open_valid n _ (by have h := Nat.cast_nonneg (α := ℚ) n; linarith), produce_valid n _ true (by simp; have h := Nat.cast_nonneg (α := ℚ) n; linarith),
    deliver_valid n _ true, consume_valid n _ true, maintain_valid n _ true (by have h := Nat.cast_nonneg (α := ℚ) n; linarith)⟩

theorem exclusive_paid (n : Nat) :
    Necessity.AllNeedsPaid (law n) (initial n) [false, true] (exclusive n) := by
  intro person _
  cases person
  · refine ⟨Or.inl rfl, Or.inr ?_⟩
    refine ⟨⟨3, state 2 0 0 false, maintain⟩, ?_, maintain_valid n 2 false (by norm_num), ?_⟩
    · rw [RawLaw.rawItems, exclusive_execution]
      simp
    · exact ⟨rfl, rfl, rfl⟩
  · refine ⟨Or.inr ?_, Or.inl rfl⟩
    refine ⟨⟨2, state 2 0 ((n : ℚ) + 1) false, consume n⟩, ?_, consume_valid n 2 false, ?_⟩
    · rw [RawLaw.rawItems, exclusive_execution]
      simp
    · exact ⟨rfl, rfl, rfl⟩

theorem public_paid (n : Nat) :
    Necessity.AllNeedsPaid (law n) (initial n) [false, true] (publicRoute n) := by
  intro person _
  cases person
  · refine ⟨Or.inl rfl, Or.inr ?_⟩
    refine ⟨⟨4, state ((n : ℚ) + 3) 0 0 true, maintain⟩, ?_,
      maintain_valid n _ true (by have h := Nat.cast_nonneg (α := ℚ) n; linarith), ?_⟩
    · rw [RawLaw.rawItems, public_execution]
      simp
    · exact ⟨rfl, rfl, rfl⟩
  · refine ⟨Or.inr ?_, Or.inl rfl⟩
    refine ⟨⟨3, state ((n : ℚ) + 3) 0 ((n : ℚ) + 1) true, consume n⟩, ?_,
      consume_valid n _ true, ?_⟩
    · rw [RawLaw.rawItems, public_execution]
      simp
    · exact ⟨rfl, rfl, rfl⟩

theorem time_independent (n : Nat) : (law n).TimeIndependent :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.OpenReplication
