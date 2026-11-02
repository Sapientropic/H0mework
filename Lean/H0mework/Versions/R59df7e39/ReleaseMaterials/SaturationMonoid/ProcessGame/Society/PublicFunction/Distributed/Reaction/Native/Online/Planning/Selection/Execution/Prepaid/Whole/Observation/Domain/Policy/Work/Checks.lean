import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work.Checks
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

/-- Leaves request original source checks; no completed check or decision is an input. -/
inductive Code (prepared : Prepared input) : Prop → Type where
  | truth : Code prepared True
  | row (reference term : Section prepared) (row : Row prepared) : Code prepared (Holds prepared reference term row)
  | benefit (new previous : Section prepared) (index : Index prepared) : Code prepared
      (localBenefit prepared.saved[index].stage (readTerm prepared new index) (readTerm prepared previous index))
  | conjunction {A B : Prop} (left : Code prepared A) (right : Code prepared B) : Code prepared (A ∧ B)
  | negative {A : Prop} (body : Code prepared A) : Code prepared (¬A)
  | implication {A B : Prop} (left : Code prepared A) (right : Code prepared B) : Code prepared (A → B)
  | transport {A B : Prop} (equivalent : A ↔ B) (body : Code prepared A) : Code prepared B

/-- Specification only. The cursor below never calls this evaluator. -/
def Code.eval {A : Prop} : Code prepared A → Check prepared A
  | .truth => Builders.trueCheck
  | .row reference term entry => atom prepared reference term entry
  | .benefit new previous index => localImprovement prepared index prepared.saved[index].stage
      (readTerm prepared new index) (readTerm prepared previous index)
  | .conjunction left right => Work.conjunction left.eval (fun _ => right.eval)
  | .negative body => Work.negative body.eval
  | .implication left right => Work.implication left.eval (fun _ => right.eval)
  | .transport equivalent body => Work.transport equivalent body.eval

def Code.weight {A : Prop} : Code prepared A → Nat
  | .truth | .row .. | .benefit .. => 1
  | .conjunction left right | .implication left right => left.weight+right.weight+2
  | .negative body | .transport _ body => body.weight+1

def rowsCode (reference term : Section prepared) : (items : List (Row prepared)) → Code prepared (∀ row ∈ items,Holds prepared reference term row)
  | [] => .transport (by simp) .truth
  | head::tail => .transport (by simp only [List.mem_cons,forall_eq_or_imp]) (.conjunction (.row reference term head) (rowsCode reference term tail))
def benefitsCode (new previous : Section prepared) : (items : List (Index prepared)) → Code prepared
    (∀ index ∈ items,localBenefit prepared.saved[index].stage (readTerm prepared new index) (readTerm prepared previous index))
  | [] => .transport (by simp) .truth
  | head::tail => .transport (by simp only [List.mem_cons,forall_eq_or_imp]) (.conjunction (.benefit new previous head) (benefitsCode new previous tail))
def noWorseCode (new previous : Section prepared) : Code prepared (NoWorse prepared new previous) :=
  .transport (rows_iff prepared previous new) (rowsCode previous new (rows prepared))
def benefitCode (new previous : Section prepared) : Code prepared (Benefit prepared new previous) :=
  .transport (by
    constructor
    · intro h index;exact h index (List.mem_finRange index)
    · intro h index _;exact h index) (benefitsCode new previous (keys prepared))
def strictCode (previous new : Section prepared) : Code prepared (Strict prepared previous new) :=
  .conjunction (benefitCode new previous) (.negative (benefitCode previous new))
def othersCode (reference term : Section prepared) : (items : List (Section prepared)) → Code prepared
    (∀ other ∈ items,NoWorse prepared other reference → ¬Improves (axes prepared) (cost prepared) term other)
  | [] => .transport (by simp) .truth
  | head::tail => .transport (by simp only [List.mem_cons,forall_eq_or_imp]) (.conjunction
      (.implication (noWorseCode head reference) (.negative (.transport (Builders.strictEquivalence term head) (strictCode term head))))
      (othersCode reference term tail))
def verifyCode (reference term : Section prepared) : Code prepared
    (NoWorse prepared term reference ∧ ∀ other ∈ sections prepared,NoWorse prepared other reference → ¬Improves (axes prepared) (cost prepared) term other) :=
  .conjunction (noWorseCode term reference) (othersCode reference term (sections prepared))

theorem rowsCode_exact (reference term : Section prepared) (items : List (Row prepared)) :
    (rowsCode reference term items).eval = allRows (Holds prepared reference term) (atom prepared reference term) items := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [rowsCode,Code.eval,allRows,ih]
theorem benefitsCode_exact (new previous : Section prepared) (items : List (Index prepared)) :
    (benefitsCode new previous items).eval = allRows
      (fun index => localBenefit prepared.saved[index].stage (readTerm prepared new index) (readTerm prepared previous index))
      (fun index => localImprovement prepared index prepared.saved[index].stage (readTerm prepared new index) (readTerm prepared previous index)) items := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [benefitsCode,Code.eval,allRows,ih]
theorem noWorseCode_exact (new previous : Section prepared) : (noWorseCode new previous).eval = noWorse prepared new previous := by
  simp only [noWorseCode,Code.eval,rowsCode_exact,noWorse]
theorem benefitCode_exact (new previous : Section prepared) : (benefitCode new previous).eval = realBenefit prepared new previous := by
  simp only [benefitCode,Code.eval,benefitsCode_exact,realBenefit]
theorem strictCode_exact (previous new : Section prepared) : (strictCode previous new).eval = strict prepared previous new := by
  simp only [strictCode,Code.eval,benefitCode_exact,strict];rfl
theorem othersCode_exact (reference term : Section prepared) (items : List (Section prepared)) :
    (othersCode reference term items).eval = allRows
      (fun other => NoWorse prepared other reference → ¬Improves (axes prepared) (cost prepared) term other)
      (fun other => Work.implication (noWorse prepared other reference) (fun _ => Work.negative
        (Work.transport (Builders.strictEquivalence term other) (strict prepared term other)))) items := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [othersCode,Code.eval,allRows,noWorseCode_exact,strictCode_exact,ih]
theorem verifyCode_exact (reference term : Section prepared) : (verifyCode reference term).eval = verify prepared reference term := by
  simp only [verifyCode,Code.eval,noWorseCode_exact,othersCode_exact,verify]

def noWorseWeight (prepared : Prepared input) := 4*(rows prepared).length+3
def strictWeight (prepared : Prepared input) := 8*(keys prepared).length+9
def verifyWeight (prepared : Prepared input) := noWorseWeight prepared+(sections prepared).length*(noWorseWeight prepared+strictWeight prepared+7)+4
theorem rowsCode_weight (reference term : Section prepared) (items : List (Row prepared)) :
    (rowsCode reference term items).weight = 4*items.length+2 := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [rowsCode,Code.weight,List.length_cons,ih];omega
theorem benefitsCode_weight (new previous : Section prepared) (items : List (Index prepared)) :
    (benefitsCode new previous items).weight = 4*items.length+2 := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [benefitsCode,Code.weight,List.length_cons,ih];omega
theorem noWorseCode_weight (new previous : Section prepared) : (noWorseCode new previous).weight = noWorseWeight prepared := by
  simp only [noWorseCode,Code.weight,rowsCode_weight,noWorseWeight]
theorem strictCode_weight (previous new : Section prepared) : (strictCode previous new).weight = strictWeight prepared := by
  simp only [strictCode,benefitCode,Code.weight,benefitsCode_weight,strictWeight];omega
theorem othersCode_weight (reference term : Section prepared) (items : List (Section prepared)) :
    (othersCode reference term items).weight = items.length*(noWorseWeight prepared+strictWeight prepared+7)+2 := by
  induction items with
  | nil => simp only [othersCode,Code.weight,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons head tail ih => simp only [othersCode,Code.weight,noWorseCode_weight,strictCode_weight,List.length_cons,ih,Nat.add_mul,Nat.one_mul];omega
theorem verifyCode_weight (reference term : Section prepared) : (verifyCode reference term).weight = verifyWeight prepared := by
  simp only [verifyCode,Code.weight,noWorseCode_weight,othersCode_weight,verifyWeight];omega

inductive Kont (prepared : Prepared input) (goal : Prop) : Prop → Type where
  | done : Kont prepared goal goal
  | transport {A B : Prop} (equivalent : A ↔ B) (later : Kont prepared goal B) : Kont prepared goal A
  | negative {A : Prop} (later : Kont prepared goal (¬A)) : Kont prepared goal A
  | andLeft {A B : Prop} (right : Code prepared B) (later : Kont prepared goal (A ∧ B)) : Kont prepared goal A
  | andRight {A B : Prop} (left : Check prepared A) (holds : A) (decision : left.decision = .isTrue holds)
      (later : Kont prepared goal (A ∧ B)) : Kont prepared goal B
  | impLeft {A B : Prop} (right : Code prepared B) (later : Kont prepared goal (A → B)) : Kont prepared goal A
  | impRight {A B : Prop} (left : Check prepared A) (holds : A) (decision : left.decision = .isTrue holds)
      (later : Kont prepared goal (A → B)) : Kont prepared goal B
/-- Completion semantics is proof-only during cursor execution. -/
def Kont.apply {goal A : Prop} : Kont prepared goal A → Check prepared A → Check prepared goal
  | .done,checked => checked
  | .transport equivalent later,checked => later.apply (Work.transport equivalent checked)
  | .negative later,checked => later.apply (Work.negative checked)
  | .andLeft right later,checked => later.apply (Work.conjunction checked (fun _ => right.eval))
  | .andRight left _ _ later,checked => later.apply (Work.conjunction left (fun _ => checked))
  | .impLeft right later,checked => later.apply (Work.implication checked (fun _ => right.eval))
  | .impRight left _ _ later,checked => later.apply (Work.implication left (fun _ => checked))
def Kont.weight {goal A : Prop} : Kont prepared goal A → Nat
  | .done => 0
  | .transport _ later | .negative later => later.weight+1
  | .andLeft right later | .impLeft right later => 2*right.weight+later.weight+3
  | .andRight _ _ _ later | .impRight _ _ _ later => later.weight+2

variable {goal : Prop} (original : Code prepared goal)
inductive State where
  | evaluating {A : Prop} (code : Code prepared A) (kont : Kont prepared goal A) (coherent : kont.apply code.eval = original.eval)
  | returning {A : Prop} (checked : Check prepared A) (kont : Kont prepared goal A) (coherent : kont.apply checked = original.eval)
  | finished (checked : Check prepared goal) (generated : checked = original.eval)
def initial : State original := .evaluating original .done rfl
inductive Event where
  | opened | returned | branch (accepted : Bool)
  | row (reference term : Section prepared) (row : Row prepared)
  | benefit (new previous : Section prepared) (index : Index prepared)
  | completed (checked : Check prepared goal) (generated : checked = original.eval)
def move : State original → Option (State original × Event original)
  | .evaluating .truth kont coherent => some (.returning Builders.trueCheck kont coherent,.returned)
  | .evaluating (.row reference term entry) kont coherent => some (.returning (atom prepared reference term entry) kont coherent,.row reference term entry)
  | .evaluating (.benefit new previous index) kont coherent => some (.returning
      (localImprovement prepared index prepared.saved[index].stage (readTerm prepared new index) (readTerm prepared previous index)) kont coherent,.benefit new previous index)
  | .evaluating (.conjunction left right) kont coherent => some (.evaluating left (.andLeft right kont) coherent,.opened)
  | .evaluating (.negative body) kont coherent => some (.evaluating body (.negative kont) coherent,.opened)
  | .evaluating (.implication left right) kont coherent => some (.evaluating left (.impLeft right kont) coherent,.opened)
  | .evaluating (.transport equivalent body) kont coherent => some (.evaluating body (.transport equivalent kont) coherent,.opened)
  | .returning checked .done coherent => some (.finished checked coherent,.completed checked coherent)
  | .returning checked (.transport equivalent later) coherent => some (.returning (Work.transport equivalent checked) later coherent,.returned)
  | .returning checked (.negative later) coherent => some (.returning (Work.negative checked) later coherent,.returned)
  | .returning checked (.andLeft right later) coherent => match decision : checked.decision with
    | .isFalse broken => some (.returning (Builders.andFalse checked broken) later (by
        rw [Builders.andFalse_exact checked broken decision right.eval];exact coherent),.branch false)
    | .isTrue holds => some (.evaluating right (.andRight checked holds decision later) coherent,.branch true)
  | .returning checked (.impLeft right later) coherent => match decision : checked.decision with
    | .isFalse broken => some (.returning (Builders.impFalse checked broken) later (by
        rw [Builders.impFalse_exact checked broken decision right.eval];exact coherent),.branch false)
    | .isTrue holds => some (.evaluating right (.impRight checked holds decision later) coherent,.branch true)
  | .returning checked (.andRight left _ _ later) coherent => some (.returning (Work.conjunction left (fun _ => checked)) later coherent,.returned)
  | .returning checked (.impRight left _ _ later) coherent => some (.returning (Work.implication left (fun _ => checked)) later coherent,.returned)
  | .finished .. => none

def State.rank : State original → Nat
  | .evaluating code kont _ => 2*code.weight+kont.weight+1
  | .returning _ kont _ => kont.weight+1
  | .finished .. => 0
def State.done : State original → Bool | .finished .. => true | _ => false
theorem progress {before after : State original} {event : Event original}
    (actual : move original before = some (after,event)) : after.rank original < before.rank original := by
  cases before with
  | evaluating code kont coherent =>
      cases code <;> dsimp only [move] at actual <;> cases Option.some.inj actual
      all_goals simp only [State.rank,Code.weight,Kont.weight];omega
  | returning checked kont coherent =>
      cases kont <;> dsimp only [move] at actual
      all_goals first
        | (cases Option.some.inj actual;simp only [State.rank,Kont.weight];omega)
        | (split at actual <;> cases Option.some.inj actual <;> simp only [State.rank,Kont.weight] <;> omega)
  | finished => cases actual
theorem no_move_iff_done (before : State original) : move original before = none ↔ before.done original = true := by
  cases before with
  | evaluating code => cases code <;> simp [move,State.done]
  | returning checked kont =>
      cases kont <;> dsimp only [move,State.done]
      all_goals first | (solve | simp) | (split <;> simp)
  | finished => simp [move,State.done]
namespace Rejection
variable (reference term : Section prepared) (items : List (Row prepared))
  (inside : ∀ row ∈ items,row ∈ rows prepared) (invalid : ¬∀ row ∈ items,Holds prepared reference term row)
inductive State where
  | walking (remaining : List (Row prepared)) (inside : ∀ row ∈ remaining,row ∈ rows prepared)
      (invalid : ¬∀ row ∈ remaining,Holds prepared reference term row)
      (wrap : Rejected prepared reference term → Rejected prepared reference term)
      (coherent : wrap (Builders.rejectSpecification term remaining inside invalid) = Builders.rejectSpecification term items ‹_› ‹_›)
  | checked (head : Row prepared) (tail : List (Row prepared)) (inside : ∀ row ∈ head::tail,row ∈ rows prepared)
      (invalid : ¬∀ row ∈ head::tail,Holds prepared reference term row)
      (wrap : Rejected prepared reference term → Rejected prepared reference term)
      (coherent : wrap (Builders.rejectSpecification term (head::tail) inside invalid) = Builders.rejectSpecification term items ‹_› ‹_›)
      (checked : Check prepared (Holds prepared reference term head)) (actual : checked = atom prepared reference term head)
  | finished (report : Rejected prepared reference term) (generated : report = Builders.rejectSpecification term items inside invalid)
def initial : State reference term items inside invalid := .walking items inside invalid id rfl
inductive Event where
  | checked (row : Row prepared) (check : Check prepared (Holds prepared reference term row)) (actual : check = atom prepared reference term row)
  | passed (row : Row prepared)
  | completed (report : Rejected prepared reference term) (generated : report = Builders.rejectSpecification term items inside invalid)
def move : State reference term items inside invalid → Option (State reference term items inside invalid × Event reference term items inside invalid)
  | .walking [] _ impossible _ _ => False.elim (impossible (by simp))
  | .walking (head::tail) inRows bad wrap coherent =>
      let checked := atom prepared reference term head
      some (.checked head tail inRows bad wrap coherent checked rfl,.checked head checked rfl)
  | .checked head tail inRows bad wrap coherent checked actual => match decision : checked.decision with
    | .isFalse broken =>
        let report := wrap (Builders.rejectAt term head tail inRows checked broken)
        let exact : report = Builders.rejectSpecification term items inside invalid := by
          dsimp only [report];rw [Builders.rejectAt_exact term head tail inRows bad checked actual broken decision];exact coherent
        some (.finished report exact,.completed report exact)
    | .isTrue holds =>
        some (.walking tail (fun row member => inRows row (List.mem_cons_of_mem _ member))
          (Builders.tailInvalid term head tail bad holds) (fun later => wrap (Builders.rejectAfter term head checked later)) (by
            rw [Builders.rejectAfter_exact term head tail inRows bad checked actual holds decision];exact coherent),.passed head)
  | .finished .. => none
def State.rank : State reference term items inside invalid → Nat
  | .walking remaining .. => 2*remaining.length+1
  | .checked _ tail .. => 2*tail.length+2
  | .finished .. => 0
def State.done : State reference term items inside invalid → Bool | .finished .. => true | _ => false
theorem progress {before after : State reference term items inside invalid} {event : Event reference term items inside invalid}
    (actual : move reference term items inside invalid before = some (after,event)) : after.rank reference term items inside invalid < before.rank reference term items inside invalid := by
  cases before with
  | walking remaining inRows bad =>
      cases remaining with
      | nil => exact False.elim (bad (by simp))
      | cons => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,List.length_cons];omega
  | checked =>
      dsimp only [move] at actual;split at actual
      all_goals cases Option.some.inj actual;simp only [State.rank];omega
  | finished => cases actual
theorem no_move_iff_done (before : State reference term items inside invalid) : move reference term items inside invalid before = none ↔ before.done reference term items inside invalid = true := by
  cases before with
  | walking remaining inRows bad =>
      cases remaining with
      | nil => exact False.elim (bad (by simp))
      | cons => simp [move,State.done]
  | checked => dsimp only [move,State.done];split <;> simp
  | finished => simp [move,State.done]
end Rejection
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Work.Checks
