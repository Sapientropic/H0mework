import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceBudgetMachine
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
 {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
 {input : Input seed} (prepared : Prepared input)

inductive Source where
 | sections | rows | admission | keys | benefit
 deriving DecidableEq

def Source.expected : Source → Nat
 | .sections => (Policy.sections prepared).length
 | .rows => (Policy.rows prepared).length
 | .admission => Work.admissionCeiling prepared
 | .keys => (Policy.keys prepared).length
 | .benefit => Work.benefitCeiling prepared

/-- Invoked by the paid source instruction, never supplied as a finished budget. -/
def Source.calculate : (source : Source) → Budget.Run prepared (source.expected prepared)
 | .sections => Budget.length (Policy.sections prepared)
 | .rows => Budget.length (Policy.rows prepared)
 | .admission => Budget.admissionCeiling prepared
 | .keys => Budget.length (Policy.keys prepared)
 | .benefit => Budget.benefitCeiling prepared

inductive Instruction where
 | source (field : Source)
 | literal (value : Nat)
 | cached (slot : Fin 5)
 | save (slot : Fin 5)
 | add | multiply | maximum
 deriving DecidableEq

structure Core where
 stack : List Nat
 memory : Fin 5 → Option Nat

def initial : Core := ⟨[],fun _ => none⟩
def push (core : Core) (value : Nat) : Core := {core with stack := value :: core.stack}
def store (core : Core) (slot : Fin 5) (value : Nat) (rest : List Nat) : Core :=
 ⟨rest,fun key => if key=slot then some value else core.memory key⟩

def step (fetch : Source → Nat) (instruction : Instruction) (core : Core) : Option Core :=
 match instruction with
 | .source field => some (push core (fetch field))
 | .literal value => some (push core value)
 | .cached slot => (core.memory slot).map (push core)
 | .save slot => match core.stack with
   | [] => none
   | value::rest => some (store core slot value rest)
 | .add => match core.stack with
   | right::left::rest => some {core with stack := (left+right)::rest}
   | _ => none
 | .multiply => match core.stack with
   | right::left::rest => some {core with stack := (left*right)::rest}
   | _ => none
 | .maximum => match core.stack with
   | right::left::rest => some {core with stack := (max left right)::rest}
   | _ => none

/-- This is the original five cached budget registers, compiled without reading their values. -/
def code : List Instruction :=
 [.source .sections,.save 0,
  .source .rows,.source .admission,.literal 1,.add,.multiply,.save 1,
  .source .keys,.source .benefit,.literal 1,.add,.multiply,.save 2,
  .literal 2,.cached 2,.multiply,.literal 2,.add,.save 3,
  .cached 1,.literal 1,.add,.cached 0,.cached 1,.cached 3,.add,.literal 3,.add,.multiply,.add,.save 4,
  .cached 0,.cached 1,.literal 1,.add,.multiply,
  .cached 0,.cached 3,.literal 1,.add,.multiply,.add,
  .cached 4,.add,.cached 0,.cached 1,.multiply,.add,.literal 1,.add]

def runPure (fetch : Source → Nat) : List Instruction → Core → Option Core
 | [],core => some core
 | head::tail,core => (step fetch head core).bind (runPure fetch tail)

def formula (count rowCount admission keyCount benefit : Nat) : Nat :=
 let admitted := rowCount*(admission+1)
 let improved := keyCount*(benefit+1)
 let strict := 2*improved+2
 let verification := admitted+1+count*(admitted+strict+3)
 count*(admitted+1)+count*(strict+1)+verification+count*admitted+1

theorem the_fixed_program_computes_the_original_formula (count rowCount admission keyCount benefit : Nat) :
 ((runPure (fun field => match field with
   | .sections => count | .rows => rowCount | .admission => admission | .keys => keyCount | .benefit => benefit)
   code initial).map (fun core => core.stack.head?)) =
 some (some (formula count rowCount admission keyCount benefit)) := by rfl

theorem the_source_program_computes_the_original_work_budget :
 ((runPure (Source.expected prepared) code initial).map (fun core => core.stack.head?)) =
 some (some (Work.workBudget prepared)) := by
 exact the_fixed_program_computes_the_original_formula (Policy.sections prepared).length
  (Policy.rows prepared).length (Work.admissionCeiling prepared)
  (Policy.keys prepared).length (Work.benefitCeiling prepared)

structure Update (instruction : Instruction) (before : Core) where
 private mk ::
 after : Core
 exact : step (Source.expected prepared) instruction before = some after
 work : List (Budget.Event prepared)
 valid : ∀ event ∈ work,event.Valid prepared

inductive Evaluation (instruction : Instruction) (before : Core) where
 | invalid (why : step (Source.expected prepared) instruction before = none)
 | done (made : Update prepared instruction before)

def evaluate (instruction : Instruction) (before : Core) : Evaluation prepared instruction before :=
 match instruction with
 | .source field =>
   let made := field.calculate prepared
   .done ⟨push before made.value,by dsimp only [step];rw [made.exact],made.work,made.sound⟩
 | .literal value => .done ⟨push before value,rfl,[.literal value],by simp [Budget.Event.Valid]⟩
 | .cached slot =>
   match saved : before.memory slot with
   | none => .invalid (by simp only [step,saved,Option.map_none])
   | some value => .done ⟨push before value,by simp only [step,saved,Option.map_some],
       [.reuse slot.val value],by simp [Budget.Event.Valid]⟩
 | .save slot =>
   match saved : before.stack with
   | [] => .invalid (by simp only [step,saved])
   | value::rest => .done ⟨store before slot value rest,by simp only [step,saved],
       [.branch .nativeRow],by simp [Budget.Event.Valid]⟩
 | .add =>
   match saved : before.stack with
   | right::left::rest => .done ⟨{before with stack := (left+right)::rest},by simp only [step,saved],
       [.add left right (left+right)],by simp [Budget.Event.Valid]⟩
   | [] => .invalid (by simp only [step,saved])
   | [_] => .invalid (by simp only [step,saved])
 | .multiply =>
   match saved : before.stack with
   | right::left::rest => .done ⟨{before with stack := (left*right)::rest},by simp only [step,saved],
       [.multiply left right (left*right)],by simp [Budget.Event.Valid]⟩
   | [] => .invalid (by simp only [step,saved])
   | [_] => .invalid (by simp only [step,saved])
 | .maximum =>
   match saved : before.stack with
   | right::left::rest => .done ⟨{before with stack := (max left right)::rest},by simp only [step,saved],
       [.maximum left right (max left right)],by simp [Budget.Event.Valid]⟩
   | [] => .invalid (by simp only [step,saved])
   | [_] => .invalid (by simp only [step,saved])

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceBudgetMachine
