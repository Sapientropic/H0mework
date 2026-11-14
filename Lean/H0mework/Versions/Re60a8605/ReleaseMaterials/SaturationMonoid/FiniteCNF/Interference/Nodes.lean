import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Action

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram

def bit (b : Bool) : ℤ := if b then 1 else 0
def truth (z : ℤ) : Bool := z != 0
def sign (z : ℤ) : ℤ := if z = 0 then 1 else -1

inductive Node where
  | constant : ℤ → Node
  | input : Nat → Node
  | add : Nat → Nat → Node
  | mul : Nat → Nat → Node
  | neg : Nat → Node
  | band : Nat → Nat → Node
  | bxor : Nat → Nat → Node
  | bnot : Nat → Node
  | phase : Nat → Node
  | select : Nat → Nat → Nat → Node
  deriving DecidableEq, Repr

def Node.refs : Node → List Nat
  | .constant _ | .input _ => []
  | .add a b | .mul a b | .band a b | .bxor a b => [a,b]
  | .neg a | .bnot a | .phase a => [a]
  | .select c a b => [c,a,b]

def Node.run (environment : Nat → Bool) (values : Array ℤ) : Node → ℤ
  | .constant z => z
  | .input i => bit (environment i)
  | .add a b => values.getD a 0 + values.getD b 0
  | .mul a b => values.getD a 0 * values.getD b 0
  | .neg a => -values.getD a 0
  | .band a b => bit (truth (values.getD a 0) && truth (values.getD b 0))
  | .bxor a b => bit (truth (values.getD a 0) ^^ truth (values.getD b 0))
  | .bnot a => bit (!truth (values.getD a 0))
  | .phase a => sign (values.getD a 0)
  | .select c a b => if values.getD c 0 = 0 then values.getD a 0 else values.getD b 0

def Node.shift (offset : Nat) : Node → Node
  | .constant z => .constant z
  | .input i => .input i
  | .add a b => .add (offset+a) (offset+b)
  | .mul a b => .mul (offset+a) (offset+b)
  | .neg a => .neg (offset+a)
  | .band a b => .band (offset+a) (offset+b)
  | .bxor a b => .bxor (offset+a) (offset+b)
  | .bnot a => .bnot (offset+a)
  | .phase a => .phase (offset+a)
  | .select c a b => .select (offset+c) (offset+a) (offset+b)

def Node.cofactor (address : Nat) (value : Bool) : Node → Node
  | .input i => if i = address then .constant (bit value) else .input i
  | node => node

def runCode (environment : Nat → Bool) : Array ℤ → List Node → Array ℤ
  | values, [] => values
  | values, node :: rest => runCode environment (values.push (node.run environment values)) rest

def run (environment : Nat → Bool) (code : Array Node) : Array ℤ :=
  runCode environment #[] code.toList

theorem runCode_size (environment : Nat → Bool) (values : Array ℤ) (code : List Node) :
    (runCode environment values code).size = values.size + code.length := by
  induction code generalizing values with
  | nil => simp [runCode]
  | cons node rest ih => simp only [runCode, ih, Array.size_push, List.length_cons]; omega

@[simp] theorem run_size (environment : Nat → Bool) (code : Array Node) :
    (run environment code).size = code.size := by simp [run, runCode_size]

theorem runCode_append (environment : Nat → Bool) (values : Array ℤ) (a b : List Node) :
    runCode environment values (a ++ b) = runCode environment (runCode environment values a) b := by
  induction a generalizing values with
  | nil => rfl
  | cons node rest ih => exact ih _

theorem getD_append_right (headValues values : Array ℤ) (i : Nat) :
    (headValues ++ values).getD (headValues.size+i) 0 = values.getD i 0 := by
  simp [Array.getD]

theorem getD_append_left (headValues values : Array ℤ) (i : Nat) (h : i < headValues.size) :
    (headValues ++ values).getD i 0 = headValues.getD i 0 := by
  have bound : i < headValues.size + values.size := by omega
  simp [Array.getD, h, bound]

theorem Node.run_shift (environment : Nat → Bool) (headValues values : Array ℤ) (node : Node) :
    (node.shift headValues.size).run environment (headValues ++ values) = node.run environment values := by
  cases node <;> simp only [Node.shift, Node.run, getD_append_right]

theorem push_append (headValues values : Array ℤ) (z : ℤ) :
    (headValues ++ values).push z = headValues ++ values.push z := by
  apply Array.toList_inj.mp
  simp

theorem runCode_shift (environment : Nat → Bool) (headValues values : Array ℤ) (code : List Node) :
    runCode environment (headValues ++ values) (code.map (Node.shift headValues.size)) =
      headValues ++ runCode environment values code := by
  induction code generalizing values with
  | nil => rfl
  | cons node rest ih =>
      simp only [List.map_cons, runCode, Node.run_shift, push_append, ih]

theorem run_join (environment : Nat → Bool) (left right : Array Node) :
    run environment (left ++ right.map (Node.shift left.size)) =
      run environment left ++ run environment right := by
  simp only [run, Array.toList_append, Array.toList_map, runCode_append]
  have eqn := runCode_shift environment (run environment left) #[] right.toList
  simp only [Array.append_empty, run_size] at eqn
  exact eqn

theorem Node.run_cofactor (environment : Nat → Bool) (values : Array ℤ)
    (address : Nat) (value : Bool) (node : Node) :
    (node.cofactor address value).run environment values =
      node.run (Function.update environment address value) values := by
  cases node <;> try rfl
  rename_i i
  by_cases same : i = address <;> simp [Node.cofactor, Node.run, same]

theorem runCode_cofactor (environment : Nat → Bool) (values : Array ℤ)
    (address : Nat) (value : Bool) (code : List Node) :
    runCode environment values (code.map (Node.cofactor address value)) =
      runCode (Function.update environment address value) values code := by
  induction code generalizing values with
  | nil => rfl
  | cons node rest ih => simp only [List.map_cons, runCode, Node.run_cofactor, ih]

theorem run_cofactor (environment : Nat → Bool) (address : Nat) (value : Bool) (code : Array Node) :
    run environment (code.map (Node.cofactor address value)) =
      run (Function.update environment address value) code := by
  simp only [run, Array.toList_map, runCode_cofactor]

theorem run_push (environment : Nat → Bool) (code : Array Node) (node : Node) :
    run environment (code.push node) =
      (run environment code).push (node.run environment (run environment code)) := by
  simp only [run, Array.toList_push, runCode_append, runCode]

theorem getD_push_last (values : Array ℤ) (z : ℤ) :
    (values.push z).getD values.size 0 = z := by simp [Array.getD]

theorem getD_push_old (values : Array ℤ) (z : ℤ) (i : Nat) (h : i < values.size) :
    (values.push z).getD i 0 = values.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?]
  simp [Array.getElem?_push, Nat.ne_of_lt h]

structure Fragment where
  code : Array Node
  output : Fin code.size
  deriving Repr

def Fragment.eval (environment : Nat → Bool) (fragment : Fragment) : ℤ :=
  (run environment fragment.code).getD fragment.output.val 0

def Fragment.constant (z : ℤ) : Fragment := ⟨#[.constant z], ⟨0, by simp⟩⟩
def Fragment.input (address : Nat) : Fragment := ⟨#[.input address], ⟨0, by simp⟩⟩

def Fragment.unary (fragment : Fragment) (node : Nat → Node) : Fragment :=
  ⟨fragment.code.push (node fragment.output.val), ⟨fragment.code.size, by simp⟩⟩

def Fragment.binary (left right : Fragment) (node : Nat → Nat → Node) : Fragment :=
  let code := left.code ++ right.code.map (Node.shift left.code.size)
  ⟨code.push (node left.output.val (left.code.size+right.output.val)), ⟨code.size, by simp⟩⟩

@[simp] theorem Fragment.eval_constant (environment : Nat → Bool) (z : ℤ) :
    (constant z).eval environment = z := by simp [constant, eval, run, runCode, Node.run, Array.getD]

@[simp] theorem Fragment.eval_input (environment : Nat → Bool) (address : Nat) :
    (input address).eval environment = bit (environment address) := by
  simp [input, eval, run, runCode, Node.run, Array.getD]

theorem Fragment.eval_unary (environment : Nat → Bool) (fragment : Fragment) (node : Nat → Node) :
    (fragment.unary node).eval environment =
      (node fragment.output.val).run environment (run environment fragment.code) := by
  simp only [unary, eval, run_push]
  simpa only [run_size] using getD_push_last (run environment fragment.code)
    ((node fragment.output.val).run environment (run environment fragment.code))

theorem Fragment.eval_binary (environment : Nat → Bool) (left right : Fragment)
    (node : Nat → Nat → Node) :
    (left.binary right node).eval environment =
      (node left.output.val (left.code.size+right.output.val)).run environment
        (run environment left.code ++ run environment right.code) := by
  simp only [binary, eval, run_push]
  rw [← run_size environment (left.code ++ right.code.map (Node.shift left.code.size)), getD_push_last]
  rw [run_join]

def Fragment.and (left right : Fragment) : Fragment := left.binary right Node.band
def Fragment.xor (left right : Fragment) : Fragment := left.binary right Node.bxor
def Fragment.not (fragment : Fragment) : Fragment := fragment.unary Node.bnot

@[simp] theorem Fragment.eval_and (environment : Nat → Bool) (left right : Fragment) :
    (left.and right).eval environment = bit (truth (left.eval environment) && truth (right.eval environment)) := by
  rw [and, eval_binary]
  simp only [Node.run, ← run_size environment left.code, getD_append_right]
  rw [getD_append_left _ _ _ (by simp)]
  rfl

@[simp] theorem Fragment.eval_xor (environment : Nat → Bool) (left right : Fragment) :
    (left.xor right).eval environment = bit (truth (left.eval environment) ^^ truth (right.eval environment)) := by
  rw [xor, eval_binary]
  simp only [Node.run, ← run_size environment left.code, getD_append_right]
  rw [getD_append_left _ _ _ (by simp)]
  rfl

@[simp] theorem Fragment.eval_not (environment : Nat → Bool) (fragment : Fragment) :
    fragment.not.eval environment = bit (!truth (fragment.eval environment)) := by
  rw [not, eval_unary]
  rfl

@[simp] theorem truth_bit (b : Bool) : truth (bit b) = b := by cases b <;> rfl

def compileLiteral {n : Nat} (lit : CNFLiteral n) : Fragment :=
  if lit.positive then (Fragment.input lit.var.val).not else Fragment.input lit.var.val

def compileClause {n : Nat} : CNFClause n → Fragment
  | [] => Fragment.constant 1
  | lit :: rest => (compileLiteral lit).and (compileClause rest)

def compilePhase {n : Nat} (offset : Nat) : CNFFormula n → Fragment
  | [] => Fragment.constant 0
  | clause :: rest =>
      ((Fragment.input offset).and (compileClause clause)).xor (compilePhase (offset+1) rest)

theorem eval_compileLiteral {n : Nat} (lit : CNFLiteral n) (environment : Nat → Bool) :
    (compileLiteral lit).eval environment = bit (!(CNFLiteral.eval lit environment)) := by
  cases hp : lit.positive <;> simp [compileLiteral, hp, CNFLiteral.eval, bit, truth]

theorem eval_compileClause {n : Nat} (clause : CNFClause n) (environment : Nat → Bool) :
    (compileClause clause).eval environment = bit (!(CNFClause.eval clause environment)) := by
  induction clause with
  | nil => simp [compileClause, CNFClause.eval, bit]
  | cons lit rest ih =>
      simp only [compileClause, Fragment.eval_and, eval_compileLiteral, ih, truth_bit,
        CNFClause.eval, List.any_cons, Bool.not_or]

def phaseValue {n : Nat} (offset : Nat) (environment : Nat → Bool) : CNFFormula n → Bool
  | [] => false
  | clause :: rest => (environment offset && !(CNFClause.eval clause environment)) ^^
      phaseValue (offset+1) environment rest

theorem eval_compilePhase {n : Nat} (offset : Nat) (formula : CNFFormula n) (environment : Nat → Bool) :
    (compilePhase offset formula).eval environment = bit (phaseValue offset environment formula) := by
  induction formula generalizing offset with
  | nil => simp [compilePhase, phaseValue, bit]
  | cons clause rest ih =>
      simp only [compilePhase, Fragment.eval_xor, Fragment.eval_and, Fragment.eval_input,
        eval_compileClause, ih, truth_bit, phaseValue]

theorem getD_push_any (values : Array ℤ) (z : ℤ) (i : Nat) :
    (values.push z).getD i 0 = if i = values.size then z else values.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?]
  by_cases same : i = values.size <;> simp [Array.getElem?_push, same]

end SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram
