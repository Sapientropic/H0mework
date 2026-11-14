import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.Nodes

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram

structure Program where
  code : Array Node
  weight : Fin code.size
  phase : Fin code.size
  deriving Repr

def Program.eval (program : Program) (environment : Nat → Bool) : ℤ :=
  let values := run environment program.code
  values.getD program.weight.val 0 * sign (values.getD program.phase.val 0)

def compile {n : Nat} (formula : CNFFormula n) : Program :=
  let phase := compilePhase n formula
  ⟨phase.code.push (.constant 1), ⟨phase.code.size, by simp⟩,
    ⟨phase.output.val, by have h := phase.output.isLt; simp only [Array.size_push]; omega⟩⟩

theorem eval_compile {n : Nat} (formula : CNFFormula n) (environment : Nat → Bool) :
    (compile formula).eval environment = sign (bit (phaseValue n environment formula)) := by
  simp only [compile, Program.eval, run_push, Node.run]
  have last := getD_push_last (run environment (compilePhase n formula).code) 1
  rw [run_size] at last
  rw [last, one_mul, getD_push_old _ _ _ (by simp)]
  exact congrArg sign (eval_compilePhase n formula environment)

def Program.cofactor (program : Program) (address : Nat) (value : Bool) : Program :=
  ⟨program.code.map (Node.cofactor address value),
    ⟨program.weight.val, by simp⟩,
    ⟨program.phase.val, by simp⟩⟩

@[simp] theorem Program.cofactor_size (program : Program) (address : Nat) (value : Bool) :
    (program.cofactor address value).code.size = program.code.size := by simp [cofactor]

theorem Program.eval_cofactor (program : Program) (address : Nat) (value : Bool)
    (environment : Nat → Bool) :
    (program.cofactor address value).eval environment =
      program.eval (Function.update environment address value) := by
  simp only [cofactor, eval, run_cofactor]

/-- The second binding owns its value if two raw addresses coincide. -/
def Program.cofactorPair (program : Program) (a b : Nat) (x y : Bool) : Program :=
  (program.cofactor b y).cofactor a x

theorem Program.eval_cofactorPair (program : Program) (a b : Nat) (x y : Bool)
    (environment : Nat → Bool) :
    (program.cofactorPair a b x y).eval environment =
      program.eval (Function.update (Function.update environment a x) b y) := by
  rw [cofactorPair, eval_cofactor, eval_cofactor]

def join (left right : Array Node) : Array Node := left ++ right.map (Node.shift left.size)

@[simp] theorem join_size (left right : Array Node) : (join left right).size = left.size+right.size := by
  simp [join]

theorem run_join' (environment : Nat → Bool) (left right : Array Node) :
    run environment (join left right) = run environment left ++ run environment right :=
  run_join environment left right

def copies (program : Program) (a b : Nat) : Array Node :=
  join (join (join (program.cofactorPair a b false false).code
    (program.cofactorPair a b false true).code)
    (program.cofactorPair a b true false).code)
    (program.cofactorPair a b true true).code

@[simp] theorem copies_size (program : Program) (a b : Nat) :
    (copies program a b).size = 4 * program.code.size := by
  simp [copies, Program.cofactorPair]
  omega

/-- Each branch refers to the same four already-generated cofactor blocks.
The final select retains both values of the generated mixed phase. -/
def pairTail (size weight phase : Nat) : Array Node := #[
  .bxor (2*size+phase) phase,
  .bxor (size+phase) phase,
  .bxor (3*size+phase) (2*size+phase),
  .bxor (4*size+2) (4*size+1),
  .phase (4*size),
  .phase (4*size+1),
  .bxor (4*size) (4*size+1),
  .phase (4*size+6),
  .mul (4*size+4) (2*size+weight),
  .mul (4*size+5) (size+weight),
  .mul (4*size+7) (3*size+weight),
  .add weight (4*size+8),
  .add (4*size+11) (4*size+9),
  .add (4*size+12) (4*size+10),
  .neg (4*size+10),
  .add (4*size+12) (4*size+14),
  .select (4*size+3) (4*size+13) (4*size+15)]

def Program.eliminatePair (program : Program) (a b : Nat) : Program :=
  ⟨copies program a b ++ pairTail program.code.size program.weight.val program.phase.val,
    ⟨4*program.code.size+16, by simp [pairTail]⟩,
    ⟨program.phase.val, by have h := program.phase.isLt; simp only [Array.size_append, copies_size]; simp [pairTail]; omega⟩⟩

@[simp] theorem Program.eliminatePair_size (program : Program) (a b : Nat) :
    (program.eliminatePair a b).code.size = 4 * program.code.size + 17 := by
  simp [eliminatePair, pairTail]

theorem runCode_before (environment : Nat → Bool) (values : Array ℤ) (code : List Node)
    (i : Nat) (bound : i < values.size) :
    (runCode environment values code).getD i 0 = values.getD i 0 := by
  induction code generalizing values with
  | nil => rfl
  | cons node rest ih =>
      rw [runCode, ih _ (by simp only [Array.size_push]; omega), getD_push_old _ _ _ bound]

end SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram
