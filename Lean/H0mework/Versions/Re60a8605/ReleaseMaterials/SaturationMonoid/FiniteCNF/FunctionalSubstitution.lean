import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.BooleanValues

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.FunctionalSubstitution

open InterferenceProgram

/-- The body is generated once; every occurrence of the input reads this shared prefix. -/
def rewrite (address offset output : Nat) : Node → Node
  | .input i => if i = address then .band output output else .input i
  | node => node.shift offset

def bind (address : Nat) (body : Fragment) (environment : Nat → Bool) : Nat → Bool :=
  Function.update environment address (truth (body.eval environment))

theorem node_rewrite (address : Nat) (body : Fragment) (environment : Nat → Bool)
    (values : Array ℤ) (node : Node) :
    (rewrite address body.code.size body.output.val node).run environment
      (run environment body.code ++ values) = node.run (bind address body environment) values := by
  cases node <;> simp only [rewrite]
  case input i =>
    by_cases same : i = address
    · simp only [same, if_true, Node.run]
      rw [getD_append_left _ _ _ (by simp)]
      simp only [Bool.and_self, bind, Function.update_self, Fragment.eval]
    · simp [same, Node.run, bind]
  all_goals
    rw [← run_size environment body.code, Node.run_shift]
    rfl

theorem runCode_rewrite (address : Nat) (body : Fragment) (environment : Nat → Bool)
    (values : Array ℤ) (code : List Node) :
    runCode environment (run environment body.code ++ values)
      (code.map (rewrite address body.code.size body.output.val)) =
      run environment body.code ++ runCode (bind address body environment) values code := by
  induction code generalizing values with
  | nil => rfl
  | cons node rest ih =>
      simp only [List.map_cons, runCode, node_rewrite, push_append]
      exact ih _

def substitute (program : Program) (address : Nat) (body : Fragment) : Program :=
  let code := body.code ++ program.code.map (rewrite address body.code.size body.output.val)
  ⟨code,
    ⟨body.code.size + program.weight.val, by
      simpa only [code, Array.size_append, Array.size_map] using
        Nat.add_lt_add_left program.weight.isLt body.code.size⟩,
    ⟨body.code.size + program.phase.val, by
      simpa only [code, Array.size_append, Array.size_map] using
        Nat.add_lt_add_left program.phase.isLt body.code.size⟩⟩

theorem run_substitute (program : Program) (address : Nat) (body : Fragment)
    (environment : Nat → Bool) :
    run environment (substitute program address body).code =
      run environment body.code ++ run (bind address body environment) program.code := by
  simp only [substitute, run, Array.toList_append, Array.toList_map, runCode_append]
  simpa only [Array.append_empty, run] using runCode_rewrite address body environment #[] program.code.toList

theorem eval_substitute (program : Program) (address : Nat) (body : Fragment)
    (environment : Nat → Bool) :
    (substitute program address body).eval environment = program.eval (bind address body environment) := by
  simp only [Program.eval]
  rw [run_substitute]
  simp only [substitute]
  rw [← run_size environment body.code, getD_append_right, getD_append_right]

theorem substitute_size (program : Program) (address : Nat) (body : Fragment) :
    (substitute program address body).code.size = body.code.size + program.code.size := by
  simp only [substitute, Array.size_append, Array.size_map]

def Node.Free (address : Nat) : Node → Prop
  | .input i => i ≠ address
  | _ => True

def Free (address : Nat) (code : Array Node) : Prop := ∀ node ∈ code.toList, Node.Free address node

theorem node_free_update (address : Nat) (node : Node) (free : Node.Free address node)
    (environment : Nat → Bool) (value : Bool) (values : Array ℤ) :
    node.run (Function.update environment address value) values = node.run environment values := by
  cases node <;> try rfl
  simp only [Node.Free] at free
  simp [Node.run, free]

theorem runCode_free_update (address : Nat) (code : List Node)
    (free : ∀ node ∈ code, Node.Free address node) (environment : Nat → Bool)
    (value : Bool) (values : Array ℤ) :
    runCode (Function.update environment address value) values code = runCode environment values code := by
  induction code generalizing values with
  | nil => rfl
  | cons node rest ih =>
      simp only [runCode, node_free_update address node (free node (by simp))]
      exact ih (fun other member => free other (by simp [member])) _

theorem run_free_update (address : Nat) (code : Array Node) (free : Free address code)
    (environment : Nat → Bool) (value : Bool) :
    run (Function.update environment address value) code = run environment code :=
  runCode_free_update address code.toList free environment value #[]

theorem eval_free_update (address : Nat) (body : Fragment) (free : Free address body.code)
    (environment : Nat → Bool) (value : Bool) :
    body.eval (Function.update environment address value) = body.eval environment := by
  simp only [Fragment.eval, run_free_update address body.code free]

theorem rewrite_free_self (address offset output : Nat) (node : Node) :
    Node.Free address (rewrite address offset output node) := by
  cases node <;> try trivial
  rename_i i
  by_cases same : i = address <;> simp [rewrite, same, Node.Free]

theorem rewrite_free (address other offset output : Nat) (node : Node)
    (free : Node.Free other node) : Node.Free other (rewrite address offset output node) := by
  cases node <;> try trivial
  rename_i i
  by_cases same : i = address <;> simp_all [rewrite, Node.Free]

theorem substitute_free_self (program : Program) (address : Nat) (body : Fragment)
    (free : Free address body.code) : Free address (substitute program address body).code := by
  intro node member
  simp only [substitute, Array.toList_append, Array.toList_map, List.mem_append, List.mem_map] at member
  rcases member with member | ⟨original, _, rfl⟩
  · exact free node member
  · exact rewrite_free_self address _ _ original

theorem substitute_free (program : Program) (address other : Nat) (body : Fragment)
    (first : Free other program.code) (second : Free other body.code) :
    Free other (substitute program address body).code := by
  intro node member
  simp only [substitute, Array.toList_append, Array.toList_map, List.mem_append, List.mem_map] at member
  rcases member with member | ⟨original, member, rfl⟩
  · exact second node member
  · exact rewrite_free address other _ _ original (first original member)

theorem bind_fixes (address : Nat) (body : Fragment) (environment : Nat → Bool)
    (holds : environment address = truth (body.eval environment)) : bind address body environment = environment := by
  simp [bind, ← holds]

theorem bind_holds (address : Nat) (body : Fragment) (free : Free address body.code)
    (environment : Nat → Bool) :
    bind address body environment address = truth (body.eval (bind address body environment)) := by
  simp only [bind, Function.update_self, eval_free_update address body free]

theorem bind_idempotent (address : Nat) (body : Fragment) (free : Free address body.code)
    (environment : Nat → Bool) : bind address body (bind address body environment) = bind address body environment :=
  bind_fixes address body _ (bind_holds address body free environment)

theorem bind_update (address : Nat) (body : Fragment) (free : Free address body.code)
    (environment : Nat → Bool) (value : Bool) :
    bind address body (Function.update environment address value) = bind address body environment := by
  simp only [bind, eval_free_update address body free, Function.update_idem]

theorem rewrite_small (address offset output : Nat) (node : Node)
    (small : BooleanValues.NodeSmall node) :
    BooleanValues.NodeSmall (rewrite address offset output node) := by
  cases node <;> try (first | exact small | trivial)
  rename_i i
  by_cases same : i = address <;> simp [rewrite, same, BooleanValues.NodeSmall]

theorem substitute_small (program : Program) (address : Nat) (body : Fragment)
    (original : BooleanValues.Code program.code) (added : BooleanValues.Code body.code) :
    BooleanValues.Code (substitute program address body).code := by
  apply BooleanValues.code_append body.code _ added
  exact BooleanValues.code_map program.code original _ (rewrite_small address _ _)

def inputOf : Node → Option Nat
  | .input i => some i
  | _ => none

def inputs (code : Array Node) : List Nat := (code.toList.filterMap inputOf).dedup

theorem input_member (code : Array Node) (i : Nat) :
    i ∈ inputs code ↔ Node.input i ∈ code.toList := by
  simp only [inputs, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨node, member, found⟩
    cases node <;> simp only [inputOf, reduceCtorEq, Option.some.injEq] at found
    simpa only [found] using member
  · intro member
    exact ⟨.input i, member, rfl⟩

theorem inputs_free (code : Array Node) (address : Nat) (free : Free address code) :
    address ∉ inputs code := by
  intro member
  exact free (.input address) ((input_member code address).mp member) rfl

theorem inputs_size (code : Array Node) : (inputs code).length ≤ code.size := by
  exact (List.dedup_sublist _).length_le.trans (by simpa using List.length_filterMap_le inputOf code.toList)

theorem node_environment_congr (node : Node) (left right : Nat → Bool) (values : Array ℤ)
    (same : ∀ i, node = .input i → left i = right i) : node.run left values = node.run right values := by
  cases node <;> try rfl
  rename_i i
  simp only [Node.run, same i rfl]

theorem runCode_environment_congr (code : List Node) (left right : Nat → Bool) (values : Array ℤ)
    (same : ∀ i, Node.input i ∈ code → left i = right i) :
    runCode left values code = runCode right values code := by
  induction code generalizing values with
  | nil => rfl
  | cons node rest ih =>
      have first := node_environment_congr node left right values
        (fun i equal => same i (by simp [← equal]))
      simp only [runCode, first]
      exact ih _ (fun i member => same i (by simp [member]))

theorem eval_environment_congr (program : Program) (left right : Nat → Bool)
    (same : ∀ i ∈ inputs program.code, left i = right i) : program.eval left = program.eval right := by
  have result := runCode_environment_congr program.code.toList left right #[]
    (fun i member => same i ((input_member program.code i).mpr member))
  change run left program.code = run right program.code at result
  simp only [Program.eval, result]

def assign (indices : List Nat) (target environment : Nat → Bool) : Nat → Bool :=
  indices.foldl (fun previous i => Function.update previous i (target i)) environment

theorem assign_same (indices : List Nat) (target environment : Nat → Bool) (i : Nat)
    (already : environment i = target i) : assign indices target environment i = target i := by
  induction indices generalizing environment with
  | nil => exact already
  | cons j rest ih =>
      apply ih
      by_cases same : i = j <;> simp_all

theorem assign_member (indices : List Nat) (target environment : Nat → Bool) (i : Nat)
    (member : i ∈ indices) : assign indices target environment i = target i := by
  induction indices generalizing environment with
  | nil => simp at member
  | cons j rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact assign_same rest target _ i (Function.update_self i (target i) environment)
      · exact ih _ member

theorem anyOver_assign (indices : List Nat) (value : (Nat → Bool) → Bool)
    (target environment : Nat → Bool)
    (accepted : value (assign indices target environment) = true) :
    Affine.Boolean.anyOver indices value environment = true := by
  induction indices generalizing environment with
  | nil => exact accepted
  | cons i rest ih =>
      have chosen := ih (Function.update environment i (target i)) accepted
      cases selected : target i <;>
        simp_all [Affine.Boolean.anyOver]

theorem anyOver_witness (indices : List Nat) (value : (Nat → Bool) → Bool) (environment : Nat → Bool)
    (accepted : Affine.Boolean.anyOver indices value environment = true) :
    ∃ result : Nat → Bool, value result = true := by
  induction indices generalizing environment with
  | nil => exact ⟨environment, accepted⟩
  | cons i rest ih =>
      simp only [Affine.Boolean.anyOver, Bool.or_eq_true] at accepted
      rcases accepted with left | right
      · exact ih _ left
      · exact ih _ right

def close (program : Program) : Program := Affine.Boolean.fold (inputs program.code) program

def decideProgram (program : Program) : Bool :=
  truth (InterferenceDecision.readProgram (close program)).value

theorem decideProgram_correct (program : Program) :
    decideProgram program = true ↔ ∃ environment : Nat → Bool, truth (program.eval environment) = true := by
  simp only [decideProgram, InterferenceDecision.readProgram_value, close, Affine.Boolean.eval_fold]
  constructor
  · exact anyOver_witness _ _ _
  · rintro ⟨environment, accepted⟩
    apply anyOver_assign _ _ environment _
    rw [eval_environment_congr program (assign (inputs program.code) environment InterferenceDecision.zeroEnvironment)
      environment (assign_member (inputs program.code) environment InterferenceDecision.zeroEnvironment)]
    exact accepted

structure Instruction where
  address : Nat
  body : Fragment
  deriving Repr

def Instruction.bind (instruction : Instruction) (environment : Nat → Bool) : Nat → Bool :=
  FunctionalSubstitution.bind instruction.address instruction.body environment

def fill (instructions : List Instruction) (environment : Nat → Bool) : Nat → Bool :=
  instructions.foldr Instruction.bind environment

def execute : List Instruction → Program → Program
  | [], program => program
  | instruction :: rest, program => execute rest (substitute program instruction.address instruction.body)

theorem eval_execute (instructions : List Instruction) (program : Program) (environment : Nat → Bool) :
    (execute instructions program).eval environment = program.eval (fill instructions environment) := by
  induction instructions generalizing program with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [execute, ih, eval_substitute, fill, List.foldr_cons, Instruction.bind]

theorem fill_fixes (instructions : List Instruction) (environment : Nat → Bool)
    (fixed : ∀ instruction ∈ instructions, instruction.bind environment = environment) :
    fill instructions environment = environment := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [fill, List.foldr_cons]
      change instruction.bind (fill rest environment) = environment
      rw [ih (fun other member => fixed other (by simp [member])), fixed instruction (by simp)]

theorem execute_satisfiable (instructions : List Instruction) (program : Program)
    (entailed : ∀ environment, truth (program.eval environment) = true →
      ∀ instruction ∈ instructions, instruction.bind environment = environment) :
    (∃ environment, truth ((execute instructions program).eval environment) = true) ↔
      ∃ environment, truth (program.eval environment) = true := by
  constructor
  · rintro ⟨environment, accepted⟩
    exact ⟨fill instructions environment, (eval_execute instructions program environment) ▸ accepted⟩
  · rintro ⟨environment, accepted⟩
    refine ⟨environment, ?_⟩
    rw [eval_execute, fill_fixes instructions environment (entailed environment accepted)]
    exact accepted

theorem execute_size (instructions : List Instruction) (program : Program) :
    (execute instructions program).code.size = program.code.size + (instructions.map (·.body.code.size)).sum := by
  induction instructions generalizing program with
  | nil => simp [execute]
  | cons instruction rest ih =>
      simp only [execute, ih, substitute_size, List.map_cons, List.sum_cons]
      omega

theorem execute_small (instructions : List Instruction) (program : Program)
    (original : BooleanValues.Code program.code)
    (bodies : ∀ instruction ∈ instructions, BooleanValues.Code instruction.body.code) :
    BooleanValues.Code (execute instructions program).code := by
  induction instructions generalizing program with
  | nil => exact original
  | cons instruction rest ih =>
      exact ih _ (substitute_small program instruction.address instruction.body original (bodies instruction (by simp)))
        (fun other member => bodies other (by simp [member]))

theorem free_iff (code : Array Node) (address : Nat) : Free address code ↔ address ∉ inputs code := by
  constructor
  · exact inputs_free code address
  · intro absent node member
    cases node <;> try trivial
    rename_i i
    intro same
    exact absent ((input_member code address).mpr (same ▸ member))

def ready (used : List Nat) (instruction : Instruction) : Bool :=
  decide (instruction.address ∉ used) &&
    (instruction.address :: used).all (fun i => decide (i ∉ inputs instruction.body.code))

theorem ready_sound (used : List Nat) (instruction : Instruction) (accepted : ready used instruction = true) :
    instruction.address ∉ used ∧ Free instruction.address instruction.body.code ∧
      ∀ i ∈ used, Free i instruction.body.code := by
  simp only [ready, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at accepted
  refine ⟨accepted.1, (free_iff _ _).mpr (accepted.2 _ (by simp)), ?_⟩
  exact fun i member => (free_iff _ _).mpr (accepted.2 i (by simp [member]))

/-- The original generated bodies remain shared; accepting a body never reintroduces a removed input. -/
def select (used : List Nat) : List Instruction → List Instruction
  | [] => []
  | instruction :: rest =>
      if ready used instruction then instruction :: select (instruction.address :: used) rest else select used rest

theorem select_sublist (used : List Nat) (instructions : List Instruction) :
    (select used instructions).Sublist instructions := by
  induction instructions generalizing used with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [select]
      split
      · exact (ih _).cons_cons _
      · exact (ih _).cons _

theorem select_old (used : List Nat) (instructions : List Instruction) (instruction : Instruction)
    (member : instruction ∈ select used instructions) (i : Nat) (old : i ∈ used) :
    i ≠ instruction.address ∧ Free i instruction.body.code := by
  induction instructions generalizing used with
  | nil => simp [select] at member
  | cons first rest ih =>
      simp only [select] at member
      split at member
      · rename_i admitted
        rcases List.mem_cons.mp member with equal | member
        · subst instruction
          have valid := ready_sound used first admitted
          exact ⟨fun same => valid.1 (same ▸ old), valid.2.2 i old⟩
        · exact ih _ member (by simp [old])
      · exact ih _ member old

def Triangular (instructions : List Instruction) : Prop :=
  (∀ instruction ∈ instructions, Free instruction.address instruction.body.code) ∧
    instructions.Pairwise (fun left right => left.address ≠ right.address ∧ Free left.address right.body.code)

theorem select_triangular (used : List Nat) (instructions : List Instruction) : Triangular (select used instructions) := by
  induction instructions generalizing used with
  | nil => simp [select, Triangular]
  | cons instruction rest ih =>
      rw [select]
      split
      · rename_i admitted
        have tail := ih (instruction.address :: used)
        refine ⟨?_, List.pairwise_cons.mpr ⟨?_, tail.2⟩⟩
        · intro other member
          rcases List.mem_cons.mp member with equal | member
          · subst other
            exact (ready_sound used instruction admitted).2.1
          · exact tail.1 other member
        · intro other member
          exact select_old _ rest other member instruction.address (by simp)
      · exact ih used

theorem execute_free (instructions : List Instruction) (program : Program) (address : Nat)
    (original : Free address program.code)
    (bodies : ∀ instruction ∈ instructions, Free address instruction.body.code) :
    Free address (execute instructions program).code := by
  induction instructions generalizing program with
  | nil => exact original
  | cons instruction rest ih =>
      exact ih _ (substitute_free program instruction.address address instruction.body original (bodies instruction (by simp)))
        (fun other member => bodies other (by simp [member]))

theorem execute_selected_free (instructions : List Instruction) (triangular : Triangular instructions)
    (program : Program) (instruction : Instruction) (member : instruction ∈ instructions) :
    Free instruction.address (execute instructions program).code := by
  induction instructions generalizing program with
  | nil => simp at member
  | cons first rest ih =>
      have tail : Triangular rest := ⟨fun other hit => triangular.1 other (by simp [hit]),
        (List.pairwise_cons.mp triangular.2).2⟩
      rcases List.mem_cons.mp member with equal | member
      · subst instruction
        exact execute_free rest _ first.address
          (substitute_free_self program first.address first.body (triangular.1 first (by simp)))
          (fun other hit => ((List.pairwise_cons.mp triangular.2).1 other hit).2)
      · exact ih tail _ member

def prepare (instructions : List Instruction) (program : Program) : Program := execute (select [] instructions) program

theorem prepare_eliminates (instructions : List Instruction) (program : Program) (instruction : Instruction)
    (member : instruction ∈ select [] instructions) : instruction.address ∉ inputs (prepare instructions program).code :=
  inputs_free _ instruction.address (execute_selected_free _ (select_triangular [] instructions) program instruction member)

theorem prepare_size (instructions : List Instruction) (program : Program) :
    (prepare instructions program).code.size ≤ program.code.size + (instructions.map (·.body.code.size)).sum := by
  rw [prepare, execute_size]
  have bound := ((select_sublist [] instructions).map (fun instruction => instruction.body.code.size)).sum_le_sum
    (fun _ _ => Nat.zero_le _)
  exact Nat.add_le_add_left bound _

theorem prepare_correct (instructions : List Instruction) (program : Program)
    (entailed : ∀ environment, truth (program.eval environment) = true →
      ∀ instruction ∈ instructions, instruction.bind environment = environment) :
    decideProgram (prepare instructions program) = true ↔
      ∃ environment, truth (program.eval environment) = true := by
  rw [decideProgram_correct]
  apply execute_satisfiable
  intro environment accepted instruction member
  exact entailed environment accepted instruction ((select_sublist [] instructions).subset member)

end SaturationMonoid.ComplexityProjection.SATSource.FunctionalSubstitution
