import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Joint
import Mathlib.Data.List.OfFn

/-! A fixed Boolean word representation of the actual source cylinders.
Source joins and clause masks have explicit word constructors. -/

namespace SaturationMonoid.ComplexityProjection.SATJoint.CubeWords

def pack : List (Bool × Bool) → List Bool
  | [] => []
  | (a, b) :: rest => a :: b :: pack rest

theorem pack_length (pairs : List (Bool × Bool)) :
    (pack pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih => simp [pack, ih]; omega

theorem pack_injective : Function.Injective pack := by
  intro left
  induction left with
  | nil =>
      intro right h
      cases right with
      | nil => rfl
      | cons p right => simp [pack] at h
  | cons p left ih =>
      intro right h
      cases right with
      | nil => simp [pack] at h
      | cons q right =>
          obtain ⟨hp, hq, hr⟩ := by simpa [pack] using h
          have he : p = q := Prod.ext hp hq
          simp [he, ih hr]

def code {n : Nat} (cube : Cube n) : List Bool :=
  pack (List.ofFn fun i => (decide (false ∈ cube i), decide (true ∈ cube i)))

theorem code_length {n : Nat} (cube : Cube n) : (code cube).length = 2 * n := by
  simp [code, pack_length]

theorem code_injective {n : Nat} : Function.Injective (@code n) := by
  intro left right same
  have hp := List.ofFn_injective (pack_injective same)
  funext i
  apply Finset.ext
  intro b
  have hi := congrFun hp i
  cases b with
  | false =>
      simpa only [decide_eq_true_eq] using Bool.eq_iff_iff.mp (congrArg Prod.fst hi)
  | true =>
      simpa only [decide_eq_true_eq] using Bool.eq_iff_iff.mp (congrArg Prod.snd hi)

def joinCode (left right : List Bool) : List Bool :=
  List.zipWith Bool.and left right

theorem pack_zip (left right : List (Bool × Bool)) :
    pack (List.zipWith (fun a b => (a.1 && b.1, a.2 && b.2)) left right) =
      joinCode (pack left) (pack right) := by
  induction left generalizing right with
  | nil => rfl
  | cons a left ih =>
      cases right with
      | nil => rfl
      | cons b right => simp [pack, joinCode, ih]

theorem zip_ofFn {α β γ : Type} {n : Nat} (f : Fin n → α) (g : Fin n → β)
    (op : α → β → γ) :
    List.zipWith op (List.ofFn f) (List.ofFn g) = List.ofFn (fun i => op (f i) (g i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem joinCode_correct {n : Nat} (left right : Cube n) :
    joinCode (code left) (code right) = code (joinCube left right) := by
  rw [code, code, ← pack_zip, zip_ofFn]
  simp [code, joinCube, Finset.mem_inter]

def topCode (n : Nat) : List Bool := pack (List.replicate n (true, true))

theorem topCode_correct (n : Nat) : topCode n = code (topCube n) := by
  simp [topCode, code, topCube, List.ofFn_const]

def literalCode {n : Nat} (lit : CNFLiteral n) : List Bool :=
  pack (List.ofFn fun i =>
    if i = lit.var then (lit.positive, !lit.positive) else (true, true))

theorem literalCode_correct {n : Nat} (lit : CNFLiteral n) :
    literalCode lit = code (clauseCube [lit]) := by
  apply congrArg pack
  apply congrArg List.ofFn
  funext i
  by_cases hi : i = lit.var
  · subst i
    cases hp : lit.positive <;> simp [clauseCube, hp]
  · have hn : lit.var ≠ i := Ne.symm hi
    simp [clauseCube, hi, hn]

theorem clauseCube_cons {n : Nat} (lit : CNFLiteral n) (rest : CNFClause n) :
    clauseCube (lit :: rest) = joinCube (clauseCube [lit]) (clauseCube rest) := by
  funext i
  apply Finset.ext
  intro b
  simp [clauseCube, joinCube]

def clauseCode {n : Nat} : CNFClause n → List Bool
  | [] => topCode n
  | lit :: rest => joinCode (literalCode lit) (clauseCode rest)

theorem clauseCode_correct {n : Nat} (clause : CNFClause n) :
    clauseCode clause = code (clauseCube clause) := by
  induction clause with
  | nil =>
      rw [clauseCode, topCode_correct]
      apply congrArg code
      funext i
      simp [clauseCube, topCube]
  | cons lit rest ih =>
      rw [clauseCode, literalCode_correct, ih, joinCode_correct,
        clauseCube_cons lit rest]

/-- This is the number of actual pairwise Boolean operations in `joinCode`. -/
def joinCells : List Bool → List Bool → Nat
  | _ :: left, _ :: right => 1 + joinCells left right
  | _, _ => 0

theorem joinCells_length (left right : List Bool) :
    joinCells left right = min left.length right.length := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a left ih =>
      cases right with
      | nil => rfl
      | cons b right => simp [joinCells, ih, Nat.add_comm]

theorem joinCells_source {n : Nat} (left right : Cube n) :
    joinCells (code left) (code right) = 2 * n := by
  rw [joinCells_length, code_length, code_length, min_self]

end SaturationMonoid.ComplexityProjection.SATJoint.CubeWords
