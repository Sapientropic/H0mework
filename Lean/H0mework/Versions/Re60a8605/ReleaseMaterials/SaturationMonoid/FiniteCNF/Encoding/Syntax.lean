import H0mework.Computation.SelfReduction.P687

/-!
One fixed prefix format for every finite CNF. Naturals use a true-run ending
in false; a list uses false for nil and true before each encoded entry.
A literal contains its unary address followed by its polarity bit. The
header's variable bound is therefore paid for in the actual input length.
Sparse binary-address CNF needs dense renumbering before conversion to this
format; no binary-header size claim is made here.

List readers use input-length fuel; the unary reader consumes input
structurally. This supplies input semantics and an actual total Boolean
program, without a TM2 polynomial-cost claim.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Encoding

abbrev Input := (n : Nat) × CNFFormula n

def writeNat : Nat → List Bool
  | 0 => [false]
  | n + 1 => true :: writeNat n

def readNat : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, tail) ← readNat rest
      some (n + 1, tail)

theorem readNat_writeNat (n : Nat) (tail : List Bool) :
    readNat (writeNat n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [writeNat, readNat, ih]

theorem writeNat_length (n : Nat) : (writeNat n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [writeNat, ih]

theorem readNat_length (bits : List Bool) (n : Nat) (tail : List Bool)
    (h : readNat bits = some (n, tail)) : n + 1 + tail.length = bits.length := by
  induction bits generalizing n with
  | nil => simp [readNat] at h
  | cons bit rest ih =>
      cases bit with
      | false =>
          simp only [readNat, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp [Nat.add_comm]
      | true =>
          cases hr : readNat rest with
          | none => simp [readNat, hr] at h
          | some value =>
              rcases value with ⟨k, suffix⟩
              simp [readNat, hr] at h
              rcases h with ⟨rfl, rfl⟩
              have size := ih k hr
              simp only [List.length_cons]
              omega

def writeList {α : Type} (write : α → List Bool) : List α → List Bool
  | [] => [false]
  | a :: rest => true :: (write a ++ writeList write rest)

def readList {α : Type} (read : List Bool → Option (α × List Bool)) :
    Nat → List Bool → Option (List α × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: rest => do
      let (a, next) ← read rest
      let (values, tail) ← readList read fuel next
      some (a :: values, tail)

theorem writeList_length_ge {α : Type} (write : α → List Bool) (values : List α) :
    values.length + 1 ≤ (writeList write values).length := by
  induction values with
  | nil => rfl
  | cons a rest ih => simp only [writeList, List.length_cons, List.length_append] at *; omega

theorem readList_writeList {α : Type} (write : α → List Bool)
    (read : List Bool → Option (α × List Bool))
    (roundtrip : ∀ a tail, read (write a ++ tail) = some (a, tail))
    (values : List α) (fuel : Nat) (tail : List Bool)
    (enough : values.length + 1 ≤ fuel) :
    readList read fuel (writeList write values ++ tail) = some (values, tail) := by
  induction values generalizing fuel with
  | nil =>
      cases fuel with
      | zero => simp at enough
      | succ fuel => rfl
  | cons a rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have budget : rest.length + 1 ≤ fuel := by simpa using enough
          simp [writeList, readList, List.append_assoc, roundtrip, ih fuel budget]

def writeLiteral {n : Nat} (lit : CNFLiteral n) : List Bool :=
  writeNat lit.var.val ++ [lit.positive]

def readLiteral (n : Nat) (bits : List Bool) : Option (CNFLiteral n × List Bool) := do
  let (index, rest) ← readNat bits
  match rest with
  | [] => none
  | bit :: tail =>
      if bound : index < n then some (⟨⟨index, bound⟩, bit⟩, tail) else none

theorem readLiteral_writeLiteral {n : Nat} (lit : CNFLiteral n) (tail : List Bool) :
    readLiteral n (writeLiteral lit ++ tail) = some (lit, tail) := by
  cases lit with
  | mk var positive =>
      cases var with
      | mk index bound => simp [writeLiteral, readLiteral, List.append_assoc, readNat_writeNat, bound]

def writeClause {n : Nat} (clause : CNFClause n) : List Bool :=
  writeList writeLiteral clause

def readClause (n : Nat) (bits : List Bool) : Option (CNFClause n × List Bool) :=
  readList (readLiteral n) bits.length bits

theorem readClause_writeClause {n : Nat} (clause : CNFClause n) (tail : List Bool) :
    readClause n (writeClause clause ++ tail) = some (clause, tail) := by
  apply readList_writeList writeLiteral (readLiteral n) readLiteral_writeLiteral
  have budget := writeList_length_ge writeLiteral clause
  simp only [writeClause, List.length_append]
  omega

theorem writeClause_length {n : Nat} (clause : CNFClause n) :
    (writeClause clause).length = 1 + (clause.map fun lit => lit.var.val + 3).sum := by
  induction clause with
  | nil => rfl
  | cons lit rest ih =>
      change (true :: (writeLiteral lit ++ writeClause rest)).length = _
      simp only [List.length_cons, List.length_append, writeLiteral, writeNat_length,
        List.length_nil, List.map_cons, List.sum_cons, ih]
      omega

def writeFormula {n : Nat} (formula : CNFFormula n) : List Bool :=
  writeList writeClause formula

def readFormula (n : Nat) (bits : List Bool) : Option (CNFFormula n × List Bool) :=
  readList (readClause n) bits.length bits

theorem readFormula_writeFormula {n : Nat} (formula : CNFFormula n) (tail : List Bool) :
    readFormula n (writeFormula formula ++ tail) = some (formula, tail) := by
  apply readList_writeList writeClause (readClause n) readClause_writeClause
  have budget := writeList_length_ge writeClause formula
  simp only [writeFormula, List.length_append]
  omega

theorem writeFormula_length {n : Nat} (formula : CNFFormula n) :
    (writeFormula formula).length =
      1 + (formula.map fun clause => 2 + (clause.map fun lit => lit.var.val + 3).sum).sum := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      change (true :: (writeClause clause ++ writeFormula rest)).length = _
      simp only [List.length_cons, List.length_append, writeClause_length,
        List.map_cons, List.sum_cons, ih]
      omega

def encode (input : Input) : List Bool :=
  writeNat input.1 ++ writeFormula input.2

def parse (bits : List Bool) : Option Input := do
  let (n, rest) ← readNat bits
  let (formula, tail) ← readFormula n rest
  if tail = [] then some ⟨n, formula⟩ else none

theorem parse_encode (input : Input) : parse (encode input) = some input := by
  cases input with
  | mk n formula =>
      have readback := readFormula_writeFormula formula []
      simp only [List.append_nil] at readback
      simp [encode, parse, readNat_writeNat, readback]

theorem encode_length (input : Input) :
    (encode input).length = input.1 + 2 +
      (input.2.map fun clause => 2 + (clause.map fun lit => lit.var.val + 3).sum).sum := by
  simp only [encode, List.length_append, writeNat_length, writeFormula_length]
  omega

theorem parse_variableBound_lt (bits : List Bool) (input : Input)
    (parsed : parse bits = some input) : input.1 < bits.length := by
  cases hn : readNat bits with
  | none => simp [parse, hn] at parsed
  | some header =>
      rcases header with ⟨n, rest⟩
      cases hf : readFormula n rest with
      | none => simp [parse, hn, hf] at parsed
      | some body =>
          rcases body with ⟨formula, tail⟩
          by_cases ht : tail = []
          · simp [parse, hn, hf, ht] at parsed
            subst input
            have size := readNat_length bits n rest hn
            simp only
            omega
          · simp [parse, hn, hf, ht] at parsed

private theorem literal_word_sum_le {n : Nat} (clause : CNFClause n) :
    (clause.map fun lit => lit.var.val + 3).sum ≤ (n + 2) * clause.length := by
  induction clause with
  | nil => simp
  | cons lit clause ih =>
      have bound := lit.var.isLt
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add,
        Nat.mul_one]
      omega

theorem encode_formula_length_le {n : Nat} (formula : CNFFormula n) :
    (encode ⟨n, formula⟩).length ≤
      n + 2 + 2 * formula.length + (n + 2) * formula.flatten.length := by
  rw [encode_length]
  have weight :
      (formula.map fun clause => 2 + (clause.map fun lit => lit.var.val + 3).sum).sum ≤
        2 * formula.length + (n + 2) * formula.flatten.length := by
    induction formula with
    | nil => simp
    | cons clause formula ih =>
        have bounded := literal_word_sum_le clause
        simp only [List.map_cons, List.sum_cons, List.length_cons, List.flatten_cons,
          List.length_append, Nat.mul_add, Nat.mul_one]
        omega
  simp only
  omega

theorem readNat_prefix (bits : List Bool) (n : Nat) (tail : List Bool)
    (parsed : readNat bits = some (n, tail)) : bits = writeNat n ++ tail := by
  induction bits generalizing n with
  | nil => simp [readNat] at parsed
  | cons bit bits ih =>
      cases bit with
      | false =>
          simp only [readNat, Option.some.injEq, Prod.mk.injEq] at parsed
          rcases parsed with ⟨rfl, rfl⟩
          rfl
      | true =>
          cases next : readNat bits with
          | none => simp [readNat, next] at parsed
          | some value =>
              obtain ⟨k, rest⟩ := value
              simp [readNat, next] at parsed
              rcases parsed with ⟨rfl, rfl⟩
              simpa [writeNat] using congrArg (List.cons true) (ih k next)

theorem readList_prefix {α : Type} (write : α → List Bool)
    (read : List Bool → Option (α × List Bool))
    (source : ∀ bits value tail, read bits = some (value, tail) → bits = write value ++ tail)
    (fuel : Nat) (bits : List Bool) (values : List α) (tail : List Bool)
    (parsed : readList read fuel bits = some (values, tail)) :
    bits = writeList write values ++ tail := by
  induction fuel generalizing bits values with
  | zero => simp [readList] at parsed
  | succ fuel ih =>
      cases bits with
      | nil => simp [readList] at parsed
      | cons bit bits =>
          cases bit with
          | false =>
              simp only [readList, Option.some.injEq, Prod.mk.injEq] at parsed
              rcases parsed with ⟨rfl, rfl⟩
              rfl
          | true =>
              cases first : read bits with
              | none => simp [readList, first] at parsed
              | some firstValue =>
                  obtain ⟨value, next⟩ := firstValue
                  cases rest : readList read fuel next with
                  | none => simp [readList, first, rest] at parsed
                  | some remaining =>
                      obtain ⟨suffix, after⟩ := remaining
                      simp [readList, first, rest] at parsed
                      rcases parsed with ⟨rfl, rfl⟩
                      rw [source bits value next first, ih next suffix rest]
                      simp [writeList, List.append_assoc]

theorem readLiteral_prefix (n : Nat) (bits : List Bool) (lit : CNFLiteral n)
    (tail : List Bool) (parsed : readLiteral n bits = some (lit, tail)) :
    bits = writeLiteral lit ++ tail := by
  cases header : readNat bits with
  | none => simp [readLiteral, header] at parsed
  | some value =>
      obtain ⟨index, rest⟩ := value
      cases rest with
      | nil => simp [readLiteral, header] at parsed
      | cons bit rest =>
          by_cases bound : index < n
          · simp [readLiteral, header, bound] at parsed
            rcases parsed with ⟨rfl, rfl⟩
            simpa [writeLiteral, List.append_assoc] using readNat_prefix bits index (bit :: rest) header
          · simp [readLiteral, header, bound] at parsed

theorem readClause_prefix (n : Nat) (bits : List Bool) (clause : CNFClause n)
    (tail : List Bool) (parsed : readClause n bits = some (clause, tail)) :
    bits = writeClause clause ++ tail :=
  readList_prefix writeLiteral (readLiteral n) (readLiteral_prefix n) bits.length bits clause tail parsed

theorem readFormula_prefix (n : Nat) (bits : List Bool) (formula : CNFFormula n)
    (tail : List Bool) (parsed : readFormula n bits = some (formula, tail)) :
    bits = writeFormula formula ++ tail :=
  readList_prefix writeClause (readClause n) (readClause_prefix n) bits.length bits formula tail parsed

theorem encode_of_parse (bits : List Bool) (input : Input)
    (parsed : parse bits = some input) : encode input = bits := by
  cases header : readNat bits with
  | none => simp [parse, header] at parsed
  | some value =>
      obtain ⟨n, rest⟩ := value
      cases body : readFormula n rest with
      | none => simp [parse, header, body] at parsed
      | some value =>
          obtain ⟨formula, tail⟩ := value
          by_cases empty : tail = []
          · simp [parse, header, body, empty] at parsed
            subst input
            have sourcePrefix := readFormula_prefix n rest formula tail body
            rw [empty, List.append_nil] at sourcePrefix
            rw [readNat_prefix bits n rest header, sourcePrefix]
            rfl
          · simp [parse, header, body, empty] at parsed

theorem encode_source_size (input : Input) :
    input.1 + 2 + 2 * input.2.length + 3 * input.2.flatten.length ≤ (encode input).length := by
  have clauseBound {n : Nat} (clause : CNFClause n) :
      3 * clause.length ≤ (clause.map fun lit => lit.var.val + 3).sum := by
    induction clause with
    | nil => simp
    | cons lit rest ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.mul_add, Nat.mul_one]
        omega
  have formulaBound {n : Nat} (formula : CNFFormula n) :
      2 * formula.length + 3 * formula.flatten.length ≤
        (formula.map fun clause => 2 + (clause.map fun lit => lit.var.val + 3).sum).sum := by
    induction formula with
    | nil => simp
    | cons clause rest ih =>
        have bounded := clauseBound clause
        simp only [List.length_cons, List.flatten_cons, List.length_append,
          List.map_cons, List.sum_cons, Nat.mul_add, Nat.mul_one]
        omega
  rw [encode_length]
  have bounded := formulaBound input.2
  omega

theorem parse_source_size (bits : List Bool) (input : Input)
    (parsed : parse bits = some input) :
    input.1 + 2 + 2 * input.2.length + 3 * input.2.flatten.length ≤ bits.length := by
  rw [← encode_of_parse bits input parsed]
  exact encode_source_size input

end SaturationMonoid.ComplexityProjection.SATSource.Encoding
