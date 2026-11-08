import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.List.Nodup

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening

structure Address (Instrument Party : Type) where
  instrument : Instrument
  debtor : Party
  holder : Party
  deriving DecidableEq

variable {Instrument Party : Type}

abbrev Matrix (Instrument Party : Type) := Address Instrument Party → ℚ

/-- The finite carrier covers both original readings, including every
nonzero coordinate. Its enumeration cannot add a financial event. -/
structure Support (raw carried : Matrix Instrument Party) where
  keys : List (Address Instrument Party)
  distinct : keys.Nodup
  outside : ∀ key, key ∉ keys → raw key = 0 ∧ carried key = 0

def Support.ofAll (raw carried : Matrix Instrument Party)
    (keys : List (Address Instrument Party)) (distinct : keys.Nodup)
    (complete : ∀ key, key ∈ keys) : Support raw carried :=
  ⟨keys, distinct, fun key absent => (absent (complete key)).elim⟩

variable {raw carried : Matrix Instrument Party} (support : Support raw carried)

def discrepancies : List (Address Instrument Party) :=
  support.keys.filter fun key => decide (raw key ≠ carried key)

theorem discrepancies_exact (key : Address Instrument Party) :
    key ∈ discrepancies support ↔ raw key ≠ carried key := by
  change key ∈ support.keys.filter (fun key => decide (raw key ≠ carried key)) ↔ _
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro different
    refine ⟨?_, different⟩
    by_contra absent
    obtain ⟨rawZero, carriedZero⟩ := support.outside key absent
    exact different (rawZero.trans carriedZero.symm)

theorem discrepancies_distinct : (discrepancies support).Nodup :=
  support.distinct.filter _

theorem discrepancies_empty_iff : discrepancies support = [] ↔ raw = carried := by
  constructor
  · intro empty
    funext key
    by_contra different
    have member := (discrepancies_exact support key).2 different
    rw [empty] at member
    exact List.not_mem_nil member
  · intro equal
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro key member
    exact (discrepancies_exact support key).1 member (congrFun equal key)

/-- A refusal reports all differing original coordinates, with the two
amounts available at each original debtor and holder. -/
inductive Decision
  | accepted (equal : raw = carried)
  | refused (first : Address Instrument Party) (rest : List (Address Instrument Party))
      (exactReport : discrepancies support = first :: rest)

def inspect : Decision support :=
  match report : discrepancies support with
  | [] => .accepted ((discrepancies_empty_iff support).1 report)
  | first :: rest => .refused first rest report

theorem accepted_iff : (∃ equal, inspect support = .accepted equal) ↔ raw = carried := by
  constructor
  · rintro ⟨equal, _⟩
    exact equal
  · intro equal
    refine ⟨equal, ?_⟩
    unfold inspect
    split
    · rfl
    · rename_i first rest nonempty
      rw [(discrepancies_empty_iff support).2 equal] at nonempty
      cases nonempty

theorem refused_exact {first : Address Instrument Party} {rest : List (Address Instrument Party)}
    (report : discrepancies support = first :: rest) (key : Address Instrument Party) :
    key ∈ first :: rest ↔ raw key - carried key ≠ 0 := by
  rw [← report, discrepancies_exact, sub_ne_zero]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening
