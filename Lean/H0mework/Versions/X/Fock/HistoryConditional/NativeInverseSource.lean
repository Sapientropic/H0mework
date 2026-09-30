import H0mework.Fock.HistoryConditional.NativeInverseNative
import H0mework.Versions.X.Fock.HistoryConditional.GWordProgramSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeProgramInverse

theorem decode_execute (program : Nat × Nat) (positive : 0 < program.1) (state : Nat) :
    decode program (SourceCopyWordAffine.execute program state) = some state := by
  rw [decode, SourceGWordProgram.index_exact program positive, Nat.add_sub_cancel]
  have product : 0 < program.1 * (state + 1) := Nat.mul_pos positive (Nat.succ_pos state)
  rw [if_pos ⟨positive, by omega, dvd_mul_right _ _⟩]
  simp [positive]

theorem decode_some_iff (program : Nat × Nat) (positive : 0 < program.1) (target state : Nat) :
    decode program target = some state ↔ SourceCopyWordAffine.execute program state = target := by
  constructor
  · intro result
    unfold decode at result
    split at result
    next present =>
      have recovered := Option.some.inj result
      have divided := Nat.div_mul_cancel present.2.2
      have quotientPositive : 0 < (target + 1 - program.2) / program.1 := by
        by_contra notPositive
        have zero : (target + 1 - program.2) / program.1 = 0 := Nat.eq_zero_of_not_pos notPositive
        rw [zero, Nat.zero_mul] at divided
        omega
      have stateSucc : state + 1 = (target + 1 - program.2) / program.1 := by
        rw [← recovered]
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt quotientPositive)
      apply Nat.add_right_cancel (m := 1)
      rw [SourceGWordProgram.index_exact program positive, stateSucc, Nat.mul_div_cancel' present.2.2]
      exact Nat.sub_add_cancel (Nat.le_of_lt present.2.1)
    next absent => cases result
  · intro same
    rw [← same]
    exact decode_execute program positive state

theorem decode_none_iff (program : Nat × Nat) (positive : 0 < program.1) (target : Nat) :
    decode program target = none ↔ target ∉ Set.range (SourceCopyWordAffine.execute program) := by
  constructor
  · rintro none ⟨state, generated⟩
    have restored := (decode_some_iff program positive target state).mpr generated
    rw [none] at restored
    cases restored
  · intro outside
    cases result : decode program target with
    | none => rfl
    | some state => exact (outside ⟨state, (decode_some_iff program positive target state).mp result⟩).elim

theorem compiled_none (word : List (Option Nat)) (target : Nat) :
    decode (SourceCopyWordAffine.compile word) target = none ↔
      ¬ ((SourceCopyWordAffine.compile word).2 < target + 1 ∧
        (SourceCopyWordAffine.compile word).1 ∣ target + 1 - (SourceCopyWordAffine.compile word).2) := by
  rw [decode_none_iff _ (SourceCompiledWordOperator.slope_positive word), SourceCompiledWordOperator.index_range]

end SourceNativeProgramInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
