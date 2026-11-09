import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Trace

universe u v
variable {Current : Type u} {Write : Type v} (trace : Trace Current Write)

def Progress : Prop := ∀ cut, ∃ visit, cut ≤ trace.ordinal visit

def FirstAt (cut visit : Nat) : Prop :=
  trace.ordinal visit = cut ∧ ∀ earlier < visit, trace.ordinal earlier < cut

theorem earliest_cut_of_reached {cut : Nat} (reached : ∃ visit, cut ≤ trace.ordinal visit) :
    ∃! visit, trace.FirstAt cut visit := by
  let first := Nat.find reached
  have large : cut ≤ trace.ordinal first := Nat.find_spec reached
  have before (earlier : Nat) (early : earlier < first) : trace.ordinal earlier < cut :=
    Nat.lt_of_not_ge (Nat.find_min reached early)
  have exactCut : trace.ordinal first = cut := by
    cases named : first with
    | zero =>
      rw [named] at large
      exact Nat.le_antisymm (Nat.zero_le _) large
    | succ earlier =>
      have small := before earlier (by rw [named]; omega)
      rw [named] at large
      have next := trace.ordinal_succ_le earlier
      omega
  refine ⟨first, ⟨exactCut, before⟩, fun other exactOther => ?_⟩
  rcases Nat.lt_trichotomy other first with early | same | late
  · exact (Nat.ne_of_lt (before other early) exactOther.1).elim
  · exact same
  · exact (Nat.ne_of_lt (exactOther.2 first late) exactCut).elim

theorem progress_iff_every_original_cut_has_unique_first_visit :
    trace.Progress ↔ ∀ cut, ∃! visit, trace.FirstAt cut visit := by
  constructor
  · exact fun progress cut => earliest_cut_of_reached trace (progress cut)
  · intro crossings cut
    obtain ⟨visit, first, _⟩ := crossings cut
    exact ⟨visit, first.1.ge⟩

structure Stall where
  last : Nat
  first : Nat
  reaches : trace.FirstAt last first
  frozen : ∀ visit ≥ first, trace.ordinal visit = last
  silent : ∀ visit ≥ first, trace.effect visit = none

theorem Stall.noProgress (stall : trace.Stall) : ¬ trace.Progress := by
  intro progress
  obtain ⟨visit, late⟩ := progress (stall.last + 1)
  have enough := late.trans (trace.ordinal_mono (Nat.le_max_left visit stall.first))
  rw [stall.frozen _ (Nat.le_max_right _ _)] at enough
  omega

noncomputable def last_before_stall (stops : ¬ trace.Progress) : trace.Stall := by
  classical
  have missing : ∃ cut, ¬ ∃ visit, cut ≤ trace.ordinal visit := by
    by_contra noneMissing
    apply stops
    intro cut
    by_contra missingCut
    exact noneMissing ⟨cut, missingCut⟩
  let cut := Nat.find missing
  have missingCut : ¬ ∃ visit, cut ≤ trace.ordinal visit := Nat.find_spec missing
  have nonzero : cut ≠ 0 := by
    intro zero
    exact missingCut ⟨0, zero.symm ▸ Nat.zero_le _⟩
  let last := cut - 1
  have adjacent : cut = last + 1 := by omega
  have prior : ∃ visit, last ≤ trace.ordinal visit := by
    by_contra noPrior
    exact Nat.find_min missing (by omega : last < cut) noPrior
  let first := Nat.find prior
  have reachFirst : trace.ordinal first = last := by
    have reached : last ≤ trace.ordinal first := Nat.find_spec prior
    have notAbove : ¬ cut ≤ trace.ordinal first := fun large => missingCut ⟨first, large⟩
    omega
  have freeze (visit : Nat) (after : first ≤ visit) : trace.ordinal visit = last := by
    have enough := trace.ordinal_mono after
    rw [reachFirst] at enough
    have notAbove : ¬ cut ≤ trace.ordinal visit := fun large => missingCut ⟨visit, large⟩
    omega
  refine ⟨last, first, ⟨reachFirst, fun earlier before =>
    Nat.lt_of_not_ge (Nat.find_min prior before)⟩, freeze, ?_⟩
  intro visit after
  cases effect : trace.effect visit with
  | none => rfl
  | some written =>
    have next := freeze (visit + 1) (by omega)
    rw [show trace.ordinal (visit + 1) = trace.ordinal visit + 1 by simp [ordinal, width, effect],
      freeze visit after] at next
    omega

section
variable {Clock : Type} [Preorder Clock] (clock : Current → Clock) {currentAt : Nat → Current} {writeAt : Nat → Write}

theorem clock_cofinal_after_each_visit_of_progress
    (factor : trace.Factors currentAt writeAt trace.ordinal)
    (mono : Monotone (clock ∘ currentAt))
    (nativeCofinal : ∀ bound, ∃ cut, bound < clock (currentAt cut))
    (progress : trace.Progress) :
    ∀ start bound, ∃ visit ≥ start, bound < clock (trace.current visit) := by
  intro start bound
  obtain ⟨cut, elapsed⟩ := nativeCofinal bound
  obtain ⟨visit, reached⟩ := progress cut
  refine ⟨max start visit, Nat.le_max_left _ _, ?_⟩
  rw [factor.reads]
  exact elapsed.trans_le (mono (reached.trans (trace.ordinal_mono (Nat.le_max_right _ _))))

theorem progress_of_clock_cofinal (factor : trace.Factors currentAt writeAt trace.ordinal)
    (mono : Monotone (clock ∘ currentAt))
    (cofinal : ∀ bound, ∃ visit, bound < clock (trace.current visit)) :
    trace.Progress := by
  intro cut
  obtain ⟨visit, elapsed⟩ := cofinal (clock (currentAt cut))
  refine ⟨visit, Nat.le_of_not_gt fun before => ?_⟩
  rw [factor.reads] at elapsed
  exact (not_lt_of_ge (mono before.le)) elapsed

end

variable (currentAt : Nat → Current) (writeAt : Nat → Write)

inductive Disposition where
  | foreignOrigin (wrong : trace.current 0 ≠ currentAt 0)
  | foreignWrite (first : Nat) (failure : ¬ trace.Check currentAt writeAt first)
      (earlier : ∀ n < first, trace.Check currentAt writeAt n)
      (retained : ∀ n ≤ first, trace.current n = currentAt (trace.ordinal n))
  | stalled (factor : trace.Factors currentAt writeAt trace.ordinal) (cut : trace.Stall)
  | cofinal (factor : trace.Factors currentAt writeAt trace.ordinal) (progress : trace.Progress)

noncomputable def audit : trace.Disposition currentAt writeAt := by
  classical
  by_cases starts : trace.current 0 = currentAt 0
  · by_cases fails : ∃ n, ¬ trace.Check currentAt writeAt n
    · have earlier (n : Nat) (before : n < Nat.find fails) : trace.Check currentAt writeAt n :=
        Classical.not_not.mp (Nat.find_min fails before)
      exact .foreignWrite (Nat.find fails) (Nat.find_spec fails) earlier
        (fun n within => trace.read_at_checked_prefix currentAt writeAt starts n
          (fun j strict => earlier j (strict.trans_le within)))
    · have checks : ∀ n, trace.Check currentAt writeAt n :=
        fun n => Classical.not_not.mp fun failure => fails ⟨n, failure⟩
      let factor := trace.factor_of_checks currentAt writeAt starts checks
      by_cases progress : trace.Progress
      · exact .cofinal factor progress
      · exact .stalled factor (trace.last_before_stall progress)
  · exact .foreignOrigin starts

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Trace
