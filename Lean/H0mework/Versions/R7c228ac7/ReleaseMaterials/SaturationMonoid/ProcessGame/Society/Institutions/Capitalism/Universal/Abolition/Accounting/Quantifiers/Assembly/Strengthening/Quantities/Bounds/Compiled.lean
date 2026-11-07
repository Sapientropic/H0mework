import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Scalar

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Compiled

open Abolition.Root Abolition.Root.Registered

noncomputable section

universe u v w

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

variable {Candidate : Type u} {Issue : Candidate → Type v} {Value : Type w}

/-- A typed proposal can compile to raw requests using intermediate original
currents. The only settlement relation is still the original script fold. -/
def values (source : C) (compile : Candidate → Script)
    (inspect : (candidate : Candidate) → Option (Issue candidate)) (read : Candidate → Value) : Set Value :=
  fun value => ∃ candidate, Settled source (compile candidate) ∧ inspect candidate = none ∧ read candidate = value

variable [CompleteLinearOrder Value]

inductive Minimum (source : C) (compile : Candidate → Script)
    (inspect : (candidate : Candidate) → Option (Issue candidate)) (read : Candidate → Value) : Prop
  | attained (candidate : Candidate) (paid : Settled source (compile candidate))
      (checked : inspect candidate = none) (least : read candidate = sInf (values source compile inspect read))
  | approached (actual : (values source compile inspect read).Nonempty)
      (notAttained : sInf (values source compile inspect read) ∉ values source compile inspect read)
      (near : ∀ limit, sInf (values source compile inspect read) < limit →
        ∃ candidate, Settled source (compile candidate) ∧ inspect candidate = none ∧ read candidate < limit)
  | obstructed (issues : ∀ candidate, Recorded source (compile candidate) ∧
      (Nonempty (Obstruction source (compile candidate)) ∨ ∃ issue, inspect candidate = some issue))

theorem resolve (source : C) (compile : Candidate → Script)
    (inspect : (candidate : Candidate) → Option (Issue candidate)) (read : Candidate → Value) :
    Minimum source compile inspect read := by
  classical
  let feasible := values source compile inspect read
  by_cases attained : sInf feasible ∈ feasible
  · obtain ⟨candidate, paid, checked, exactValue⟩ := attained
    exact .attained candidate paid checked exactValue
  by_cases nonempty : feasible.Nonempty
  · refine .approached nonempty attained ?_
    intro limit closer
    obtain ⟨value, ⟨candidate, paid, checked, rfl⟩, strict⟩ := sInf_lt_iff.mp closer
    exact ⟨candidate, paid, checked, strict⟩
  · refine .obstructed (fun candidate => ⟨record source _, ?_⟩)
    cases decideAt source (compile candidate) with
    | blocked issue => exact .inl ⟨issue⟩
    | feasible paid =>
        cases observed : inspect candidate with
        | some issue => exact .inr ⟨issue, rfl⟩
        | none =>
            exact (nonempty ⟨read candidate, candidate, settle source _ paid, observed, rfl⟩).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Compiled
