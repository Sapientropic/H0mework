import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Frontier
import Mathlib.Data.List.MinMax

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro PublicFunction Quantities

noncomputable section

variable {Party Good Port Technology Instrument TaskId : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Plan" => Proposal Party Good Port Technology Instrument

variable (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (ordered : List TaskId) (task : TaskId → PublicTaskSpec Party Good)
  (reserved : ∀ word : List (Option (Compile.RawInput Party Good Port Technology Instrument)),
    Finset (Due.Service.Ordinal source word))
  (held : Finset (Due.Service.Need ordered.toFinset task)) (budget : Party × Good → ℚ) (deadline : WithTop ℚ)

def admittedFrom (candidates : List Plan) : List Plan :=
  candidates.filter fun proposal => (refusal source ordered task reserved held budget deadline proposal).isNone

theorem admittedFrom_exact (candidates : List Plan) (proposal : Plan) :
    proposal ∈ admittedFrom source ordered task reserved held budget deadline candidates ↔
      proposal ∈ candidates ∧ Admitted source ordered task reserved held budget deadline proposal := by
  rw [admittedFrom, List.mem_filter]
  apply and_congr_right
  intro _
  rw [Option.isNone_iff_eq_none, has_no_refusal_iff]

variable {Value : Type*} [LinearOrder Value]

inductive Selection (candidates : List Plan) (read : Plan → Value)
  | selected (proposal : Plan) (submitted : proposal ∈ candidates)
      (paid : Admitted source ordered task reserved held budget deadline proposal)
      (least : ∀ other ∈ candidates, Admitted source ordered task reserved held budget deadline other →
        read proposal ≤ read other)
  | exhausted (failures : ∀ proposal ∈ candidates, Nonempty (Refusal source ordered task reserved held budget deadline proposal))

/-- An enumerated set of raw submissions has an attained tight selection
or a refusal at each original submission. The unrestricted domain is
separately compared by `resolve`. -/
def select (candidates : List Plan) (read : Plan → Value) :
    Selection source ordered task reserved held budget deadline candidates read :=
  let qualified := admittedFrom source ordered task reserved held budget deadline candidates
  match chosen : qualified.argmin read with
  | some proposal =>
    have original : proposal ∈ qualified.argmin read := Option.mem_def.mpr chosen
    have listed := (admittedFrom_exact source ordered task reserved held budget deadline candidates proposal).mp
      (List.argmin_mem original)
    .selected proposal listed.1 listed.2 fun other submitted paid =>
      List.le_of_mem_argmin
        ((admittedFrom_exact source ordered task reserved held budget deadline candidates other).mpr ⟨submitted, paid⟩)
        original
  | none => .exhausted fun proposal submitted =>
    match found : refusal source ordered task reserved held budget deadline proposal with
    | some reason => ⟨reason⟩
    | none =>
      have empty : qualified = [] := List.argmin_eq_none.mp chosen
      have listed : proposal ∈ qualified :=
        (admittedFrom_exact source ordered task reserved held budget deadline candidates proposal).mpr
          ⟨submitted, (has_no_refusal_iff source ordered task reserved held budget deadline proposal).mp found⟩
      (by simp only [empty, List.not_mem_nil] at listed : False).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff
