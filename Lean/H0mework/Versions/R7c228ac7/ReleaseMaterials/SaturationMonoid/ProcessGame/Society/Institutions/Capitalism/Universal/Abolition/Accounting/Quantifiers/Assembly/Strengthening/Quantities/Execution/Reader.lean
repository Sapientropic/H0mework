import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Coverage

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

theorem the_actual_script_keeps_the_original_reader_indices (source : C) (script : Script) :
    (endAt source script).native.input = source.native.input ∧
      (endAt source script).native.depth = source.native.depth ∧
      (endAt source script).native.count = source.native.count := by
  induction script generalizing source with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons request tail rest =>
    have later := rest (next source request)
    have original :
        (next source request).native.depth = source.native.depth ∧
          (next source request).native.count = source.native.count := by
      cases request with
      | none =>
        exact ⟨source.advance_parameters.2.1, source.advance_parameters.2.2.1⟩
      | some request =>
        let queried := query source (some request)
        exact ⟨queried.advance_parameters.2.1, queried.advance_parameters.2.2.1⟩
    exact ⟨endAt_input source _, later.2.1.trans original.1, later.2.2.trans original.2⟩

/-- Keep the source's own rule while feeding it the actual new cursor and
whole account. Temporary raw submissions do not become the policy. -/
def originalReaderAt (source : C) (script : Script) :
    Raw.Reader (endAt source script).native.input (endAt source script).native.depth (endAt source script).native.count := by
  intro cursor account
  refine source.native.reader cursor (cast ?_ account)
  obtain ⟨input, depth, count⟩ := the_actual_script_keeps_the_original_reader_indices source script
  rw [input, depth, count]

def originalResponse (source : C) (script : Script) : Compile.RawInput Party Good Port Technology Instrument :=
  (endAt source script).native.actual.proposal (originalReaderAt source script)

theorem a_constant_original_reader_does_not_repeat_a_temporary_submission
    (source : C) (script : Script) (request : Compile.RawInput Party Good Port Technology Instrument)
    (owned : source.native.reader = fun _ _ => request) :
    originalResponse source script = request := by
  unfold originalResponse Public.Inquiry.ActualAt.proposal originalReaderAt
  rw [owned]

def originalResponses (source : C) (front : Script) : Nat → Script
  | 0 => []
  | count + 1 =>
      let previous := originalResponses source front count
      previous ++ [some (originalResponse source (front ++ previous))]

theorem each_response_queries_the_original_rule_on_its_paid_prefix
    (source : C) (front : Script) (count : Nat) :
    endAt source (front ++ originalResponses source front (count + 1)) =
      next (endAt source (front ++ originalResponses source front count))
        (some (originalResponse source (front ++ originalResponses source front count))) := by
  rw [originalResponses, ← List.append_assoc, endAt_append]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
