import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee.Decision
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Compiled

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee

open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Plan" => Script × Script

def feeCut (source : C) (plan : Plan) := Execution.endAt source plan.1

def compile (source : C) (plan : Plan) := plan.1 ++ script (feeCut source plan) ++ plan.2

def observedFee (source : C) (plan : Plan) : EReal :=
  match selected? (feeCut source plan) with
  | none => 0
  | some original => ((original.fee.scope.amount : ℝ) : EReal)

def checkPlan (source : C) (plan : Plan) := inspect (feeCut source plan)

theorem exact_fees_are_generated_by_safe_and_settled_original_programmes
    (source : C) (amount : EReal) :
    amount ∈ Bounds.Compiled.values source (compile source) (checkPlan source) (observedFee source) ↔
      ∃ plan, Settled source (compile source plan) ∧
        ∃ safe : SafeAt (feeCut source plan), ((safe.fee.fee.scope.amount : ℝ) : EReal) = amount := by
  constructor
  · rintro ⟨plan, paid, seen, exactAmount⟩
    obtain ⟨safe⟩ := (inspection_recognizes_exactly_the_original_safe_fee _).mp seen
    unfold observedFee at exactAmount
    rw [safe.original] at exactAmount
    exact ⟨plan, paid, safe, exactAmount⟩
  · rintro ⟨plan, paid, safe, exactAmount⟩
    refine ⟨plan, paid, (inspection_recognizes_exactly_the_original_safe_fee _).mpr ⟨safe⟩, ?_⟩
    unfold observedFee
    rw [safe.original]
    exact exactAmount

theorem the_original_review_has_a_tight_paid_fee_envelope (source : C) :
    Bounds.Compiled.Minimum source (compile source) (checkPlan source) (observedFee source) ∧
      Bounds.Compiled.Minimum source (compile source) (checkPlan source)
        (fun plan => OrderDual.toDual (observedFee source plan)) :=
  ⟨Bounds.Compiled.resolve _ _ _ _, Bounds.Compiled.resolve _ _ _ _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee
