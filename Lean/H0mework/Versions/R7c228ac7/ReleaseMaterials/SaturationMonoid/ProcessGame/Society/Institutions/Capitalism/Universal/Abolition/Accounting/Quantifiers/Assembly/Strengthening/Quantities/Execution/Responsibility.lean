import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Fold
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Proposal" => Compile.RawInput Party Good Port Technology Instrument
local notation "Script" => List (Option Proposal)

abbrev ClaimAt (source : C) := source.native.frame.N.Claim

abbrev RowAt (source : C) :=
  OpenResponsibilityAt source.native.frame.N (source.native.frame.sourceSupport source.native.visit.current)

private def stepClaim (source : C) :
    (proposal : Option Proposal) → ClaimAt source → ClaimAt (next source proposal)
  | none => Characterization.Escape.nextClaim source
  | some raw => Characterization.Escape.nextClaim (query source (some raw))

private def stepRow (source : C) :
    (proposal : Option Proposal) → RowAt source → RowAt (next source proposal)
  | none => Characterization.Escape.nextRow source
  | some raw => Characterization.Escape.nextRow (query source (some raw))

private theorem stepClaim_injective (source : C) (proposal : Option Proposal) :
    Function.Injective (stepClaim source proposal) := by
  cases proposal
  · exact Characterization.Escape.nextClaim_does_not_merge_original_claims source
  · exact Characterization.Escape.nextClaim_does_not_merge_original_claims (query source (some _))

private theorem stepRow_exact (source : C) (proposal : Option Proposal) (row : RowAt source) :
    (stepRow source proposal row).claim = stepClaim source proposal row.claim ∧
      (stepRow source proposal row).progressBudget ≤ row.progressBudget := by
  cases proposal with
  | none =>
      exact ⟨Characterization.Escape.nextRow_keeps_the_same_source_claim source row,
        Characterization.Escape.nextRow_never_refills_an_original_residual source row⟩
  | some raw =>
      let cut := query source (some raw)
      exact ⟨Characterization.Escape.nextRow_keeps_the_same_source_claim cut row,
        Characterization.Escape.nextRow_never_refills_an_original_residual cut row⟩

def claimAt : (source : C) → (script : Script) → ClaimAt source → ClaimAt (endAt source script)
  | _, [], claim => claim
  | source, proposal :: tail, claim =>
      claimAt (next source proposal) tail (stepClaim source proposal claim)

def rowAt : (source : C) → (script : Script) → RowAt source → RowAt (endAt source script)
  | _, [], row => row
  | source, proposal :: tail, row =>
      rowAt (next source proposal) tail (stepRow source proposal row)

theorem claimAt_injective (source : C) (script : Script) :
    Function.Injective (claimAt source script) := by
  induction script generalizing source with
  | nil => exact Function.injective_id
  | cons proposal tail ih => exact (ih _).comp (stepClaim_injective source proposal)

theorem rowAt_exact (source : C) (script : Script) (row : RowAt source) :
    (rowAt source script row).claim = claimAt source script row.claim ∧
      (rowAt source script row).progressBudget ≤ row.progressBudget := by
  induction script generalizing source with
  | nil => exact ⟨rfl, le_rfl⟩
  | cons proposal tail ih =>
      have first := stepRow_exact source proposal row
      have rest := ih (next source proposal) (stepRow source proposal row)
      exact ⟨rest.1.trans (congrArg (claimAt (next source proposal) tail) first.1),
        rest.2.trans first.2⟩

theorem paid_row_stays_paid (source : C) (script : Script) (row : RowAt source)
    (paid : row.progressBudget = 0) : (rowAt source script row).progressBudget = 0 :=
  Nat.eq_zero_of_le_zero ((rowAt_exact source script row).2.trans paid.le)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
