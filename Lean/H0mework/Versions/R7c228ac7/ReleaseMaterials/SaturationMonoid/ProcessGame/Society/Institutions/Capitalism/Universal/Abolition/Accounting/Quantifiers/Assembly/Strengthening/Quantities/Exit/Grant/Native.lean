import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Native
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Admission

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction.Repayment
open Innovation.Contribution.Pricing.Root.Runtime
open Redemption (sourceLaw sourceOrigin rate lower)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

def grantScript (source : C) (position : Position Party Instrument) (quantity : ℚ) :=
  Execution.primitiveScript (word (sourceLaw source) position quantity)

structure PaidAt (source : C) (position : Position Party Instrument) (quantity : ℚ) : Prop where
  qualified : Qualified (sourceLaw source) (sourceOrigin source) source.raw position quantity
  actual : Trace source (word (sourceLaw source) position quantity)
    (Execution.endAt source (grantScript source position quantity))
  ready : Ready (Execution.endAt source (grantScript source position quantity))
  available : ReviewAvailable (Execution.endAt source (grantScript source position quantity))
  account : Recorded source (grantScript source position quantity)

theorem paid_grant_is_the_literal_original_issue_and_redemption
    (source : C) (position : Position Party Instrument) (quantity : ℚ)
    (ready : Ready source) (review : ReviewAvailable source)
    (qualified : Qualified (sourceLaw source) (sourceOrigin source) source.raw position quantity) :
    PaidAt source position quantity := by
  have valid : ∀ item ∈ ((sourceLaw source).execute source.raw 0 (word (sourceLaw source) position quantity)).items,
      (sourceLaw source).Valid item.before item.request := by
    simp only [word, RawLaw.execute, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨qualified.1, qualified.2.2.1⟩
  have signed : ∀ request ∈ word (sourceLaw source) position quantity, request.consents = [] := by
    intro request listed
    simp only [word, List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl <;> rfl
  obtain ⟨trace, finished, available⟩ := Execution.pay_checked_primitives source
    (word (sourceLaw source) position quantity) 0 ready review signed valid
  exact ⟨qualified, trace, finished, available, record source _⟩

theorem original_public_issue_is_valid (source : C) (position : Position Party Instrument) (quantity : ℚ)
    (nonnegative : 0 ≤ quantity) :
    (sourceLaw source).Valid source.raw (issue (sourceLaw source) position quantity) := by
  refine ⟨⟨rfl, rfl⟩, fun _ _ => Or.inl rfl, nonnegative, ?_, ?_, ?_⟩ <;> simp [issue, RawLaw.debit,
    RawLaw.credit, NonnegativeBundle]

theorem actual_grant_amounts_fill_the_exact_original_funded_interval
    (source : C) (position : Position Party Instrument) (quantity : ℚ)
    (ready : Ready source) (review : ReviewAvailable source) :
    PaidAt source position quantity ↔
      position.debtor ≠ position.creditor ∧ 0 < rate (sourceLaw source) position ∧
      0 ≤ balance position source.raw ∧
      lower (sourceLaw source) (sourceOrigin source) source.raw position ≤ quantity ∧
      quantity ≤ stockCeiling (sourceLaw source) (sourceOrigin source) source.raw position := by
  have exactDomain := every_grant_is_exactly_checked_at_its_source_floor_and_stock_ceiling
    (sourceLaw source) (sourceOrigin source) source.raw position quantity
  constructor
  · intro paid
    obtain ⟨_, distinct, positive, claims, floor, stock, _⟩ := exactDomain.mp paid.qualified
    exact ⟨distinct, positive, claims, floor, stock⟩
  · rintro ⟨distinct, positive, claims, floor, stock⟩
    have nonnegative : 0 ≤ lower (sourceLaw source) (sourceOrigin source) source.raw position :=
      div_nonneg (le_max_left _ _) positive.le
    exact paid_grant_is_the_literal_original_issue_and_redemption source position quantity ready review
      (exactDomain.mpr ⟨original_public_issue_is_valid source position quantity (nonnegative.trans floor),
        distinct, positive, claims, floor, stock, ⟨rfl, fun _ _ => rfl⟩⟩)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant
