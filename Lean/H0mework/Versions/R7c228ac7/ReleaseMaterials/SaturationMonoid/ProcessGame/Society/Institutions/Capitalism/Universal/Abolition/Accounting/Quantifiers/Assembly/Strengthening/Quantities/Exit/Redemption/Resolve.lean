import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction.Repayment
open Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

abbrev floor (source : C) (position : Position Party Instrument) :=
  lower (sourceLaw source) (sourceOrigin source) source.raw position

abbrev ceiling (source : C) (position : Position Party Instrument) :=
  upper (sourceLaw source) (sourceOrigin source) source.raw position

inductive Blocker (source : C) (position : Position Party Instrument)
  | sameAddress (same : position.debtor = position.creditor)
  | rate (nonpositive : rate (sourceLaw source) position ≤ 0)
  | material (gap : ceiling source position < floor source position)
  | native (issue : NativeObstruction source)
  | review (unavailable : ¬ ReviewAvailable source)

inductive Decision (source : C) (position : Position Party Instrument)
  | paid (actual : PaidAt source position (floor source position))
  | blocked (issue : Blocker source position)

def decideMinimum (source : C) (position : Position Party Instrument) : Decision source position :=
  if distinct : position.debtor ≠ position.creditor then
    if positive : 0 < rate (sourceLaw source) position then
      if capacity : floor source position ≤ ceiling source position then
        match found : inspectNative source with
        | some issue => .blocked (.native issue)
        | none =>
            if review : ReviewAvailable source then
              .paid (the_original_root_attains_both_redemption_endpoints source position
                (native_is_finished_without_a_pending_item source found) review distinct positive capacity).1
            else .blocked (.review review)
      else .blocked (.material (lt_of_not_ge capacity))
    else .blocked (.rate (le_of_not_gt positive))
  else .blocked (.sameAddress (Classical.not_not.mp distinct))

def Decision.selected {source : C} {position : Position Party Instrument} :
    Decision source position → List (Option (Compile.RawInput Party Good Port Technology Instrument))
  | .paid _ => script source position (floor source position)
  | .blocked _ => []

theorem the_generated_redemption_keeps_its_whole_original_account
    (source : C) (position : Position Party Instrument) :
    Recorded source (decideMinimum source position).selected :=
  record source _

theorem sufficient_capacity_selects_and_pays_the_tight_amount
    (source : C) (position : Position Party Instrument)
    (ready : Ready source) (review : ReviewAvailable source)
    (distinct : position.debtor ≠ position.creditor) (positive : 0 < rate (sourceLaw source) position)
    (capacity : floor source position ≤ ceiling source position) :
    ∃ actual, decideMinimum source position = .paid actual := by
  unfold decideMinimum
  rw [dif_pos distinct, dif_pos positive, dif_pos capacity]
  split
  · rename_i issue observed
    exact (ready issue.pending).elim
  · rw [dif_pos review]
    exact ⟨(the_original_root_attains_both_redemption_endpoints source position
      ready review distinct positive capacity).1, rfl⟩

theorem a_material_blocker_excludes_every_safe_redemption_at_this_cut
    (source : C) (position : Position Party Instrument)
    (gap : ceiling source position < floor source position) :
    ∀ quantity, ¬ Safe (sourceLaw source) (sourceOrigin source) source.raw position quantity := by
  intro quantity safe
  have within := ((safe_iff_original_authority_and_tight_material_interval _ _ _ _ _).mp safe).2.2.1
  exact (not_le_of_gt gap) (within.1.trans within.2)

theorem a_material_blocker_names_the_original_financial_or_stock_shortage
    (source : C) (position : Position Party Instrument)
    (positive : 0 < rate (sourceLaw source) position)
    (gap : ceiling source position < floor source position) :
    balance position source.raw < floor source position ∨
      debtorStock (sourceLaw source) source.raw position -
        essentials (sourceLaw source) (sourceOrigin source) position.debtor (unit (sourceLaw source) position) <
      floor source position * rate (sourceLaw source) position := by
  unfold ceiling upper at gap
  rcases min_lt_iff.mp gap with principal | stock
  · exact .inl principal
  · exact .inr ((div_lt_iff₀ positive).mp stock)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption
