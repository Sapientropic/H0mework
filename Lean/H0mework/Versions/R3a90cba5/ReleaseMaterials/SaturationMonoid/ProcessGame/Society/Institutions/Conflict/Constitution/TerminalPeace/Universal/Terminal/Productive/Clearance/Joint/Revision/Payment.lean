import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Reserve
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Disposition

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation (Key)
open Reparation.Actual (ReceiptAnswers Occurrence Script)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Occurrence seed community) (answers : ReceiptAnswers seed)
  (front : Script Party Good Port Technology Instrument) (key : Key Party Good)

def materialMargin : ℚ :=
  (prefixRaw loss front).stock key.2.1 key.2.2 - reserveAt loss front key.2.1 key.2.2

/-- The largest material transfer supported by this debt and this
inventory. Authority and independent acceptance are checked separately. -/
def maximumInstallment : ℚ :=
  min (dueFor key (prefixRows loss answers front)) (max 0 (materialMargin loss front key))

theorem maximumInstallment_nonnegative : 0 ≤ maximumInstallment loss answers front key :=
  le_min (dueFor_nonnegative _ _) (le_max_left _ _)

theorem maximumInstallment_pos_iff :
    0 < maximumInstallment loss answers front key ↔
      0 < dueFor key (prefixRows loss answers front) ∧ 0 < materialMargin loss front key := by
  rw [maximumInstallment, lt_min_iff, lt_max_iff]
  simp

theorem material_installment_iff (quantity : ℚ) (positive : 0 < quantity) :
    quantity ≤ maximumInstallment loss answers front key ↔
      quantity ≤ dueFor key (prefixRows loss answers front) ∧
        reserveAt loss front key.2.1 key.2.2 + quantity ≤
          (prefixRaw loss front).stock key.2.1 key.2.2 := by
  rw [maximumInstallment, le_min_iff, le_max_iff]
  simp only [not_le_of_gt positive, false_or, materialMargin]
  constructor <;> rintro ⟨owing, stock⟩ <;> exact ⟨owing, by linarith only [stock]⟩

theorem original_stock_shortage_is_exact :
    maximumInstallment loss answers front key = 0 ↔
      dueFor key (prefixRows loss answers front) = 0 ∨
      (prefixRaw loss front).stock key.2.1 key.2.2 ≤ reserveAt loss front key.2.1 key.2.2 := by
  have zero (x : ℚ) (nonnegative : 0 ≤ x) : x = 0 ↔ ¬ 0 < x :=
    ⟨by rintro rfl; exact lt_irrefl 0, fun notPos => le_antisymm (le_of_not_gt notPos) nonnegative⟩
  rw [zero _ (maximumInstallment_nonnegative loss answers front key), maximumInstallment_pos_iff,
    not_and_or, ← zero _ (dueFor_nonnegative _ _)]
  simp only [not_lt, materialMargin, sub_nonpos]

theorem maximumInstallment_covers_the_entire_due_iff
    (owing : 0 < dueFor key (prefixRows loss answers front)) :
    maximumInstallment loss answers front key = dueFor key (prefixRows loss answers front) ↔
      reserveAt loss front key.2.1 key.2.2 + dueFor key (prefixRows loss answers front) ≤
        (prefixRaw loss front).stock key.2.1 key.2.2 := by
  constructor
  · intro exactAmount
    exact ((material_installment_iff loss answers front key _ owing).mp exactAmount.ge).2
  · intro funded
    exact le_antisymm (min_le_left _ _)
      ((material_installment_iff loss answers front key _ owing).mpr ⟨le_rfl, funded⟩)

variable (purpose : Port)

/-- A refusal of a materially affordable amount is attributed to the
original payment channel at that exact material position. -/
theorem funded_issue_is_original_channel
    (issue : InstallmentIssue loss answers (reserveAt loss front) front purpose key
      (maximumInstallment loss answers front key))
    (positive : 0 < maximumInstallment loss answers front key) :
    match issue with
    | .nonpositive _ | .exceedsDue _ | .shortage _ => False
    | .sameParty _ | .policy _ | .stockPort _ | .payerRefused _ _ _ | .victimRefused _ _ _ => True := by
  have exactBound := (material_installment_iff loss answers front key _ positive).mp le_rfl
  cases issue with
  | nonpositive failed => exact (not_le_of_gt positive) failed
  | exceedsDue failed => exact (not_lt_of_ge exactBound.1) failed
  | shortage failed => exact (not_lt_of_ge exactBound.2) failed
  | sameParty _ | policy _ | stockPort _ | payerRefused _ _ _ | victimRefused _ _ _ => trivial

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve
