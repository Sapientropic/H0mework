import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System.Envelope
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers.Completed

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System.Consumers

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers
  (position proposal original_unit every_positive_small_grant_executes_and_leaves_an_actual_exit_service)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption (sourceLaw rate unit)
open Innovation.Contribution.Pricing.Consumers.Actual (task source_input_is_the_original_registered_input)

noncomputable section

def compileGrant (quantity : ℚ) := compile lifeSource position (proposal quantity)

def checkGrant (_ : Unit) (quantity : ℚ) :=
  inspectPlan lifeSource position [] task (proposal quantity)

def originalCashDraw (quantity : ℚ) (actor : Bool) : EReal :=
  (((lifeSource.raw.stock actor false -
    (redeemed lifeSource position (proposal quantity)).raw.stock actor false : ℚ) : ℝ) : EReal)

private theorem actual_cash_coordinates (quantity : ℚ) (paid : PaidAt lifeSource position quantity) :
    originalCashDraw quantity false = (((-quantity : ℚ) : ℝ) : EReal) ∧
      originalCashDraw quantity true = ((quantity : ℝ) : EReal) := by
  have readRate : rate (sourceLaw lifeSource) position = 1 := by
    unfold rate sourceLaw
    rw [source_input_is_the_original_registered_input]
    rfl
  have material : actualMaterial lifeSource position (proposal quantity) = quantity := by
    change quantity * rate (sourceLaw lifeSource) position = quantity
    rw [readRate, mul_one]
  have receiver := material_amount_is_literal_received_stock lifeSource position (proposal quantity) paid
  have payer := the_issued_amount_is_the_same_real_debit_of_its_original_payer
    lifeSource position (proposal quantity) paid
  change (redeemed lifeSource position (proposal quantity)).raw.stock false (unit (sourceLaw lifeSource) position) =
    lifeSource.raw.stock false (unit (sourceLaw lifeSource) position) + actualMaterial lifeSource position (proposal quantity) at receiver
  change (redeemed lifeSource position (proposal quantity)).raw.stock true (unit (sourceLaw lifeSource) position) =
    lifeSource.raw.stock true (unit (sourceLaw lifeSource) position) - actualMaterial lifeSource position (proposal quantity) at payer
  rw [original_unit, material] at receiver payer
  unfold originalCashDraw
  rw [receiver, payer]
  constructor <;> apply congrArg (fun value : ℚ => ((value : ℝ) : EReal)) <;> ring

def incompatibleCaps (actor : Bool) : EReal :=
  if actor then ((1 / 2 : ℝ) : EReal) else ((-1 : ℝ) : EReal)

private theorem passes_for_small_positive_grant (quantity : ℚ) (positive : 0 < quantity) (bounded : quantity ≤ 1) :
    originalCashDraw quantity ∈ values lifeSource compileGrant checkGrant originalCashDraw := by
  have paid := every_positive_small_grant_executes_and_leaves_an_actual_exit_service quantity positive bounded
  apply (an_assignment_is_in_the_joint_domain_exactly_when_the_original_root_pays_it
    lifeSource compileGrant checkGrant originalCashDraw _).mpr
  exact ⟨quantity, paid.root, fun _ => (inspect_passes_iff_funded_and_independently_served _ _ _ _ _).mpr
    paid.eligible, rfl⟩

theorem each_original_cash_cap_can_be_paid_separately (actor : Bool) :
    ∃ profile ∈ values lifeSource compileGrant checkGrant originalCashDraw, profile actor ≤ incompatibleCaps actor := by
  cases actor with
  | false =>
    have positive : (0 : ℚ) < 1 := by norm_num
    have paid := (every_positive_small_grant_executes_and_leaves_an_actual_exit_service 1 positive le_rfl).grant
    refine ⟨originalCashDraw 1, passes_for_small_positive_grant 1 positive le_rfl, ?_⟩
    rw [(actual_cash_coordinates 1 paid).1]
    norm_num [incompatibleCaps]
  | true =>
    have positive : (0 : ℚ) < 1 / 2 := by norm_num
    have bounded : (1 / 2 : ℚ) ≤ 1 := by norm_num
    have paid := (every_positive_small_grant_executes_and_leaves_an_actual_exit_service (1 / 2) positive bounded).grant
    refine ⟨originalCashDraw (1 / 2), passes_for_small_positive_grant _ positive bounded, ?_⟩
    rw [(actual_cash_coordinates (1 / 2) paid).2]
    norm_num [incompatibleCaps]

theorem no_original_grant_can_jointly_pay_both_cash_caps :
    ¬ ∃ profile ∈ values lifeSource compileGrant checkGrant originalCashDraw, profile ≤ incompatibleCaps := by
  rintro ⟨profile, actual, within⟩
  obtain ⟨quantity, paid, passed, rfl⟩ :=
    (an_assignment_is_in_the_joint_domain_exactly_when_the_original_root_pays_it
      lifeSource compileGrant checkGrant originalCashDraw profile).mp actual
  have grant := ((complete_iff_original_paid_and_eligible lifeSource position [] task (proposal quantity)).mpr
    ⟨paid, passed ()⟩).grant
  obtain ⟨receiver, payer⟩ := actual_cash_coordinates quantity grant
  have lower := within false
  have upper := within true
  rw [receiver] at lower
  rw [payer] at upper
  change (((-quantity : ℚ) : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal) at lower
  change ((quantity : ℝ) : EReal) ≤ ((1 / 2 : ℝ) : EReal) at upper
  have lo := EReal.coe_le_coe_iff.mp lower
  have hi := EReal.coe_le_coe_iff.mp upper
  push_cast at lo
  linarith

theorem the_incompatible_caps_keep_every_original_account_and_exact_obstruction :
    ∀ quantity, Recorded lifeSource (compileGrant quantity) ∧
      Nonempty (BoxIssue lifeSource compileGrant checkGrant originalCashDraw incompatibleCaps quantity) := by
  exact (a_joint_box_is_paid_or_has_an_exact_original_issue_for_every_plan lifeSource compileGrant checkGrant
    originalCashDraw incompatibleCaps).resolve_left no_original_grant_can_jointly_pay_both_cash_caps

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System.Consumers
