import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Source

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped
open Institutions.Capitalism.Universal.Source.Program

theorem access_step_independent (before : AuditCurrent) (actor : Party) (left right : Query) :
    auditLaw.step before (accessRequest actor left) = auditLaw.step before (accessRequest actor right) := by
  have same := (access_valid_iff before actor left).trans (access_valid_iff before actor right).symm
  by_cases accepted : auditLaw.Valid before (accessRequest actor left)
  · have other := same.mp accepted
    rw [RawLaw.step,if_pos accepted,RawLaw.step,if_pos other]
    rfl
  · rw [auditLaw.rejected_preserves_current _ _ accepted,
      auditLaw.rejected_preserves_current _ _ (fun paid => accepted (same.mpr paid))]

theorem read_next_independent (before : AuditCurrent) (actor : Party) (left right : Query) :
    auditLaw.next before (readWord before actor left) = auditLaw.next before (readWord before actor right) := by
  have step := access_step_independent before actor left right
  have permission := (access_valid_iff before actor left).trans (access_valid_iff before actor right).symm
  by_cases paid : auditLaw.Valid before (accessRequest actor left) ∧
      auditLaw.Valid (auditLaw.step before (accessRequest actor left)) deliveryFee
  · have other : auditLaw.Valid before (accessRequest actor right) ∧
        auditLaw.Valid (auditLaw.step before (accessRequest actor right)) deliveryFee :=
      ⟨permission.mp paid.1,step ▸ paid.2⟩
    rw [readWord,if_pos paid,readWord,if_pos other]
    change { auditLaw.step (auditLaw.step before (accessRequest actor left)) deliveryFee with
      clock := before.clock + max 0 (auditLaw.duration before),round := before.round + 1 } = _
    rw [step]
    rfl
  · have other : ¬ (auditLaw.Valid before (accessRequest actor right) ∧
        auditLaw.Valid (auditLaw.step before (accessRequest actor right)) deliveryFee) := by
      intro accepted
      exact paid ⟨permission.mpr accepted.1,step.symm ▸ accepted.2⟩
    rw [readWord,if_neg paid,readWord,if_neg other]
    change { auditLaw.step before (accessRequest actor left) with
      clock := before.clock + max 0 (auditLaw.duration before),round := before.round + 1 } = _
    rw [step]
    rfl

theorem emit_next_independent (before : AuditCurrent) (left right : Nat → Query) (larger : Bool) :
    auditLaw.next before (emit left larger before) = auditLaw.next before (emit right larger before) := by
  unfold emit
  dsimp only
  split
  all_goals first | rfl | exact read_next_independent _ _ _ _ | (split <;> first | rfl | exact read_next_independent _ _ _ _)

theorem query_masks_do_not_change_material_history (left right : Nat → Query) (larger : Bool) (ordinal : Nat) :
    current left larger ordinal = current right larger ordinal := by
  induction ordinal with
  | zero => rw [current_zero,current_zero]
  | succ ordinal ih =>
      simp only [current_succ,ih]
      cases ordinal with
      | zero => rfl
      | succ ordinal => exact emit_next_independent _ _ _ _

def shift (before : AuditCurrent) (count : Nat) : AuditCurrent :=
  { before with clock := before.clock + count,round := before.round + count }

theorem exhausted_base (larger : Bool) :
    (current defaultQuery larger 14).stock 2 .labor = 0 ∧
    (current defaultQuery larger 14).round = initial.round + 14 := by
  cases larger <;> decide +kernel

theorem exhausted_emit (queries : Nat → Query) (larger : Bool) (before : AuditCurrent)
    (late : 10 ≤ before.round - initial.round) (empty : before.stock 2 .labor = 0) :
    emit queries larger before = [accessRequest 2 (queries (before.round - initial.round))] := by
  have denied : ¬ auditLaw.Valid before (accessRequest 2 (queries (before.round - initial.round))) := by
    rw [access_valid_iff,empty]
    norm_num
  unfold emit
  dsimp only
  split
  all_goals first | omega | skip
  rw [if_pos late,readWord,if_neg (fun accepted => denied accepted.1)]

theorem exhausted_history_is_its_own_continuing_tail (larger : Bool) (count : Nat) :
    current defaultQuery larger (14 + count) = shift (current defaultQuery larger 14) count := by
  induction count with
  | zero => simp [shift]
  | succ count ih =>
      rw [Nat.add_succ,current_succ,if_neg (show 14 + count ≠ 0 by omega)]
      rw [ih]
      have empty : (shift (current defaultQuery larger 14) count).stock 2 .labor = 0 := (exhausted_base larger).1
      have late : 10 ≤ (shift (current defaultQuery larger 14) count).round - initial.round := by
        simp only [shift,exhausted_base larger |>.2]
        omega
      rw [exhausted_emit _ _ _ late empty]
      have denied : ¬ auditLaw.Valid (shift (current defaultQuery larger 14) count)
          (accessRequest 2 (defaultQuery ((shift (current defaultQuery larger 14) count).round - initial.round))) := by
        rw [access_valid_iff,empty]
        norm_num
      simp only [RawLaw.next,RawLaw.execute,auditLaw.rejected_preserves_current _ _ denied]
      apply RawCurrent.ext <;> try rfl
      · change (current defaultQuery larger 14).clock + (count : ℚ) + 1 = _
        simp only [shift]
        push_cast
        ring

structure PublicView where
  permission : Mandate.State Party Technology
  clock : ℚ
  round : Nat
  labor0 : ℚ
  labor1 : ℚ
  labor2 : ℚ
  labor3 : ℚ
  deriving DecidableEq

def permittedView (before : AuditCurrent) : PublicView :=
  ⟨before.technology,before.clock,before.round,before.stock 0 .labor,
    before.stock 1 .labor,before.stock 2 .labor,before.stock 3 .labor⟩

def PublicView.shift (view : PublicView) (count : Nat) : PublicView :=
  { view with clock := view.clock + count,round := view.round + count }

theorem permittedView_shift (before : AuditCurrent) (count : Nat) :
    permittedView (shift before count) = (permittedView before).shift count := rfl

theorem every_current_has_the_same_permitted_view (queries : Nat → Query) (ordinal : Nat) :
    permittedView (current queries false ordinal) = permittedView (current queries true ordinal) := by
  rw [query_masks_do_not_change_material_history queries defaultQuery false,
    query_masks_do_not_change_material_history queries defaultQuery true]
  by_cases early : ordinal < 15
  · interval_cases ordinal <;> decide +kernel +revert
  · have decompose : ordinal = 14 + (ordinal - 14) := by omega
    rw [decompose,exhausted_history_is_its_own_continuing_tail,exhausted_history_is_its_own_continuing_tail,
      permittedView_shift,permittedView_shift]
    have same : permittedView (current defaultQuery false 14) = permittedView (current defaultQuery true 14) := by decide +kernel
    rw [same]

theorem all_available_labor_is_actually_accounted :
    (current defaultQuery false 14).stock 0 .labor = 0 ∧
    (current defaultQuery false 14).stock 1 .labor = 1 ∧
    (current defaultQuery false 14).stock 2 .labor = 0 ∧
    (current defaultQuery false 14).stock 3 .labor = 0 := by decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped
