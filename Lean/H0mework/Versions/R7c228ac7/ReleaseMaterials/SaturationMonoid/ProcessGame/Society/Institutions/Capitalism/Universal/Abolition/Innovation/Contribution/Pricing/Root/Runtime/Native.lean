import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Action
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Native
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Parameters

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Abolition.Accounting.Quantifiers.Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (request : Request Party Good Port Technology Instrument)

def afterNative := (afterBody source request).advance

theorem the_actual_body_has_its_single_original_native_head
    (ready : Ready source) (available : ReviewAvailable source) (noConsents : request.consents = [])
    (valid : (Physical.Public.interpreter source.native.input).Valid source.raw request) :
    ∃ item,
      Public.Accounting.items (afterBody source request).native.input (afterBody source request).native.depth
        (afterBody source request).native.count (afterBody source request).native.prefixLimit
        (afterBody source request).native.renewalLimit (afterBody source request).native.oldPast
        (afterBody source request).native.start = [item] ∧
      Public.Accounting.item? (afterBody source request).native.input (afterBody source request).native.depth
        (afterBody source request).native.count (afterBody source request).native.prefixLimit
        (afterBody source request).native.renewalLimit (afterBody source request).native.oldPast
        (afterBody source request).native.start (afterBody source request).native.actual.actual = some item := by
  have complete : ¬ Public.Inquiry.HasWork (queued source request).native.frame
      (queued source request).native.actual.actual := ready
  have readers : (queued source request).executionReader = (queued source request).native.reader := by
    funext cursor account
    exact the_available_review_forwards_the_actual_requested_primitive source request available
  have original := Clearing.the_actual_raw_has_one_original_position
    (queued source request).native request rfl complete noConsents valid
  unfold afterBody
  rw [Evolving.Epoch.Current.advance_eq_epoch _ complete]
  let items := Public.Accounting.items source.native.input source.native.depth source.native.count
    source.native.prefixLimit source.native.renewalLimit source.native.oldPast
    (Factory.Direct.selectedStart (queued source request).native.full (queued source request).native.sourceActual
      (queued source request).executionReader)
  have length : items.length = 1 := by
    dsimp only [items]
    rw [readers]
    exact original
  obtain ⟨item,single⟩ := List.length_eq_one_iff.mp length
  refine ⟨item,single,?_⟩
  change (if true then items[0]? else none) = some item
  rw [single]
  rfl

theorem the_actual_body_must_consume_its_original_native_head
    (ready : Ready source) (available : ReviewAvailable source) (noConsents : request.consents = [])
    (valid : (Physical.Public.interpreter source.native.input).Valid source.raw request) :
    Public.Inquiry.HasWork (afterBody source request).native.frame (afterBody source request).native.actual.actual := by
  obtain ⟨item,_single,present⟩ := the_actual_body_has_its_single_original_native_head source request ready available noConsents valid
  exact Or.inr (by rw [present]; rfl)

variable (item : Epoch.Finance.ActualItem source.native.input source.native.depth source.native.count)
  (present : Public.Accounting.item? source.native.input source.native.depth source.native.count
    source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.start
    source.native.actual.actual = some item)

include present in
theorem native_head_uses_the_original_admission_or_consumption :
    HEq source.advance.native.actual.actual.account
      ((Epoch.Finance.consume source.native.input source.native.depth source.native.count item
        source.native.actual.actual.account).next source.native.input source.native.depth source.native.count) := by
  have work : Public.Inquiry.HasWork source.native.frame source.native.actual.actual := Or.inr (by rw [present]; rfl)
  unfold Evolving.Epoch.Current.advance
  rw [dif_pos work]
  cases generated : Public.Accounting.registration? source.native.input source.native.depth source.native.count
      source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.start
      source.native.actual.actual with
  | none =>
      apply heq_of_eq
      exact Public.Accounting.every_actual_head_has_its_literal_source_account _ _ _ _ _ _ _ _ source.native.bodyPaid item present
  | some registered =>
      apply heq_of_eq
      have same : registered.item = item := Option.some.inj (registered.present.symm.trans present)
      cases same
      exact (Public.Accounting.Born.the_same_actual_item_is_the_original_native_admission
        source.native.actual.actual registered).symm

include present in
theorem native_head_keeps_the_same_original_control : source.advance.control = source.control := by
  have work : Public.Inquiry.HasWork source.native.frame source.native.actual.actual := Or.inr (by rw [present]; rfl)
  unfold Evolving.Epoch.Current.advance
  rw [dif_pos work]
  cases generated : Public.Accounting.registration? source.native.input source.native.depth source.native.count
      source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.start
      source.native.actual.actual with
  | none => exact source.the_unconsumed_source_phase_is_not_reset_by_ordinary_accounting
  | some registered => exact source.native_birth_keeps_the_same_source_phase registered

include present in
theorem native_head_keeps_the_same_actual_material_cut : source.advance.raw = source.raw := by
  have work : Public.Inquiry.HasWork source.native.frame source.native.actual.actual := Or.inr (by rw [present]; rfl)
  unfold Evolving.Epoch.Current.advance
  rw [dif_pos work]
  cases generated : Public.Accounting.registration? source.native.input source.native.depth source.native.count
      source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.start
      source.native.actual.actual with
  | none =>
      change (Evolving.Epoch.Source.originalState source.ordinary.native).raw = _
      unfold Evolving.Epoch.Current.raw Evolving.Epoch.Source.originalState Public.Inquiry.ActualAt.snapshot
      rw [source.ordinary.native.bodyPaid,source.native.bodyPaid]
      rfl
  | some registered =>
      change (Evolving.Epoch.Source.originalState (source.birth registered).native).raw = _
      unfold Evolving.Epoch.Current.raw Evolving.Epoch.Source.originalState Public.Inquiry.ActualAt.snapshot
      rw [(source.birth registered).native.bodyPaid,source.native.bodyPaid]
      rfl

include present in
theorem the_single_native_head_finishes_at_its_next_actual_root
    (position : source.native.actual.actual.position = 0)
    (single : Public.Accounting.items source.native.input source.native.depth source.native.count
      source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.start = [item]) :
    Ready source.advance := by
  have work : Public.Inquiry.HasWork source.native.frame source.native.actual.actual := Or.inr (by rw [present]; rfl)
  unfold Evolving.Epoch.Current.advance
  rw [dif_pos work]
  cases generated : Public.Accounting.registration? source.native.input source.native.depth source.native.count
      source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.start
      source.native.actual.actual with
  | none =>
      change ¬ ((Public.Accounting.nativeNext source.native.input source.native.depth source.native.count
        source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.start
        source.native.actual.actual).bodyPaid = false ∨
        (Public.Accounting.item? source.native.input source.native.depth source.native.count
          source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.start
          (Public.Accounting.nativeNext source.native.input source.native.depth source.native.count
            source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.start
            source.native.actual.actual)).isSome = true)
      have next : Public.Accounting.nativeNext source.native.input source.native.depth source.native.count
          source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.start
          source.native.actual.actual = source.native.actual.actual.afterItem source.native.bodyPaid item := by
        unfold Public.Accounting.nativeNext
        rw [dif_pos source.native.bodyPaid,present]
      rw [next]
      have facts := Public.Accounting.Current.after_item_reads_the_source_generated_native_account
        source.native.actual.actual source.native.bodyPaid item
      simp only [facts.2.2,Public.Accounting.item?,facts.2.1,position,single]
      simp
  | some registered =>
      change ¬ (true = false ∨
        (if true then getElem? (Public.Accounting.items source.native.input source.native.depth source.native.count
          source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.start)
          (source.native.actual.actual.position + 1) else none).isSome = true)
      rw [position,single]
      simp

theorem two_actual_root_steps_pay_and_consume_the_generated_primitive
    (ready : Ready source) (available : ReviewAvailable source) (noConsents : request.consents = [])
    (valid : (Physical.Public.interpreter source.native.input).Valid source.raw request) :
    Ready (afterNative source request) ∧
      (afterNative source request).raw = (Physical.Public.interpreter source.native.input).step source.raw request := by
  obtain ⟨head,single,present⟩ := the_actual_body_has_its_single_original_native_head source request ready available noConsents valid
  have position : (afterBody source request).native.actual.actual.position = 0 := by
    let P := fun next : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument) => next.native.actual.actual.position = 0
    have complete : ¬ Public.Inquiry.HasWork (queued source request).native.frame
      (queued source request).native.actual.actual := ready
    change P (queued source request).advance
    exact (congrArg P (Evolving.Epoch.Current.advance_eq_epoch (queued source request) complete)).mpr rfl
  exact ⟨the_single_native_head_finishes_at_its_next_actual_root (afterBody source request) head present position single,
    (native_head_keeps_the_same_actual_material_cut (afterBody source request) head present).trans
      (the_original_root_executes_the_generated_request source request ready available noConsents valid).1⟩

theorem afterNative_keeps_the_same_original_input :
    (afterNative source request).native.input = source.native.input :=
  ((afterBody source request).advance_parameters.1).trans (queued source request).advance_parameters.1

theorem afterNative_keeps_the_available_review
    (ready : Ready source) (available : ReviewAvailable source) (noConsents : request.consents = [])
    (valid : (Physical.Public.interpreter source.native.input).Valid source.raw request) :
    ReviewAvailable (afterNative source request) := by
  obtain ⟨head,_single,headAt⟩ := the_actual_body_has_its_single_original_native_head source request ready available noConsents valid
  have control := native_head_keeps_the_same_original_control (afterBody source request) head headAt
  have review := (congrArg (fun control => control.review) control).trans
    (afterBody_keeps_the_original_review_coordinate source request ready available)
  unfold ReviewAvailable afterNative
  rw [review]
  exact available

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
