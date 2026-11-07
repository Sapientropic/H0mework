import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.SourceRank
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Action.Installed

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Drain

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (current : frame.V.Current)
  (actual : Accounting.Current input depth count frame.anchor)

local notation "sourceMass" => Accounting.mass input depth count prefixLimit renewalLimit oldPast start
local notation "nativeStep" => Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start

theorem actual_work_iff_positive_source_mass :
    Public.Inquiry.HasWork frame actual ↔ 0 < sourceMass actual := by
  constructor
  · intro work
    by_contra notPositive
    obtain ⟨paid, nohead⟩ := zero_source_mass_has_no_unpaid_internal_work
      input depth count prefixLimit renewalLimit oldPast start actual (Nat.eq_zero_of_not_pos notPositive)
    simp [Public.Inquiry.HasWork, paid, nohead] at work
  · intro positive
    by_contra noWork
    have paid : actual.bodyPaid = true := by
      cases flag : actual.bodyPaid <;> simp_all [Public.Inquiry.HasWork]
    have nohead : item? input depth count prefixLimit renewalLimit oldPast start actual = none := by
      cases found : item? input depth count prefixLimit renewalLimit oldPast start actual with
      | none => rfl
      | some item => exact (noWork (.inr (by simp [found]))).elim
    have unchanged : nativeStep actual = actual := by
      rw [Accounting.nativeNext, dif_pos paid, nohead]
    have lowered := every_positive_source_mass_is_strictly_consumed
      input depth count prefixLimit renewalLimit oldPast start actual positive
    rw [unchanged] at lowered
    exact Nat.lt_irrefl _ lowered

theorem every_actual_internal_restriction_spends_one_position
    (work : Public.Inquiry.HasWork frame actual) :
    sourceMass (nativeStep actual) + 1 = sourceMass actual := by
  by_cases paid : actual.bodyPaid = true
  · cases present : item? input depth count prefixLimit renewalLimit oldPast start actual with
    | none => simp [Public.Inquiry.HasWork, paid, present] at work
    | some item =>
      exact every_native_financial_head_spends_its_actual_position
        input depth count prefixLimit renewalLimit oldPast start actual paid item present
  · have same := the_unexecuted_body_is_the_original_initial_state actual paid
    subst actual
    exact the_source_body_spends_its_actual_step input depth count prefixLimit renewalLimit oldPast start

/-- The ordinary source restriction is the original frame successor. The
query compiler separately routes a new claim through the born programme. -/
theorem the_original_frame_successor_consumes_the_same_source_position
    (aligned : frame.cursor current = some actual) (work : Public.Inquiry.HasWork frame actual) :
    ∃ after : Accounting.Current input depth count frame.anchor,
      frame.cursor (frame.successor current).targetCurrent = some after ∧
      sourceMass after + 1 = sourceMass actual :=
  ⟨nativeStep actual, frame.cursor_next current actual aligned,
    every_actual_internal_restriction_spends_one_position frame actual work⟩

variable (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (aligned : frame.cursor visit.current = some actual)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start actual)
  (reader : Macro.Raw.Reader input depth count)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current))

/-- The complete action has already paid its actual issue position across
anchor birth; its fresh root never restarts the old inventory or body. -/
theorem the_complete_born_action_spends_the_original_actual_head :
    ∃ after : Accounting.Current input depth count registered.admitted,
      (Born.Action.completeFrame frame visit actual registered reader).cursor
        (Born.Action.completeGenerated frame visit actual aligned registered reader authority
          (frame.root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit)).target.targetVisit.current = some after ∧
      sourceMass after + 1 = sourceMass actual :=
  ⟨registered.next,
    Born.Action.the_complete_next_keeps_the_literal_consumed_head frame visit actual registered reader,
    the_original_admission_spends_exactly_its_actual_head input depth count prefixLimit renewalLimit oldPast start registered⟩

#print axioms actual_work_iff_positive_source_mass
#print axioms the_original_frame_successor_consumes_the_same_source_position
#print axioms the_complete_born_action_spends_the_original_actual_head

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Drain
