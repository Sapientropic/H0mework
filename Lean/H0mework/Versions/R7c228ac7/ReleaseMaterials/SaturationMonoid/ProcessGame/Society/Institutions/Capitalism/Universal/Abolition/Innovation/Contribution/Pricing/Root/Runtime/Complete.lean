import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Runner
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

theorem Trace.keeps_the_original_source_input {source target : C}
    {word : RawEvent Party Good Port Technology Instrument} (actual : Trace source word target) :
    target.native.input = source.native.input := by
  induction actual with
  | nil => rfl
  | cons source request tail target ready review noConsents valid later inherited =>
      exact inherited.trans (afterNative_keeps_the_same_original_input source request)

theorem Trace.raw_is_the_original_instruction_fold {source target : C}
    {word : RawEvent Party Good Port Technology Instrument} (actual : Trace source word target) :
    target.raw = word.foldl (Physical.Public.interpreter source.native.input).step source.raw := by
  induction actual with
  | nil => rfl
  | cons source request tail target ready review noConsents valid later inherited =>
      rw [afterNative_keeps_the_same_original_input source request,
        (two_actual_root_steps_pay_and_consume_the_generated_primitive source request ready review noConsents valid).2] at inherited
      exact inherited

omit [DecidableEq Port] in
theorem an_original_execution_has_the_same_literal_instruction_fold
    (law : RawLaw Party Good Port Technology Instrument) (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (word : RawEvent Party Good Port Technology Instrument) :
    (law.execute current index word).final = word.foldl law.step current := by
  induction word generalizing current index with
  | nil => rfl
  | cons request tail inherited => exact inherited (law.step current request) (index + 1)

theorem Trace.raw_is_the_complete_original_execution {source target : C}
    {word : RawEvent Party Good Port Technology Instrument} (actual : Trace source word target) (index : Nat) :
    target.raw = ((Physical.Public.interpreter source.native.input).execute source.raw index word).final :=
  actual.raw_is_the_original_instruction_fold.trans
    (an_original_execution_has_the_same_literal_instruction_fold _ _ _ _).symm

def claimThrough (source : C) (request : Request Party Good Port Technology Instrument) :
    source.native.frame.N.Claim → (afterNative source request).native.frame.N.Claim :=
  fun claim => Characterization.Escape.nextClaim (afterBody source request)
    (Characterization.Escape.nextClaim (queued source request) claim)

def rowThrough (source : C) (request : Request Party Good Port Technology Instrument)
    (row : OpenResponsibilityAt source.native.frame.N (source.native.frame.sourceSupport source.native.visit.current)) :
    OpenResponsibilityAt (afterNative source request).native.frame.N
      ((afterNative source request).native.frame.sourceSupport (afterNative source request).native.visit.current) :=
  Characterization.Escape.nextRow (afterBody source request)
    (Characterization.Escape.nextRow (queued source request) row)

theorem claimThrough_never_merges_original_claims (source : C)
    (request : Request Party Good Port Technology Instrument) : Function.Injective (claimThrough source request) :=
  (Characterization.Escape.nextClaim_does_not_merge_original_claims _).comp
    (Characterization.Escape.nextClaim_does_not_merge_original_claims _)

theorem rowThrough_keeps_the_same_original_claim_and_never_refills (source : C)
    (request : Request Party Good Port Technology Instrument)
    (row : OpenResponsibilityAt source.native.frame.N (source.native.frame.sourceSupport source.native.visit.current)) :
    (rowThrough source request row).claim = claimThrough source request row.claim ∧
      (rowThrough source request row).progressBudget ≤ row.progressBudget := by
  constructor
  · exact (Characterization.Escape.nextRow_keeps_the_same_source_claim _ _).trans
      (congrArg (Characterization.Escape.nextClaim (afterBody source request))
        (Characterization.Escape.nextRow_keeps_the_same_source_claim (queued source request) row))
  · exact (Characterization.Escape.nextRow_never_refills_an_original_residual _ _).trans
      (Characterization.Escape.nextRow_never_refills_an_original_residual (queued source request) row)

theorem Trace.carries_every_original_row_and_claim_without_refilling {source target : C}
    {word : RawEvent Party Good Port Technology Instrument} (actual : Trace source word target) :
    ∃ claimMap : source.native.frame.N.Claim → target.native.frame.N.Claim,
      ∃ carry : OpenResponsibilityAt source.native.frame.N (source.native.frame.sourceSupport source.native.visit.current) →
        OpenResponsibilityAt target.native.frame.N (target.native.frame.sourceSupport target.native.visit.current),
      Function.Injective claimMap ∧ ∀ row, (carry row).claim = claimMap row.claim ∧
        (carry row).progressBudget ≤ row.progressBudget := by
  induction actual with
  | nil source => exact ⟨id,id,fun _ _ same => same,fun _ => ⟨rfl,le_refl _⟩⟩
  | cons source request tail target ready review noConsents valid later inherited =>
      obtain ⟨claimMap,carry,injective,commutes⟩ := inherited
      refine ⟨claimMap ∘ claimThrough source request,carry ∘ rowThrough source request,
        injective.comp (claimThrough_never_merges_original_claims source request),?_⟩
      intro row
      have first := rowThrough_keeps_the_same_original_claim_and_never_refills source request row
      have second := commutes (rowThrough source request row)
      exact ⟨second.1.trans (congrArg claimMap first.1),second.2.trans first.2⟩

theorem a_checked_original_word_forces_actual_root_completion
    (source : C) (word : RawEvent Party Good Port Technology Instrument) (index : Nat)
    (ready : Ready source) (review : ReviewAvailable source)
    (noConsents : ∀ request ∈ word, request.consents = [])
    (valid : ∀ item ∈ ((Physical.Public.interpreter source.native.input).execute source.raw index word).items,
      (Physical.Public.interpreter source.native.input).Valid item.before item.request) :
    ∃ target actual, run source word = .completed target actual := by
  induction word generalizing source index with
  | nil => exact ⟨source,.nil source,rfl⟩
  | cons request tail inherited =>
      have headValid := valid ⟨index,source.raw,request⟩ List.mem_cons_self
      have headConsent := noConsents request List.mem_cons_self
      have paid := two_actual_root_steps_pay_and_consume_the_generated_primitive source request ready review headConsent headValid
      have afterReview := afterNative_keeps_the_available_review source request ready review headConsent headValid
      have laterValid : ∀ item ∈ ((Physical.Public.interpreter (afterNative source request).native.input).execute
          (afterNative source request).raw (index + 1) tail).items,
          (Physical.Public.interpreter (afterNative source request).native.input).Valid item.before item.request := by
        rw [afterNative_keeps_the_same_original_input source request,paid.2]
        exact fun item listed => valid item (List.mem_cons_of_mem _ listed)
      obtain ⟨target,actual,completed⟩ := inherited (afterNative source request) (index + 1) paid.1 afterReview
        (fun item listed => noConsents item (List.mem_cons_of_mem _ listed)) laterValid
      refine ⟨target,.cons source request tail target ready review headConsent headValid actual,?_⟩
      simp only [run,dif_pos ready,dif_pos review,dif_pos headConsent,dif_pos headValid,completed]

theorem Trace.every_original_instruction_has_its_actual_guards {source target : C}
    {word : RawEvent Party Good Port Technology Instrument} (actual : Trace source word target) (index : Nat) :
    ∀ item ∈ ((Physical.Public.interpreter source.native.input).execute source.raw index word).items,
      (Physical.Public.interpreter source.native.input).Valid item.before item.request ∧ item.request.consents = [] := by
  induction actual generalizing index with
  | nil source => simp only [RawLaw.execute,List.not_mem_nil,forall_false,implies_true]
  | cons source request tail target ready review noConsents valid later inherited =>
      have after := inherited (index + 1)
      rw [afterNative_keeps_the_same_original_input source request,
        (two_actual_root_steps_pay_and_consume_the_generated_primitive source request ready review noConsents valid).2] at after
      intro item inside
      rcases List.mem_cons.mp inside with original | remaining
      · subst item
        exact ⟨valid,noConsents⟩
      · exact after item remaining

theorem Trace.every_original_request_has_no_controller_consents {source target : C}
    {word : RawEvent Party Good Port Technology Instrument} (actual : Trace source word target) :
    ∀ request ∈ word, request.consents = [] := by
  induction actual with
  | nil source => exact fun _ impossible => (List.not_mem_nil impossible).elim
  | cons source request tail target ready review noConsents valid later inherited =>
      intro original inside
      rcases List.mem_cons.mp inside with same | remaining
      · exact same ▸ noConsents
      · exact inherited original remaining

theorem Trace.a_nonempty_execution_starts_at_the_actual_ready_boundary {source target : C}
    {word : RawEvent Party Good Port Technology Instrument} (actual : Trace source word target) (nonempty : word ≠ []) :
    Ready source ∧ ReviewAvailable source := by
  cases actual with
  | nil source => exact (nonempty rfl).elim
  | cons source request tail target ready review noConsents valid later => exact ⟨ready,review⟩

theorem actual_completion_iff_the_nonempty_original_word_passes_all_source_guards
    (source : C) (word : RawEvent Party Good Port Technology Instrument) (index : Nat) (nonempty : word ≠ []) :
    (∃ target actual, run source word = .completed target actual) ↔
      Ready source ∧ ReviewAvailable source ∧ (∀ request ∈ word, request.consents = []) ∧
        ∀ item ∈ ((Physical.Public.interpreter source.native.input).execute source.raw index word).items,
          (Physical.Public.interpreter source.native.input).Valid item.before item.request := by
  constructor
  · rintro ⟨target,actual,_computed⟩
    obtain ⟨ready,review⟩ := actual.a_nonempty_execution_starts_at_the_actual_ready_boundary nonempty
    exact ⟨ready,review,actual.every_original_request_has_no_controller_consents,
      fun item original => (actual.every_original_instruction_has_its_actual_guards index item original).1⟩
  · rintro ⟨ready,review,noConsents,valid⟩
    exact a_checked_original_word_forces_actual_root_completion source word index ready review noConsents valid

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
