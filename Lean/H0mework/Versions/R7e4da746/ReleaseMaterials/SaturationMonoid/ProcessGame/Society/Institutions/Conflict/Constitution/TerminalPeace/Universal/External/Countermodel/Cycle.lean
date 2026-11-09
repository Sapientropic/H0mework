import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Consumer

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving (C R compact levy returnAt)
open Quantities.Execution (endAt endAt_append endAt_input inventory inventory_append next primitiveScript)

noncomputable section

abbrev cycle : Original.Word := primitiveScript [levy, returnAt 6]
abbrev firstLeg : Original.Word := primitiveScript [levy]
abbrev lastLeg : Original.Word := primitiveScript [returnAt 6]
abbrev returned : Reparation.Actual.Input Bool Bool Bool Unit Unit := some (.primitive (returnAt 6))
abbrev middle (source : C) : C := endAt source firstLeg

/-- These are the actual conditions at the old compiler's recurrent cut.
The supply is returned by a second material action within each cycle. -/
structure CycleAt (source : C) : Prop where
  sameSource : source.native.input = compact
  physical : source.raw = Original.snapshot 117 107
  quiet : Ready source
  review : ReviewAvailable source

theorem actual_opening_cycle : CycleAt Settlement.settledCut :=
  ⟨Settlement.settled_source, Settlement.settled_raw, Settlement.settled_ready, Settlement.settled_review⟩

private theorem levy_is_native {source : C} (actual : CycleAt source) :
    source.native.input.law.Valid source.raw levy := by
  rw [actual.sameSource, actual.physical]
  decide +kernel

private theorem levy_is_physical {source : C} (actual : CycleAt source) :
    (Physical.Public.interpreter source.native.input).Valid source.raw levy :=
  PublicFunction.valid_physical _ _ _ (levy_is_native actual)

private theorem after_levy {source : C} (actual : CycleAt source) :
    Ready (middle source) ∧
      (middle source).raw = (Physical.Public.interpreter source.native.input).step source.raw levy :=
  two_actual_root_steps_pay_and_consume_the_generated_primitive source levy
    actual.quiet actual.review rfl (levy_is_physical actual)

theorem middle_source {source : C} (actual : CycleAt source) : (middle source).native.input = compact :=
  (endAt_input source firstLeg).trans actual.sameSource

theorem middle_raw {source : C} (actual : CycleAt source) :
    (middle source).raw = Original.snapshot 111 113 := by
  rw [(after_levy actual).2, actual.sameSource, actual.physical]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · rfl
  · decide +kernel
  · decide +kernel

private theorem middle_review {source : C} (actual : CycleAt source) : ReviewAvailable (middle source) :=
  afterNative_keeps_the_available_review source levy actual.quiet actual.review rfl (levy_is_physical actual)

private theorem return_is_native {source : C} (actual : CycleAt source) :
    (middle source).native.input.law.Valid (middle source).raw (returnAt 6) := by
  rw [middle_source actual, middle_raw actual]
  decide +kernel

private theorem return_is_physical {source : C} (actual : CycleAt source) :
    (Physical.Public.interpreter (middle source).native.input).Valid (middle source).raw (returnAt 6) :=
  PublicFunction.valid_physical _ _ _ (return_is_native actual)

private theorem after_return {source : C} (actual : CycleAt source) :
    Ready (endAt (middle source) lastLeg) ∧ (endAt (middle source) lastLeg).raw =
      (Physical.Public.interpreter (middle source).native.input).step (middle source).raw (returnAt 6) :=
  two_actual_root_steps_pay_and_consume_the_generated_primitive (middle source) (returnAt 6)
    (after_levy actual).1 (middle_review actual) rfl (return_is_physical actual)

theorem the_real_cycle_restores_its_original_material_state {source : C} (actual : CycleAt source) :
    CycleAt (endAt source cycle) := by
  change CycleAt (endAt source (firstLeg ++ lastLeg))
  rw [endAt_append]
  refine ⟨(endAt_input (middle source) lastLeg).trans (middle_source actual), ?_, (after_return actual).1,
    afterNative_keeps_the_available_review (middle source) (returnAt 6) (after_levy actual).1
      (middle_review actual) rfl (return_is_physical actual)⟩
  rw [(after_return actual).2, middle_source actual, middle_raw actual]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · rfl
  · decide +kernel
  · decide +kernel

private theorem primitive_items (source : C) (request : R) (quiet : Ready source)
    (review : ReviewAvailable source) (noConsent : request.consents = [])
    (paid : (Physical.Public.interpreter source.native.input).Valid source.raw request) :
    Boundary.Actual.items source (some (.primitive request)) = [⟨0, source.raw, request⟩] :=
  (Quantities.Execution.the_selected_primitive_is_paid_by_the_original_root
    (queued source request) request quiet
    (the_available_review_forwards_the_actual_requested_primitive source request review) noConsent paid).2.2

private theorem primitive_native_items (source : C) (request : R) (quiet : Ready source)
    (review : ReviewAvailable source) (noConsent : request.consents = [])
    (paid : (Physical.Public.interpreter source.native.input).Valid source.raw request) :
    Boundary.Actual.items (next source (some (.primitive request))) none = [] :=
  Reparation.Transport.native_step_has_no_material_items none
    (the_actual_body_must_consume_its_original_native_head source request quiet review noConsent paid)

theorem original_levy_items {source : C} (actual : CycleAt source) :
    Boundary.Actual.items source Original.attack = [⟨0, source.raw, levy⟩] :=
  primitive_items source levy actual.quiet actual.review rfl (levy_is_physical actual)

theorem original_levy_drain {source : C} (actual : CycleAt source) :
    Boundary.Actual.items (next source Original.attack) none = [] :=
  primitive_native_items source levy actual.quiet actual.review rfl (levy_is_physical actual)

theorem original_return_items {source : C} (actual : CycleAt source) :
    Boundary.Actual.items (middle source) returned = [⟨0, (middle source).raw, returnAt 6⟩] :=
  primitive_items (middle source) (returnAt 6) (after_levy actual).1
    (middle_review actual) rfl (return_is_physical actual)

theorem original_return_drain {source : C} (actual : CycleAt source) :
    Boundary.Actual.items (next (middle source) returned) none = [] :=
  primitive_native_items (middle source) (returnAt 6) (after_levy actual).1
    (middle_review actual) rfl (return_is_physical actual)

private theorem primitive_authority (source : C) (request : R)
    (law : source.native.input.law.Valid source.raw request)
    (items : Boundary.Actual.items source (some (.primitive request)) = [⟨0, source.raw, request⟩])
    (drain : Boundary.Actual.items (next source (some (.primitive request))) none = []) :
    Reparation.Actual.SourceAuthority source (primitiveScript [request]) := by
  intro item present
  change item ∈ inventory source ([some (.primitive request)] ++ [none]) at present
  rw [inventory_append] at present
  change item ∈ Boundary.Actual.items source (some (.primitive request)) ++
    Boundary.Actual.items (next source (some (.primitive request))) none at present
  rw [items, drain, List.append_nil] at present
  rw [List.mem_singleton.mp present]
  exact law

theorem the_original_law_admits_both_material_legs {source : C} (actual : CycleAt source) :
    Reparation.Actual.SourceAuthority source cycle := by
  have attack := primitive_authority source levy (levy_is_native actual)
    (original_levy_items actual) (original_levy_drain actual)
  have returned := primitive_authority (middle source) (returnAt 6) (return_is_native actual)
    (original_return_items actual) (original_return_drain actual)
  intro item present
  change item ∈ inventory source (firstLeg ++ lastLeg) at present
  rw [inventory_append] at present
  rcases List.mem_append.mp present with first | second
  · exact attack item first
  · have legal := returned item second
    rw [middle_source actual, ← actual.sameSource] at legal
    exact legal

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel
