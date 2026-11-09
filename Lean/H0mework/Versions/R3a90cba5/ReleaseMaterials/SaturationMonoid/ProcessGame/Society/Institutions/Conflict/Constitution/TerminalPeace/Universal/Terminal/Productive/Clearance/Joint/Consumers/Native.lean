import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Production
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.OriginalExchange

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Quantities.Execution
open Conflict.Consumers.Evolving (C R compact sourceInput)
open Reparation.Actual
open Reparation.Actual.Allocation (Position originalItem)
open private keysAt original_key from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence

noncomputable section

abbrev loss := Original.occurrence
abbrev claim : Reparation.Key Bool Bool := (false, true, false)
abbrev food : Reparation.Key Bool Bool := (false, true, true)
abbrev supply : Reparation.Key Bool Bool := (true, false, false)

abbrev grow : R := ⟨true, [], false, [], .produce false⟩
abbrev production : Input Bool Bool Bool Unit Unit := some (.primitive grow)

def personalReplies (victimSigns : Bool) : ReceiptAnswers Original.seed := fun past input site who =>
  match (originalItem Original.seed past input site).request.operation with
  | .produce false => who
  | .transfer true false [(true, q)] => decide (q = 1 / 2)
  | .transfer false true [(false, q)] => decide (q = 6)
  | .transfer true false [(false, q)] => decide (q = 6) && (who || victimSigns)
  | _ => false

abbrev replies := personalReplies true

def beforeSale : Original.Word := [none, production, none]
def beforeDelivery : Original.Word := beforeSale ++ installment false food (1 / 2)
def beforePayment : Original.Word := beforeDelivery ++ installment false supply 6
def closed : Original.Word := beforePayment ++ installment false claim 6

abbrev start : Original.Word := Occurrence.history loss

def reserve (person good : Bool) : ℚ :=
  if good then if person then 1 / 2 else 1
  else if person then 113 else 111

theorem at_original : endAt Original.seed (start ++ [none]) = Original.cut :=
  congrArg (endAt Original.seed) Original.exact_history.symm

private theorem compact_at (past : Original.Word) : (endAt Original.seed past).native.input = compact :=
  (endAt_input _ _).trans sourceInput

private theorem grow_valid : compact.law.Valid (Original.snapshot 111 113) grow := by decide +kernel

private theorem grow_legal : Original.cut.native.input.law.Valid Original.cut.raw grow := by
  rw [Original.same_source, Original.cut_raw]
  exact grow_valid

private theorem grow_physical :
    (Physical.Public.interpreter Original.cut.native.input).Valid Original.cut.raw grow :=
  PublicFunction.valid_physical _ _ _ grow_legal

theorem grow_item : Boundary.Actual.items Original.cut production = [⟨0, Original.cut.raw, grow⟩] :=
  (the_selected_primitive_is_paid_by_the_original_root
    (queued Original.cut grow) grow Original.ready
    (the_available_review_forwards_the_actual_requested_primitive _ _ Original.review) rfl grow_physical).2.2

private theorem grow_no_debit :
    (Boundary.Actual.materialLaw Original.cut).actualDebit Original.cut.raw grow = [] := by
  change (Physical.Public.interpreter Original.cut.native.input).actualDebit Original.cut.raw grow = []
  rw [RawLaw.actualDebit, if_pos grow_physical, Original.same_source]
  rfl

private theorem grow_no_damage : Boundary.Actual.damages Original.cut production Original.community = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro damage _
  have literal := damage.source_item
  rw [grow_item] at literal
  have key := original_key damage
  unfold keysAt at key
  rw [List.mem_singleton.mp literal] at key
  rw [grow_no_debit] at key
  exact List.not_mem_nil key

theorem grow_accounting :
    Boundary.Actual.items (next Original.cut production) none = [] :=
  Reparation.Transport.native_step_has_no_material_items none
    (the_actual_body_must_consume_its_original_native_head Original.cut grow
      Original.ready Original.review rfl grow_physical)

private theorem grow_safe (accepts : Bool) :
    Occurrence.EligibleFrom Original.community (personalReplies accepts) start (start ++ [none]) [production, none] := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, trivial⟩
  · intro item listed
    change item ∈ Boundary.Actual.items (endAt Original.seed (start ++ [none])) production at listed
    rw [at_original, grow_item] at listed
    obtain rfl := List.mem_singleton.mp listed
    rw [at_original]
    exact grow_legal
  · intro site question asked _
    have original : originalItem Original.seed (start ++ [none]) production site =
        ⟨0, Original.cut.raw, grow⟩ := by
      have existsItem : originalItem Original.seed (start ++ [none]) production site ∈
          Boundary.Actual.items (endAt Original.seed (start ++ [none])) production :=
        List.getElem_mem site.isLt
      rw [at_original, grow_item] at existsItem
      exact List.mem_singleton.mp existsItem
    change question ∈ ExposureGuard.questions _ (originalItem _ _ _ site) at asked
    rw [original, at_original] at asked
    have literal : ExposureGuard.questions Original.cut ⟨0, Original.cut.raw, grow⟩ = [(true, .signature)] := by
      unfold ExposureGuard.questions ExposureGuard.materialQuestions ExposureGuard.financialQuestions
      change (true, ExposureGuard.Exposure.signature) ::
        (List.filterMap _ ((Boundary.Actual.materialLaw Original.cut).actualDebit Original.cut.raw grow) ++ []) = _
      rw [grow_no_debit]
      rfl
    rw [literal] at asked
    rw [List.mem_singleton.mp asked, personalReplies, original]
  · rw [at_original]
    exact grow_no_damage
  · apply ExposureGuard.no_material_is_admitted
    change Boundary.Actual.items (endAt Original.seed ((start ++ [none]) ++ [production])) none = []
    rw [endAt_append, at_original]
    exact grow_accounting
  · apply Boundary.Actual.no_material_write_has_no_damage
    rw [endAt_append, at_original]
    exact grow_accounting

theorem drain_safe (accepts : Bool) : Occurrence.Eligible (personalReplies accepts) loss [none] :=
  ⟨⟨ExposureGuard.no_material_is_admitted _ _ _ _ Original.levy_native_has_no_second_item,
    Boundary.Actual.no_material_write_has_no_damage _ _ _ Original.levy_native_has_no_second_item⟩, trivial⟩

theorem first_production_is_written (accepts : Bool) :
    ∃ write, inspectProduction (personalReplies accepts) loss [none] [grow] = .written write := by
  apply (inspectProduction_passes_iff _ _ _ _).mpr
  refine ⟨?_, ?_, grow_safe accepts⟩
  · unfold Conflict.Root.Authorized
    rw [at_original]
    intro item listed
    change item ∈ [⟨0, Original.cut.raw, grow⟩] at listed
    exact (List.mem_singleton.mp listed).symm ▸ grow_legal
  · unfold Conflict.Root.terminal
    rw [at_original]
    exact .cons Original.cut grow [] _ Original.ready Original.review rfl grow_physical (.nil _)

theorem first_production_is_safe (accepts : Bool) :
    Occurrence.Eligible (personalReplies accepts) loss beforeSale := by
  obtain ⟨write, _⟩ := first_production_is_written accepts
  exact write.eligibility (drain_safe accepts)

private theorem production_cut :
    endAt Original.seed (start ++ beforeSale) = afterNative Original.cut grow :=
  (congrArg (endAt Original.seed) (List.append_assoc start [none] [production, none]).symm).trans
    ((endAt_append Original.seed (start ++ [none]) [production, none]).trans
      (congrArg (fun cut => endAt cut [production, none]) at_original))

theorem first_production_raw : prefixRaw loss beforeSale = Original.snapshot 129 113 := by
  have original := two_actual_root_steps_pay_and_consume_the_generated_primitive Original.cut grow
    Original.ready Original.review rfl grow_physical
  change (endAt Original.seed (start ++ beforeSale)).raw = _
  rw [production_cut]
  rw [original.2, Original.same_source, Original.cut_raw]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext instrument payer victim
    cases instrument
    cases payer <;> cases victim <;> decide +kernel
  · rfl
  · decide +kernel
  · decide +kernel

theorem first_production_ready : ReadyEntry loss beforeSale := by
  change Ready (endAt Original.seed (start ++ beforeSale)) ∧
    ReviewAvailable (endAt Original.seed (start ++ beforeSale))
  rw [production_cut]
  exact ⟨(two_actual_root_steps_pay_and_consume_the_generated_primitive Original.cut grow
    Original.ready Original.review rfl grow_physical).1,
    afterNative_keeps_the_available_review Original.cut grow Original.ready Original.review rfl grow_physical⟩

private theorem transferChannel (front : Original.Word) (key : Reparation.Key Bool Bool) (q : ℚ)
    (gates : ReadyEntry loss front)
    (positive : 0 < q)
    (funded : q ≤ (prefixRaw loss front).stock key.2.1 key.2.2)
    (distinct : key.1 ≠ key.2.1)
    (port : compact.law.allowed (prefixRaw loss front).technology
      (compact.law.stockPort (prefixRaw loss front).technology key.2.1 key.2.2) key.2.1 = true)
    (policy : compact.law.operationAllowed (prefixRaw loss front) (paymentRequest false key q) = true)
    (signed : ∀ who : Bool, ∀ site : Position Original.seed (start ++ front) (payment false key q),
      originalItem Original.seed (start ++ front) (payment false key q) site =
        ⟨0, prefixRaw loss front, paymentRequest false key q⟩ →
      replies (start ++ front) (payment false key q) site who = true) :
    IndependentReceiptChannel Original.seed replies (start ++ front) false key q := by
  have stockPort :
      (endAt Original.seed (start ++ front)).native.input.law.allowed (prefixRaw loss front).technology
      ((endAt Original.seed (start ++ front)).native.input.law.stockPort
        (prefixRaw loss front).technology key.2.1 key.2.2) key.2.1 = true := by
    rw [compact_at]
    exact port
  have allowed : (endAt Original.seed (start ++ front)).native.input.law.operationAllowed
      (prefixRaw loss front) (paymentRequest false key q) = true := by
    rw [compact_at]
    exact policy
  have legal : (endAt Original.seed (start ++ front)).native.input.law.Valid
      (prefixRaw loss front) (paymentRequest false key q) := by
    unfold RawLaw.Valid
    refine ⟨⟨trivial, allowed⟩, ?_, trivial, ?_, ?_, ?_⟩
    · intro p listed
      change p ∈ [_] at listed
      rw [List.mem_singleton.mp listed]
      exact Or.inl stockPort
    · intro entry listed
      change entry ∈ [((key.2.1, key.2.2), q)] at listed
      rw [List.mem_singleton.mp listed]
      exact positive.le
    · intro entry listed
      change entry ∈ [((key.1, key.2.2), q)] at listed
      rw [List.mem_singleton.mp listed]
      exact positive.le
    · intro entry listed
      change entry ∈ [((key.2.1, key.2.2), q)] at listed
      rw [List.mem_singleton.mp listed]
      change flowAt (locate key.2.1 [(key.2.2, q)]) key.2.1 key.2.2 ≤ _
      rwa [singleton_delivery_flow, if_pos rfl]
  have items := the_delivery_writes_one_original_item gates.1 gates.2 legal
  have literal (site : Position Original.seed (start ++ front) (payment false key q)) :
      originalItem Original.seed (start ++ front) (payment false key q) site =
        ⟨0, prefixRaw loss front, paymentRequest false key q⟩ := by
    have listed : originalItem Original.seed (start ++ front) (payment false key q) site ∈
        Boundary.Actual.items (endAt Original.seed (start ++ front)) (payment false key q) := List.getElem_mem _
    rw [items] at listed
    exact List.mem_singleton.mp listed
  exact ⟨distinct, allowed, stockPort, fun site => signed key.2.1 site (literal site),
    fun site => signed key.1 site (literal site)⟩

private theorem gateAfter {front : Original.Word} {key : Reparation.Key Bool Bool} {q : ℚ}
    (delivery : DeliveryAt Original.seed Original.community replies (start ++ front) false key q) :
    ReadyEntry loss (front ++ installment false key q) := by
  unfold ReadyEntry
  rw [← List.append_assoc]
  exact ⟨delivery.ready, delivery.review⟩

theorem stockAfter {front : Original.Word} {key : Reparation.Key Bool Bool} {q : ℚ}
    (delivery : DeliveryAt Original.seed Original.community replies (start ++ front) false key q) :
    prefixRaw loss (front ++ installment false key q) = deliveredRaw (prefixRaw loss front) key q := by
  simpa only [prefixRaw, List.append_assoc] using delivery.raw

def sale : DeliveryAt Original.seed Original.community replies (start ++ beforeSale) false food (1 / 2) := by
  have gates := first_production_ready
  have positive : 0 < (1 / 2 : ℚ) := by norm_num
  have funded : 1 / 2 ≤ (prefixRaw loss beforeSale).stock true true := by
    rw [first_production_raw]
    decide +kernel
  exact executeDelivery gates.1 gates.2 positive funded
    (transferChannel beforeSale food (1 / 2) gates positive funded (by decide) rfl rfl
      (fun who site literal => by unfold replies personalReplies; rw [literal]; cases who <;> decide +kernel))

theorem before_delivery_raw :
    prefixRaw loss beforeDelivery = deliveredRaw (Original.snapshot 129 113) food (1 / 2) := by
  rw [beforeDelivery, stockAfter sale, first_production_raw]

def purchase : DeliveryAt Original.seed Original.community replies (start ++ beforeDelivery) false supply 6 := by
  have gates := gateAfter sale
  have positive : (0 : ℚ) < 6 := by norm_num
  have funded : 6 ≤ (prefixRaw loss beforeDelivery).stock false false := by
    rw [before_delivery_raw]
    decide +kernel
  exact executeDelivery gates.1 gates.2 positive funded
    (transferChannel beforeDelivery supply 6 gates positive funded (by decide) rfl rfl
      (fun who site literal => by unfold replies personalReplies; rw [literal]; cases who <;> decide +kernel))

theorem before_payment_raw :
    prefixRaw loss beforePayment = deliveredRaw
      (deliveredRaw (Original.snapshot 129 113) food (1 / 2)) supply 6 := by
  rw [beforePayment, stockAfter purchase, before_delivery_raw]

theorem before_payment_ready : ReadyEntry loss beforePayment := gateAfter purchase

theorem restitutionChannel :
    IndependentReceiptChannel Original.seed replies (start ++ beforePayment) false claim 6 :=
  transferChannel beforePayment claim 6 before_payment_ready (by norm_num)
    (by rw [before_payment_raw]; decide +kernel) (by decide) rfl rfl
    (fun who site literal => by unfold replies personalReplies; rw [literal]; cases who <;> decide +kernel)

theorem safeBeforePayment : Occurrence.Eligible replies loss beforePayment := by
  have afterFood := (eligible_append replies start).mpr
    ⟨first_production_is_safe true, sale.eligible start⟩
  exact (eligible_append replies start).mpr ⟨afterFood, purchase.eligible start⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.OriginalExchange
