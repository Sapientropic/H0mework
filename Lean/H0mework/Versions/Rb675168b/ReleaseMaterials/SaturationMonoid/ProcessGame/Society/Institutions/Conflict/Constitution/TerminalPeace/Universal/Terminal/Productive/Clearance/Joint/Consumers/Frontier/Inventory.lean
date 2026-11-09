import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Consumers.Settlement
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Compiler

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.OriginalExchange

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Quantities.Execution
open Quantities (Pending)
open Conflict.Consumers.Evolving (C R destroy levy)

noncomputable section

private theorem birth_pending : Pending (endAt Original.seed start) := by
  have trace := Conflict.Root.trace_after_prefix Original.seed _ [destroy] [levy] Original.actual_trace
  have original := trace.a_nonempty_execution_starts_at_the_actual_ready_boundary (by simp)
  have signed := trace.every_original_instruction_has_its_actual_guards 0
    ⟨0, Original.before.raw, levy⟩ List.mem_cons_self
  change Pending (endAt Original.seed (Original.prior ++ [Original.attack]))
  rw [endAt_append]
  exact the_actual_body_must_consume_its_original_native_head Original.before levy
    original.1 original.2 signed.2 signed.1

theorem original_drain_exact : openingDrain loss = [none] := by
  let source := endAt Original.seed start
  have last : next source none = Original.cut :=
    (endAt_append Original.seed start [none]).symm.trans at_original
  have dry : remainingNative (next source none) = 0 := by
    rw [last]
    exact Nat.eq_zero_of_not_pos (fun present =>
      Original.ready ((pending_iff_positive_original_positions _).mpr present))
  have spent := a_native_payment_spends_one_original_position source birth_pending
  rw [dry] at spent
  change nativePayments (remainingNative source) = [none]
  rw [← spent]
  rfl

private theorem birth_raw : prefixRaw loss [] = Original.snapshot 111 113 := by
  have same := (the_first_exhausted_native_cut_is_the_original_paid_drain
    (endAt Original.seed start)).2.1
  change (endAt (endAt Original.seed start) (openingDrain loss)).raw = _ at same
  rw [original_drain_exact, ← endAt_append, at_original, Original.cut_raw] at same
  exact same.symm

private theorem physical_singleton {source target : C} {request : R}
    (trace : Trace source [request] target) :
    (next source (some (.primitive request))).raw =
      (Boundary.Actual.materialLaw source).step source.raw request ∧
    (Boundary.Actual.materialLaw source).step source.raw request = target.raw := by
  cases trace with
  | cons source request _ _ ready review clean legal later =>
    cases later
    exact ⟨(the_selected_primitive_is_paid_by_the_original_root
      (queued source request) request ready
      (the_available_review_forwards_the_actual_requested_primitive _ _ review) clean legal).1,
      (two_actual_root_steps_pay_and_consume_the_generated_primitive source request ready review clean legal).2.symm⟩

private theorem body_same_stock (front : Original.Word) (request : R)
    {target : C} (trace : Trace (endAt Original.seed (start ++ front)) [request] target) :
    prefixRaw loss (front ++ [some (.primitive request)]) = target.raw := by
  have aligned : start ++ (front ++ [some (.primitive request)]) =
      (start ++ front) ++ [some (.primitive request)] := (List.append_assoc _ _ _).symm
  have exactCut := congrArg (endAt Original.seed) aligned
  exact (congrArg (fun cut : C => cut.raw) (exactCut.trans (endAt_append _ _ _))).trans
    ((physical_singleton trace).1.trans (physical_singleton trace).2)

private theorem grow_body_cut :
    endAt Original.seed (start ++ [none, production]) = next Original.cut production :=
  (congrArg (endAt Original.seed) (List.append_assoc start [none] [production]).symm).trans
    ((endAt_append Original.seed (start ++ [none]) [production]).trans
      (congrArg (fun cut => next cut production) at_original))

private theorem growth_trace :
    Trace (endAt Original.seed (start ++ [none])) [grow] (endAt Original.seed (start ++ beforeSale)) := by
  obtain ⟨write, _⟩ := first_production_is_written true
  have adjusted : start ++ beforeSale = (start ++ [none]) ++ primitiveScript [grow] :=
    (List.append_assoc start [none] (primitiveScript [grow])).symm
  rw [adjusted, endAt_append]
  exact write.trace

private theorem trace_after_delivery {front : Original.Word} {key : Reparation.Key Bool Bool} {q : ℚ}
    (delivery : DeliveryAt Original.seed Original.community replies (start ++ front) false key q) :
    Trace (endAt Original.seed (start ++ front)) [paymentRequest false key q]
      (endAt Original.seed (start ++ (front ++ installment false key q))) :=
  congrArg (endAt Original.seed) (List.append_assoc start front (installment false key q)) ▸ delivery.trace

private theorem body_keeps_delivery {front : Original.Word} {key : Reparation.Key Bool Bool} {q : ℚ}
    (delivery : DeliveryAt Original.seed Original.community replies (start ++ front) false key q) :
    prefixRaw loss (front ++ [payment false key q]) =
      prefixRaw loss (front ++ installment false key q) :=
  body_same_stock front (paymentRequest false key q) (trace_after_delivery delivery)

set_option maxHeartbeats 450000 in
private theorem all_openings_keep_reserve (n : Nat) (inside : n ≤ closed.length)
    (person good : Bool) :
    reserve person good ≤ (prefixRaw loss (closed.take n)).stock person good := by
  have width : n ≤ 9 := inside
  interval_cases n
  · rw [show closed.take 0 = ([] : Original.Word) from rfl]
    change reserve person good ≤ (prefixRaw loss []).stock person good
    rw [birth_raw]
    cases person <;> cases good <;> decide +kernel
  · rw [show closed.take 1 = ([none] : Original.Word) from rfl]
    change reserve person good ≤ (endAt Original.seed (start ++ [none])).raw.stock person good
    rw [at_original, Original.cut_raw]
    cases person <;> cases good <;> decide +kernel
  · rw [show closed.take 2 = ([none] ++ [some (.primitive grow)] : Original.Word) from rfl]
    have exactStock := body_same_stock [none] grow (target := endAt Original.seed (start ++ beforeSale)) growth_trace
    rw [exactStock]
    change reserve person good ≤ (prefixRaw loss beforeSale).stock person good
    rw [first_production_raw]
    cases person <;> cases good <;> decide +kernel
  · rw [show closed.take 3 = beforeSale from rfl]
    change reserve person good ≤ (prefixRaw loss beforeSale).stock person good
    rw [first_production_raw]
    cases person <;> cases good <;> decide +kernel
  · rw [show closed.take 4 = (beforeSale ++ [payment false food (1 / 2)]) from rfl]
    change reserve person good ≤ (prefixRaw loss (beforeSale ++ [payment false food (1 / 2)])).stock person good
    rw [body_keeps_delivery sale]
    change reserve person good ≤ (prefixRaw loss beforeDelivery).stock person good
    rw [before_delivery_raw]
    cases person <;> cases good <;> decide +kernel
  · rw [show closed.take 5 = beforeDelivery from rfl]
    change reserve person good ≤ (prefixRaw loss beforeDelivery).stock person good
    rw [before_delivery_raw]
    cases person <;> cases good <;> decide +kernel
  · rw [show closed.take 6 = (beforeDelivery ++ [payment false supply 6]) from rfl]
    change reserve person good ≤ (prefixRaw loss (beforeDelivery ++ [payment false supply 6])).stock person good
    rw [body_keeps_delivery purchase]
    change reserve person good ≤ (prefixRaw loss beforePayment).stock person good
    rw [before_payment_raw]
    cases person <;> cases good <;> decide +kernel
  · rw [show closed.take 7 = beforePayment from rfl]
    change reserve person good ≤ (prefixRaw loss beforePayment).stock person good
    rw [before_payment_raw]
    cases person <;> cases good <;> decide +kernel
  · rw [show closed.take 8 = (beforePayment ++ [payment false claim 6]) from rfl]
    change reserve person good ≤ (prefixRaw loss (beforePayment ++ [payment false claim 6])).stock person good
    rw [body_keeps_delivery paid.delivery]
    exact payment_preserves_the_production_floor person good
  · rw [show closed.take 9 = closed from rfl]
    exact payment_preserves_the_production_floor person good

private theorem singleton_item_floors {source target : C} {request : R}
    (trace : Trace source [request] target)
    (items : Boundary.Actual.items source (some (.primitive request)) = [⟨0, source.raw, request⟩])
    (item : Original.Item) (present : item ∈ Boundary.Actual.items source (some (.primitive request)))
    (person good : Bool)
    (before : reserve person good ≤ source.raw.stock person good)
    (after : reserve person good ≤ target.raw.stock person good) :
    reserve person good ≤ item.before.stock person good ∧
    reserve person good ≤ ((Boundary.Actual.materialLaw source).step item.before item.request).stock person good := by
  rw [items] at present
  rcases List.mem_singleton.mp present with rfl
  refine ⟨before, ?_⟩
  change reserve person good ≤ ((Boundary.Actual.materialLaw source).step source.raw request).stock person good
  rw [(physical_singleton trace).2]
  exact after

set_option maxHeartbeats 450000 in
private theorem literal_leg (n : Nat) (within : n < closed.length) (item : Original.Item)
    (present : item ∈ Boundary.Actual.items (endAt Original.seed (start ++ closed.take n)) closed[n])
    (person good : Bool) :
    reserve person good ≤ item.before.stock person good ∧
    reserve person good ≤ ((Boundary.Actual.materialLaw (endAt Original.seed (start ++ closed.take n))).step
      item.before item.request).stock person good := by
  have width : n ≤ 8 := by exact Nat.le_of_lt_succ within
  have safe (j : Nat) (h : j ≤ closed.length) := all_openings_keep_reserve j h person good
  interval_cases n
  · rw [show closed.take 0 = ([] : Original.Word) from rfl,
      show closed[0] = none from rfl] at present
    rw [show closed.take 0 = ([] : Original.Word) from rfl]
    exact (List.not_mem_nil ((Original.levy_native_has_no_second_item) ▸ present)).elim
  · rw [show closed.take 1 = ([none] : Original.Word) from rfl,
      show closed[1] = production from rfl] at present
    rw [show closed.take 1 = ([none] : Original.Word) from rfl]
    have items : Boundary.Actual.items (endAt Original.seed (start ++ [none])) production =
        [⟨0, (endAt Original.seed (start ++ [none])).raw, grow⟩] := by
      rw [at_original, grow_item]
    exact singleton_item_floors growth_trace items item present person good
      (safe 1 (by decide)) (safe 3 (by decide))
  · rw [show closed.take 2 = ([none, production] : Original.Word) from rfl,
      show closed[2] = none from rfl] at present
    rw [grow_body_cut, grow_accounting] at present
    exact (List.not_mem_nil present).elim
  · rw [show closed.take 3 = beforeSale from rfl,
      show closed[3] = payment false food (1 / 2) from rfl] at present
    rw [show closed.take 3 = beforeSale from rfl]
    exact singleton_item_floors (trace_after_delivery sale) sale.items item present person good
      (safe 3 (by decide)) (safe 5 (by decide))
  · rw [show closed.take 4 = (beforeSale ++ [payment false food (1 / 2)]) from rfl,
      show closed[4] = none from rfl] at present
    rw [← List.append_assoc start beforeSale [payment false food (1 / 2)], sale.accounting_empty] at present
    exact (List.not_mem_nil present).elim
  · rw [show closed.take 5 = beforeDelivery from rfl,
      show closed[5] = payment false supply 6 from rfl] at present
    rw [show closed.take 5 = beforeDelivery from rfl]
    exact singleton_item_floors (trace_after_delivery purchase) purchase.items item present person good
      (safe 5 (by decide)) (safe 7 (by decide))
  · rw [show closed.take 6 = (beforeDelivery ++ [payment false supply 6]) from rfl,
      show closed[6] = none from rfl] at present
    rw [← List.append_assoc start beforeDelivery [payment false supply 6], purchase.accounting_empty] at present
    exact (List.not_mem_nil present).elim
  · rw [show closed.take 7 = beforePayment from rfl,
      show closed[7] = payment false claim 6 from rfl] at present
    rw [show closed.take 7 = beforePayment from rfl]
    exact singleton_item_floors (trace_after_delivery paid.delivery) paid.delivery.items item present person good
      (safe 7 (by decide)) (safe 9 (by decide))
  · rw [show closed.take 8 = (beforePayment ++ [payment false claim 6]) from rfl,
      show closed[8] = none from rfl] at present
    rw [← List.append_assoc start beforePayment [payment false claim 6], paid.delivery.accounting_empty] at present
    exact (List.not_mem_nil present).elim

/-- Both sides of each original material item are safe. The first prefix
has no debtor surplus and the two exchange legs preserve the production floor. -/
theorem every_original_material_position_keeps_the_reserve :
    ProtectedThrough loss reserve closed := by
  intro cut listed person good
  obtain ⟨n, within, h⟩ := List.mem_flatMap.mp listed
  have opening : n ≤ closed.length := Nat.le_of_lt_succ (List.mem_range.mp within)
  rcases List.mem_cons.mp h with same | later
  · subst cut
    exact all_openings_keep_reserve n opening person good
  · split at later
    · rename_i inside
      obtain ⟨item, original, exactRead⟩ := List.mem_flatMap.mp later
      rcases List.mem_cons.mp exactRead with same | last
      · subst cut
        exact (literal_leg n inside item original person good).1
      · rw [List.mem_singleton] at last
        subst cut
        exact (literal_leg n inside item original person good).2
    · exact (List.not_mem_nil later).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.OriginalExchange
