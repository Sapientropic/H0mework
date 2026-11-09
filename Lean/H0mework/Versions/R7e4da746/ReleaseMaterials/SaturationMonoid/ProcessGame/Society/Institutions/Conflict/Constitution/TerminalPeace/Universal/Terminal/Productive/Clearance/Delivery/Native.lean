import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Menu.Eligibility
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Offer
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Admission
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.SelectedPrimitive

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable Trace queued
  the_available_review_forwards_the_actual_requested_primitive the_actual_body_must_consume_its_original_native_head)
open Quantities.Execution
open Reparation (Key)
open Reparation.Actual (ReceiptAnswers)
open Reparation.Actual.Allocation (Position)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "Cut" => Conflict.Root.Cut Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Address" => Key Party Good

def paymentRequest (purpose : Port) (key : Key Party Good) (quantity : ℚ) :
    Request Party Good Port Technology Instrument :=
  ⟨key.2.1, [], purpose, [], .transfer key.2.1 key.1 [(key.2.2, quantity)]⟩

abbrev payment (purpose : Port) (key : Key Party Good) (quantity : ℚ) :
    Reparation.Actual.Input Party Good Port Technology Instrument :=
  some (.primitive (paymentRequest purpose key quantity))

abbrev installment (purpose : Port) (key : Key Party Good) (quantity : ℚ) :
    Reparation.Actual.Script Party Good Port Technology Instrument :=
  [payment purpose key quantity, none]

/-- The original policy and stock port decide authorization. The payment
proposal cannot answer either of the two personal lanes. -/
structure IndependentReceiptChannel (seed : Cut) (answers : ReceiptAnswers seed)
    (past : Word) (purpose : Port) (key : Address) (quantity : ℚ) : Prop where
  distinct : key.1 ≠ key.2.1
  policy : (endAt seed past).native.input.law.operationAllowed (endAt seed past).raw
    (paymentRequest purpose key quantity) = true
  port : (endAt seed past).native.input.law.allowed (endAt seed past).raw.technology
    ((endAt seed past).native.input.law.stockPort (endAt seed past).raw.technology key.2.1 key.2.2) key.2.1 = true
  payer : ∀ position : Position seed past (payment purpose key quantity),
    answers past (payment purpose key quantity) position key.2.1 = true
  victim : ∀ position : Position seed past (payment purpose key quantity),
    answers past (payment purpose key quantity) position key.1 = true

def deliveredRaw (raw : RawCurrent Party Good Technology Instrument) (key : Key Party Good) (quantity : ℚ) :
    RawCurrent Party Good Technology Instrument :=
  { raw with stock := fun person good => raw.stock person good -
    (if (person, good) = (key.2.1, key.2.2) then quantity else 0) +
    (if (person, good) = (key.1, key.2.2) then quantity else 0) }

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem singleton_delivery_flow (recipient : Party) (good : Good) (quantity : ℚ)
    (person : Party) (material : Good) :
    flowAt (locate recipient [(good, quantity)]) person material =
      (if (person, material) = (recipient, good) then quantity else 0) := by
  simp [flowAt, locate, amount, eq_comm]

variable {seed : Conflict.Root.Cut Party Good Port Technology Instrument}
  {answers : ReceiptAnswers seed}
  {past : Reparation.Actual.Script Party Good Port Technology Instrument}
  {purpose : Port} {key : Key Party Good} {quantity : ℚ}

local notation "Here" => (endAt seed past)
local notation "RequestAt" => (paymentRequest purpose key quantity : Request Party Good Port Technology Instrument)
local notation "PaidInput" => (payment purpose key quantity : Reparation.Actual.Input Party Good Port Technology Instrument)
local notation "PaidWord" => (installment purpose key quantity : Word)
local notation "NextCut" => (endAt seed (past ++ PaidWord))

theorem delivery_has_original_authority (channel : IndependentReceiptChannel seed answers past purpose key quantity)
    (positive : 0 < quantity) (funded : quantity ≤ (Here).raw.stock key.2.1 key.2.2) :
    (Here).native.input.law.Valid (Here).raw RequestAt := by
  unfold RawLaw.Valid
  refine ⟨⟨trivial, channel.policy⟩, ?_, trivial, ?_, ?_, ?_⟩
  · intro port listed
    change port ∈ [(Here).native.input.law.stockPort (Here).raw.technology key.2.1 key.2.2] at listed
    rw [List.mem_singleton.mp listed]
    exact Or.inl channel.port
  · intro entry listed
    change entry ∈ [((key.2.1, key.2.2), quantity)] at listed
    rw [List.mem_singleton.mp listed]
    exact positive.le
  · intro entry listed
    change entry ∈ [((key.1, key.2.2), quantity)] at listed
    rw [List.mem_singleton.mp listed]
    exact positive.le
  · intro entry listed
    change entry ∈ [((key.2.1, key.2.2), quantity)] at listed
    rw [List.mem_singleton.mp listed]
    change flowAt (locate key.2.1 [(key.2.2, quantity)]) key.2.1 key.2.2 ≤ _
    rwa [singleton_delivery_flow, if_pos rfl]

variable (ready : Ready (endAt seed past)) (review : ReviewAvailable (endAt seed past))
  (legal : (endAt seed past).native.input.law.Valid (endAt seed past).raw (paymentRequest purpose key quantity))

include legal in
private theorem physical_authority :
    (Physical.Public.interpreter (Here).native.input).Valid (Here).raw RequestAt :=
  PublicFunction.valid_physical (Here).native.input.law (Here).raw _ legal

include ready review legal

theorem the_delivery_writes_one_original_item :
    Boundary.Actual.items (Here) PaidInput = [⟨0, (Here).raw, RequestAt⟩] :=
  (the_selected_primitive_is_paid_by_the_original_root
    (queued (Here) RequestAt) RequestAt ready
    (the_available_review_forwards_the_actual_requested_primitive _ _ review) rfl
    (physical_authority legal)).2.2

theorem the_delivery_accounting_writes_no_material :
    Boundary.Actual.items (endAt seed (past ++ [PaidInput])) none = [] := by
  have work := the_actual_body_must_consume_its_original_native_head (Here) RequestAt
    ready review rfl (physical_authority legal)
  rw [endAt_append]
  exact Reparation.Transport.native_step_has_no_material_items none work

theorem the_delivery_consumes_its_original_native_head :
    Trace (Here) [RequestAt] (NextCut) ∧
      Ready (NextCut) ∧ ReviewAvailable (NextCut) := by
  rw [endAt_append]
  apply pay_checked_primitives (Here) [RequestAt] 0 ready review
  · intro request listed
    rw [List.mem_singleton.mp listed]
    rfl
  · intro item listed
    change item ∈ [⟨0, (Here).raw, RequestAt⟩] at listed
    rw [List.mem_singleton.mp listed]
    exact physical_authority legal

theorem the_delivery_reads_its_exact_original_successor :
    (NextCut).raw = deliveredRaw (Here).raw key quantity := by
  have paid := (the_delivery_consumes_its_original_native_head ready review legal).1
  rw [paid.raw_is_the_complete_original_execution 0]
  change (Physical.Public.interpreter (Here).native.input).step (Here).raw RequestAt = _
  rw [RawLaw.step, if_pos (physical_authority legal)]
  apply RawCurrent.ext
  · funext person good
    change (Here).raw.stock person good -
      flowAt (locate key.2.1 [(key.2.2, quantity)]) person good +
      flowAt (locate key.1 [(key.2.2, quantity)]) person good = _
    rw [singleton_delivery_flow, singleton_delivery_flow]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance
