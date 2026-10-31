import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Reader
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.PositionState

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count boundary : Nat)
  (plan : RawEvent Party Good Port Technology Instrument) (fallback : Macro.Raw.Reader input depth count)

/-- Finite source-plan bookkeeping. The only live account belongs to position. -/
structure Schedule (remaining : RawEvent Party Good Port Technology Instrument) : Type 4 where
  position : Position input depth count (reader boundary plan fallback)
  front : RawEvent Party Good Port Technology Instrument
  split : plan = front ++ remaining
  location : position.past.length = boundary + front.length
  noConsents : ∀ request ∈ remaining, request.consents = []
  index : Nat
  valid : ∀ item ∈ ((Physical.Public.interpreter input).execute
      (Physical.Public.stateAt input depth count 0 0 [] position.past).raw index remaining).items,
    (Physical.Public.interpreter input).Valid item.before item.request

namespace Schedule
variable {input depth count boundary plan fallback}
variable {request : Request Party Good Port Technology Instrument} {tail : RawEvent Party Good Port Technology Instrument}
  (source : Schedule input depth count boundary plan fallback (request :: tail))

theorem selected : source.position.actual.proposal (reader boundary plan fallback) = .primitive request := by
  have listed : plan[source.front.length]? = some request := by
    exact (congrArg (fun word : RawEvent Party Good Port Technology Instrument => word[source.front.length]?) source.split).trans (by simp)
  exact each_actual_position_reads_its_original_primitive boundary plan fallback
    source.position.actual.readerCursor source.position.actual.actual.account source.front.length request source.location listed

theorem checked : (Physical.Public.interpreter input).Valid
    (Physical.Public.stateAt input depth count 0 0 [] source.position.past).raw request := by
  apply source.valid (⟨source.index,_,request⟩ : ExecutionItem Party Good Port Technology Instrument)
  exact List.mem_cons_self

def nextPosition := source.position.step request source.selected (source.noConsents request List.mem_cons_self) source.checked

def next : Schedule input depth count boundary plan fallback tail where
  position := source.nextPosition
  front := source.front ++ [request]
  split := source.split.trans (by simp only [List.append_assoc,List.singleton_append])
  location := by
    unfold nextPosition
    rw [Position.step_records_exactly_this_original_primitive]
    simp only [List.length_append,List.length_singleton]
    have before := source.location
    omega
  noConsents := fun item member => source.noConsents item (List.mem_cons_of_mem _ member)
  index := source.index + 1
  valid := by
    intro item member
    have material := Position.step_reads_the_same_actual_material_successor source.position request
      source.selected (source.noConsents request List.mem_cons_self) source.checked
    change item ∈ ((Physical.Public.interpreter input).execute
      (Physical.Public.stateAt input depth count 0 0 [] source.nextPosition.past).raw (source.index + 1) tail).items at member
    unfold nextPosition at member
    rw [material] at member
    apply source.valid item
    change item ∈ ⟨source.index,_,request⟩ :: _
    exact List.mem_cons_of_mem _ member

end Schedule
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing
