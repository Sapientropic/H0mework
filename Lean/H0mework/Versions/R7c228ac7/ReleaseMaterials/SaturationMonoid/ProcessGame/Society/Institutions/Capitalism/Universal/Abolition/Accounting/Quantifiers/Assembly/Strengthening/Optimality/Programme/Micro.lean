import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Material

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem primitive_result_keeps_the_actual_clock (request : Request Party Good Port Technology Instrument)
    (result : Physical.Public.ResultAt input before (.primitive request)) :
    result.next.raw.clock = before.raw.clock := by
  cases result with
  | accepted word selected checked =>
      exact (Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.a_whole_instruction_word_preserves_the_clock_until_the_period_boundary
        (Physical.Public.interpreter input) before.raw 0 word).1
  | refused => rfl
  | metadata => rfl

theorem every_primitive_item_is_its_original_actual_request
    (request : Request Party Good Port Technology Instrument)
    (result : Physical.Public.ResultAt input before (.primitive request))
    (item : ExecutionItem Party Good Port Technology Instrument) (listed : item ∈ result.execution.items) :
    item.request = request.resign request.signer := by
  cases result with
  | accepted word selected checked =>
      have sourceWord : word = [request.resign request.signer] := (Option.some.inj selected).symm
      cases sourceWord
      simp only [Physical.Public.ResultAt.execution,RawLaw.execute,List.mem_cons,List.not_mem_nil,or_false] at listed
      cases listed
      rfl
  | refused => cases listed
  | metadata => cases listed

theorem every_microprogramme_item_retains_its_source_instruction
    (word : RawEvent Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (listed : item ∈ items input before (word.map Compile.RawInput.primitive)) :
    ∃ request ∈ word, item.request = request.resign request.signer := by
  induction word generalizing before with
  | nil => cases listed
  | cons request tail prior =>
      rcases List.mem_append.mp listed with first | later
      · exact ⟨request,List.mem_cons_self,every_primitive_item_is_its_original_actual_request
          input before request (Physical.Public.compile input before (.primitive request)) item first⟩
      · obtain ⟨original,member,same⟩ := prior _ later
        exact ⟨original,List.mem_cons_of_mem _ member,same⟩

theorem pure_microsteps_keep_the_original_physical_clock
    (word : RawEvent Party Good Port Technology Instrument) :
    (run input before (word.map Compile.RawInput.primitive)).raw.clock = before.raw.clock := by
  induction word generalizing before with
  | nil => rfl
  | cons request tail prior =>
      exact (prior _).trans (primitive_result_keeps_the_actual_clock input before request (Physical.Public.compile input before (.primitive request)))

theorem pure_microsteps_have_zero_elapsed_cost
    (word : RawEvent Party Good Port Technology Instrument) :
    clockCost input before (word.map Compile.RawInput.primitive) = 0 := by
  unfold clockCost
  rw [pure_microsteps_keep_the_original_physical_clock]
  exact sub_self _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme
