import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement.Resources
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Result

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev PhysicalCurrent := Actual.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

omit [DecidableEq Port] in
theorem the_original_primitive_compiler_executes_the_same_raw_step
    (before : PhysicalCurrent (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (request : Request Party Good Port Technology Instrument)
    (same : request.resign request.signer = request) :
    (Physical.Public.compile input before (.primitive request)).next.raw =
      (Physical.Public.interpreter input).step before.raw request := by
  cases generated : Physical.Public.compile input before (.primitive request) with
  | accepted word selected checked =>
      have wordEq : word = [request] := by
        simpa only [Physical.Public.wordAt,same,Option.some.injEq] using selected.symm
      subst word
      change (Physical.Public.interpreter input).step before.raw request = _
      rfl
  | refused word selected item listed failed =>
      have wordEq : word = [request] := by
        simpa only [Physical.Public.wordAt,same,Option.some.injEq] using selected.symm
      subst word
      have itemEq : item = ⟨0,before.raw,request⟩ := by
        simpa only [RawLaw.rawItems,RawLaw.execute,List.mem_singleton] using listed
      subst item
      exact ((Physical.Public.interpreter input).rejected_preserves_current before.raw request failed).symm
  | metadata selected =>
      simp only [Physical.Public.wordAt,same] at selected
      cases selected

/-- This is the existing compiler fold of the submitted primitive inputs. -/
def primitiveNext (before : PhysicalCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
    (word : RawEvent Party Good Port Technology Instrument) :=
  (word.map Compile.RawInput.primitive).foldl
    (fun current submitted => (Physical.Public.compile input current submitted).next) before

omit [DecidableEq Port] in
theorem every_submitted_primitive_keeps_the_original_raw_execution
    (before : PhysicalCurrent (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (word : RawEvent Party Good Port Technology Instrument)
    (same : ∀ request ∈ word, request.resign request.signer = request) (index : Nat) :
    (primitiveNext input before word).raw =
      ((Physical.Public.interpreter input).execute before.raw index word).final := by
  induction word generalizing before index with
  | nil => rfl
  | cons request tail ih =>
      change (primitiveNext input (Physical.Public.compile input before (.primitive request)).next tail).raw = _
      rw [ih _ (fun next member => same next (List.mem_cons_of_mem _ member)) (index+1)]
      rw [the_original_primitive_compiler_executes_the_same_raw_step input before request (same request List.mem_cons_self)]
      rfl

omit [DecidableEq Port] in
theorem the_generated_price_uses_the_original_physical_compiler
    (before : PhysicalCurrent (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (payer provider : Party) (instrument : Instrument) (purpose : Port) (net : ℚ)
    (result : Result (Physical.Public.interpreter input) before.raw payer provider instrument purpose net) :
    (primitiveNext input before result.word).raw = result.next := by
  apply every_submitted_primitive_keeps_the_original_raw_execution input before result.word _ 0
  intro request member
  cases result with
  | noPayment zero => cases member
  | invalidRate nonzero failed => cases member
  | issueRefused nonzero rate failed =>
      have sameRequest : request = issue (Physical.Public.interpreter input) payer provider instrument purpose net :=
        List.mem_singleton.mp member
      subst request
      rfl
  | settlementRefused nonzero rate issued failed | paid nonzero rate issued settled =>
      simp only [Result.word,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with first | second <;> subst request <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement
