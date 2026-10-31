import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Control

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive

open ResponsibilityLifecycle Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem the_actual_primitive_prefixes_retain_the_whole_original_word
    (history : List (Compile.RawInput Party Good Port Technology Instrument)) (index : Nat)
    (word : RawEvent Party Good Port Technology Instrument)
    (noConsents : ∀ request ∈ word, request.consents = [])
    (valid : ∀ item ∈ ((Physical.Public.interpreter input).execute (state input depth count history).raw index word).items,
      (Physical.Public.interpreter input).Valid item.before item.request) :
    (events input depth count history word).map (fun item => (item.instruction input depth count).request) = word ∧
    (∀ item ∈ events input depth count history word,
      (item.interpreter input depth count).Valid (item.instruction input depth count).before
        (item.instruction input depth count).request) ∧
    (state input depth count (history ++ submitted word)).raw =
      ((Physical.Public.interpreter input).execute (state input depth count history).raw index word).final := by
  induction word generalizing history index with
  | nil => exact ⟨rfl,fun _ listed => (List.not_mem_nil listed).elim,by simp only [submitted,List.map_nil,List.append_nil,RawLaw.execute]⟩
  | cons request tail ih =>
      have firstValid : (Physical.Public.interpreter input).Valid (state input depth count history).raw request :=
        valid ⟨index,(state input depth count history).raw,request⟩ List.mem_cons_self
      have first := one_checked_original_primitive_has_one_actual_material_step input
        (state input depth count history) request (noConsents request List.mem_cons_self) firstValid
      have advance : (state input depth count (history ++ [.primitive request])).raw =
          (Physical.Public.interpreter input).step (state input depth count history).raw request :=
        congrArg Actual.Current.raw ((the_source_history_extends_by_this_same_primitive input depth count history request).trans first.2.2)
      have tailValid : ∀ item ∈ ((Physical.Public.interpreter input).execute
          (state input depth count (history ++ [.primitive request])).raw (index + 1) tail).items,
          (Physical.Public.interpreter input).Valid item.before item.request := by
        rw [advance]
        intro item listed
        exact valid item (List.mem_cons_of_mem _ listed)
      have rest := ih (history ++ [.primitive request]) (index + 1)
        (fun next listed => noConsents next (List.mem_cons_of_mem _ listed)) tailValid
      have firstInventory := one_checked_source_primitive_generates_its_own_original_native_inventory
        input depth count history request (noConsents request List.mem_cons_self) firstValid
      have firstRequests : (oneItems input depth count history request).map
          (fun item => (item.instruction input depth count).request) = [request] := by
        have same := congrArg (List.map ExecutionItem.request) firstInventory
        simpa only [List.map_map,Function.comp_def,List.map_cons,List.map_nil] using same
      refine ⟨?_,?_,?_⟩
      · change ((oneItems input depth count history request ++ events input depth count (history ++ [.primitive request]) tail).map _) = _
        rw [List.map_append,firstRequests,rest.1]
        rfl
      · intro item listed
        rcases List.mem_append.mp listed with firstItem | later
        · exact every_item_of_this_checked_primitive_is_actual input depth count history request
            (noConsents request List.mem_cons_self) firstValid item firstItem
        · exact rest.2.1 item later
      · simpa only [submitted,List.map_cons,List.singleton_append,List.append_assoc,advance,RawLaw.execute] using rest.2.2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
