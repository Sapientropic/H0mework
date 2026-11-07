import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Resigning
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

/-- Retains the original operation and signer, including a refused request;
only controller-consent syntax is removed under the public interpreter. -/
def normalise (word : RawEvent Party Good Port Technology Instrument) :=
  word.map (fun request => request.resign request.signer)

omit [DecidableEq Instrument] in
theorem public_validity_is_unchanged_by_normalising_one_request
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (PublicFunction.physicalLaw law).Valid current (request.resign request.signer) ↔
      (PublicFunction.physicalLaw law).Valid current request := by
  constructor <;> rintro ⟨signed,_ports,remaining⟩ <;> exact ⟨signed,fun _ _ => Or.inl rfl,remaining⟩

theorem public_step_keeps_the_original_request_effect
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (PublicFunction.physicalLaw law).step current (request.resign request.signer) =
      (PublicFunction.physicalLaw law).step current request := by
  by_cases accepted : (PublicFunction.physicalLaw law).Valid current request
  · exact (PublicFunction.physicalLaw law).accepted_resign_same_effect current request request.signer accepted
      ((public_validity_is_unchanged_by_normalising_one_request law current request).mpr accepted)
  · rw [(PublicFunction.physicalLaw law).rejected_preserves_current _ _ accepted,
      (PublicFunction.physicalLaw law).rejected_preserves_current _ _ (by
        intro changed
        exact accepted ((public_validity_is_unchanged_by_normalising_one_request law current request).mp changed))]

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem normalised_requests_have_no_controller_consents
    (word : RawEvent Party Good Port Technology Instrument) :
    ∀ request ∈ normalise word, request.consents = [] := by
  intro request present
  obtain ⟨original,_listed,same⟩ := List.mem_map.mp present
  cases same
  rfl

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem normalisation_keeps_every_original_operation
    (word : RawEvent Party Good Port Technology Instrument) :
    (normalise word).map Request.operation = word.map Request.operation := by
  simp only [normalise,List.map_map]
  rfl

theorem public_normalisation_keeps_the_complete_original_execution
    (current : RawCurrent Party Good Technology Instrument) (index : Nat)
    (word : RawEvent Party Good Port Technology Instrument) :
    ((PublicFunction.physicalLaw law).execute current index (normalise word)).final =
      ((PublicFunction.physicalLaw law).execute current index word).final := by
  induction word generalizing current index with
  | nil => rfl
  | cons request tail inherited =>
      simp only [normalise,List.map_cons,RawLaw.execute]
      rw [public_step_keeps_the_original_request_effect]
      exact inherited _ _

theorem public_normalisation_preserves_all_actual_request_guards
    (current : RawCurrent Party Good Technology Instrument) (index : Nat)
    (word : RawEvent Party Good Port Technology Instrument)
    (valid : ∀ item ∈ ((PublicFunction.physicalLaw law).execute current index word).items,
      (PublicFunction.physicalLaw law).Valid item.before item.request) :
    ∀ item ∈ ((PublicFunction.physicalLaw law).execute current index (normalise word)).items,
      (PublicFunction.physicalLaw law).Valid item.before item.request := by
  induction word generalizing current index with
  | nil => simp only [normalise,List.map_nil,RawLaw.execute,List.not_mem_nil,forall_false,implies_true]
  | cons request tail inherited =>
      simp only [normalise,List.map_cons,RawLaw.execute]
      rw [public_step_keeps_the_original_request_effect]
      intro item inside
      rcases List.mem_cons.mp inside with original | later
      · subst item
        exact (public_validity_is_unchanged_by_normalising_one_request law current request).mpr
          (valid ⟨index,current,request⟩ List.mem_cons_self)
      · exact inherited _ _ (fun source listed => valid source (List.mem_cons_of_mem _ listed)) item later

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
