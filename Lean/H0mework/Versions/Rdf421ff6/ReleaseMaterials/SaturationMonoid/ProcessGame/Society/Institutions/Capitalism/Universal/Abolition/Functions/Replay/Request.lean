import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Resigning

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay

open Source.Program

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

/-- The refusal's original signer and purpose remain visible, but its
replay cannot accidentally execute a formerly rejected operation. -/
def presentation (request : Request Party Good Port Technology Instrument) :
    Request Party Good Port Technology Instrument :=
  ⟨request.signer, [], request.purpose, [], .present⟩

def requestAt (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Request Party Good Port Technology Instrument :=
  if law.Valid current request then request.resign request.signer else presentation request

omit [DecidableEq Instrument] in
theorem an_accepted_original_request_can_be_replayed_without_consents
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (accepted : law.Valid current request) :
    (PublicFunction.physicalLaw law).Valid current (request.resign request.signer) := by
  refine ⟨⟨accepted.1.1, rfl⟩, ?_, accepted.2.2⟩
  intro port member
  exact Or.inl rfl

omit [DecidableEq Instrument] in
theorem the_original_refusal_presentation_is_lawful
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (PublicFunction.physicalLaw law).Valid current (presentation request) := by
  simp [RawLaw.Valid, presentation, PublicFunction.physicalLaw, RawLaw.operationAllowed,
    RawPolicy.eval, RawLaw.SignerMatches, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit,
    RawLaw.ClaimGuard, NonnegativeBundle]

omit [DecidableEq Instrument] in
theorem the_computed_request_is_lawful
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (PublicFunction.physicalLaw law).Valid current (requestAt law current request) := by
  unfold requestAt
  split
  · exact an_accepted_original_request_can_be_replayed_without_consents law current request ‹_›
  · exact the_original_refusal_presentation_is_lawful law current request

omit [DecidableEq Instrument] in
theorem the_computed_request_has_the_same_signer_and_no_consents
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (requestAt law current request).signer = request.signer ∧
    (requestAt law current request).consents = [] := by
  unfold requestAt
  split <;> exact ⟨rfl, rfl⟩

theorem the_computed_request_preserves_the_original_actual_step
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (PublicFunction.physicalLaw law).step current (requestAt law current request) =
      law.step current request := by
  by_cases accepted : law.Valid current request
  · have legal := an_accepted_original_request_can_be_replayed_without_consents law current request accepted
    simp only [requestAt, if_pos accepted, RawLaw.step, if_pos legal]
    rfl
  · simp only [requestAt, if_neg accepted]
    exact ((PublicFunction.physicalLaw law).presentation_preserves_material_and_claims current
      (presentation request) rfl).trans (law.rejected_preserves_current current request accepted).symm

omit [DecidableEq Instrument] in
theorem the_computed_request_preserves_both_original_gross_flows
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (PublicFunction.physicalLaw law).actualDebit current (requestAt law current request) = law.actualDebit current request ∧
    (PublicFunction.physicalLaw law).actualCredit current (requestAt law current request) = law.actualCredit current request := by
  have legal := the_computed_request_is_lawful law current request
  rw [RawLaw.actualDebit, if_pos legal, RawLaw.actualCredit, if_pos legal]
  by_cases accepted : law.Valid current request
  · simp only [requestAt, RawLaw.actualDebit, RawLaw.actualCredit, if_pos accepted]
    exact ⟨rfl, rfl⟩
  · simp only [requestAt, RawLaw.actualDebit, RawLaw.actualCredit, if_neg accepted]
    exact ⟨rfl, rfl⟩

theorem an_original_rejection_keeps_a_zero_effect_presentation
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument)
    (rejected : ¬ law.Valid current request) :
    (requestAt law current request).operation = .present ∧
    (requestAt law current request).gates = [] ∧
    (PublicFunction.physicalLaw law).step current (requestAt law current request) = current := by
  simp only [requestAt, if_neg rejected]
  exact ⟨rfl, rfl, (PublicFunction.physicalLaw law).presentation_preserves_material_and_claims current (presentation request) rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.the_computed_request_preserves_the_original_actual_step
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.the_computed_request_preserves_both_original_gross_flows
