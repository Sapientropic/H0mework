import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentBirth

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentInventory
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (encoding : StageTransport.Encoding (code := code))

def scopes : Finset Scope :=
  ((List.finRange code.signals).filterMap fun signal => (encoding signal).map (fun ballot => ballot.scope)).toFinset

def directory : Finset (IncidentBirth.Tag (code := code)) :=
  Finset.univ.product (Finset.univ.product (scopes encoding))

def capacity := code.sites * (code.sites * code.signals)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem directory_has_the_original_finite_interface_capacity :
    (directory encoding).card ≤ capacity (code := code) := by
  have bounded : (scopes encoding).card ≤ code.signals :=
    (List.toFinset_card_le _).trans ((List.length_filterMap_le _ _).trans (by simp))
  change ((Finset.univ : Finset (Fin code.sites)) ×ˢ
    ((Finset.univ : Finset (Fin code.sites)) ×ˢ scopes encoding)).card ≤ _
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin, capacity]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ bounded)

variable (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (law : StageReception.Law code)

theorem every_actual_incident_has_an_authenticated_signal_scope
    (entry : StageAccountability.Incident start vocabulary encoding law) :
    IncidentBirth.tag start vocabulary encoding law entry ∈ directory encoding := by
  have facts := StageAccountability.query_sound _ entry.slot entry.pair entry.detected
  obtain ⟨sendIndex, sendRow, origin, deliveryRow, packet, sent, prior, owned, sendWord,
      actualDelivery, deliveryCut, earlier, packetAt, decoded, rest⟩ :=
    StageReception.receipt_has_actual_send_delivery_and_owned_ballot_origin vocabulary encoding law
      start entry.birthStages entry.receiver entry.birthStages.length entry.pair.1 facts.1
  have represented : entry.pair.1.wire.ballot.scope ∈ scopes encoding := by
    apply List.mem_toFinset.mpr
    apply List.mem_filterMap.mpr
    exact ⟨packet.signal, List.mem_finRange _, by rw [decoded]; rfl⟩
  rw [facts.2.2.2.1] at represented
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨Finset.mem_univ _, represented⟩⟩

theorem all_actual_incident_identities_have_a_source_generated_budget
    (past : List (EventHistory.Stage (code := code))) :
    (IncidentBirth.identities start vocabulary encoding law past).card ≤ capacity (code := code) := by
  have included : (IncidentBirth.identities start vocabulary encoding law past).image IncidentBirth.normalize ⊆ directory encoding := by
    intro tagged member
    obtain ⟨identity, inside, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp inside)
    exact every_actual_incident_has_an_authenticated_signal_scope encoding start vocabulary law entry
  have bound := Finset.card_le_card included
  rw [Finset.card_image_of_injOn (IncidentBirth.normalization_preserves_distinct_actual_identities start vocabulary encoding law past)] at bound
  exact bound.trans (directory_has_the_original_finite_interface_capacity encoding)

theorem removing_every_decoded_signal_cannot_leave_an_actual_incident
    (empty : ∀ signal, encoding signal = none)
    (entry : StageAccountability.Incident start vocabulary encoding law) : False := by
  have actual := every_actual_incident_has_an_authenticated_signal_scope encoding start vocabulary law entry
  simp [directory, scopes, empty] at actual

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentInventory
