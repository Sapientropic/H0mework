import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionProgress

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentBirth
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

abbrev Tag := Fin code.sites × StageAccountability.Slot (code := code)
abbrev Identity := Fin code.sites × StageAccountability.Slot (code := code) × Nat
def tag (entry : StageAccountability.Incident start vocabulary encoding law) : Tag (code := code) :=
  (entry.receiver, entry.slot)
def id (entry : StageAccountability.Incident start vocabulary encoding law) : Identity (code := code) :=
  (entry.receiver, entry.slot, entry.pastStages.length)
def normalize (identity : Identity (code := code)) : Tag (code := code) := (identity.1, identity.2.1)

private theorem an_earlier_birth_prevents_a_later_fresh_query
    (first second : StageAccountability.Incident start vocabulary encoding law)
    (ordered : first.birthStages <+: second.pastStages)
    (receiver : first.receiver = second.receiver) (slot : first.slot = second.slot) : False := by
  obtain ⟨more, actual⟩ := ordered
  have facts := StageAccountability.query_sound _ first.slot first.pair first.detected
  have kept := StagePrefix.receipts_survive_actual_extension start first.birthStages more vocabulary encoding law first.receiver
  have found := (StageAccountability.query_exists_iff
    (StageAccountability.receipts start vocabulary encoding law (first.birthStages ++ more) first.receiver) first.slot).mpr
      ⟨first.pair.1, kept.subset facts.1, first.pair.2, kept.subset facts.2.1, facts.2.2⟩
  rw [actual, receiver, slot] at found
  obtain ⟨pair, present⟩ := found
  rw [second.fresh] at present
  contradiction

theorem one_actual_receiver_slot_has_one_original_birthday
    (past : List (EventHistory.Stage (code := code)))
    (first second : StageAccountability.Incident start vocabulary encoding law)
    (one : first.birthStages <+: past) (two : second.birthStages <+: past)
    (same : tag start vocabulary encoding law first = tag start vocabulary encoding law second) :
    id start vocabulary encoding law first = id start vocabulary encoding law second := by
  have receiver := congrArg Prod.fst same
  have slot := congrArg Prod.snd same
  have ordered : first.pastStages.length = second.pastStages.length := by
    by_contra different
    rcases lt_or_gt_of_ne different with earlier | later
    · have source : second.pastStages <+: past := (List.prefix_append _ _).trans two
      have before := List.prefix_of_prefix_length_le one source
        (by simp only [StageAccountability.Incident.birthStages, List.length_append, List.length_singleton]; omega)
      exact an_earlier_birth_prevents_a_later_fresh_query start vocabulary encoding law first second before receiver slot
    · have source : first.pastStages <+: past := (List.prefix_append _ _).trans one
      have before := List.prefix_of_prefix_length_le two source
        (by simp only [StageAccountability.Incident.birthStages, List.length_append, List.length_singleton]; omega)
      exact an_earlier_birth_prevents_a_later_fresh_query start vocabulary encoding law second first before receiver.symm slot.symm
  exact Prod.ext receiver (Prod.ext slot ordered)

def identities (past : List (EventHistory.Stage (code := code))) : Finset (Identity (code := code)) :=
  ((StageAccountability.ledger start vocabulary encoding law past).map (id start vocabulary encoding law)).toFinset

theorem normalization_preserves_distinct_actual_identities
    (past : List (EventHistory.Stage (code := code))) :
    Set.InjOn (normalize (code := code)) (↑(identities start vocabulary encoding law past) : Set (Identity (code := code))) := by
  intro first one second two same
  obtain ⟨left, leftIn, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp one)
  obtain ⟨right, rightIn, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp two)
  exact one_actual_receiver_slot_has_one_original_birthday start vocabulary encoding law past left right
    (StageAccountability.every_generated_incident_has_its_original_birth_prefix start vocabulary encoding law [] past left leftIn)
    (StageAccountability.every_generated_incident_has_its_original_birth_prefix start vocabulary encoding law [] past right rightIn) same

theorem original_incident_identities_survive_extension
    (past more : List (EventHistory.Stage (code := code))) :
    identities start vocabulary encoding law past ⊆ identities start vocabulary encoding law (past ++ more) := by
  intro identity member
  obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨entry, ?_, rfl⟩
  rw [StageAccountability.ledger_extends_by_its_generated_next]
  exact List.mem_append_left _ inside

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentBirth
