import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Family
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.RelationHistory

/-! The capital circuit keeps the actor and relation generated at each
original occurrence.  The endpoint receives those exact births through its
original root history; raw keys are never replacement actor identities. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History

open Program ProgrammeFace Kernel.AssetAuthority
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (endpoint : Visit input)

omit [DecidableEq Port] in
theorem Entry.address_in_original_history (entry : Entry input endpoint) :
    entry.address input ∈ addressesBefore input endpoint := by
  obtain ⟨pair, member, same⟩ := List.mem_map.mp entry.property
  have original := List.fst_mem_of_mem_zipIdx member
  have sameAddress := congrArg Prod.snd same
  exact Eq.mp (congrArg (fun address : Address input => address ∈ addressesBefore input endpoint) sameAddress) original

omit [DecidableEq Port] in
theorem Entry.ordinal_selects_exact_original (entry : Entry input endpoint) :
    (addressesBefore input endpoint)[entry.position input]? = some (entry.address input) := by
  rcases entry with ⟨⟨index, address⟩, member⟩
  obtain ⟨⟨oldAddress, oldIndex⟩, original, same⟩ := List.mem_map.mp member
  have both : oldIndex = index ∧ oldAddress = address := Prod.mk.inj same
  rcases both with ⟨rfl, rfl⟩
  exact List.mk_mem_zipIdx_iff_getElem?.mp original

namespace Capital
variable (capital : Capital input endpoint)

def accessVisit : Visit input := (capital.access.access.address input).1

def accessItem : RootFace.Item input (capital.accessVisit input endpoint) :=
  (capital.access.access.address input).2

private theorem executor_present : ActualBirth.presentAt input (capital.accessVisit input endpoint)
    (capital.access.access.raw input).request.signer := by
  apply List.mem_dedup.mpr
  exact List.mem_flatMap.mpr ⟨(capital.access.access.raw input),
    (capital.accessItem input endpoint).property, List.mem_cons_self⟩

def executorBirth := ActualBirth.generate input (capital.accessVisit input endpoint)
  (capital.access.access.raw input).request.signer (capital.executor_present input endpoint)

private theorem relation_present : RelationHistory.presentAt input (capital.accessVisit input endpoint)
    capital.access.port := by
  refine ⟨(capital.access.port, capital.access.controller input endpoint), ?_, rfl⟩
  apply item_relation_present input.law (RelationHistory.origin input (capital.accessVisit input endpoint))
    (capital.access.access.raw input) (capital.accessItem input endpoint).property
  · exact List.mem_cons_of_mem _ capital.checked.1.2.1
  · exact controller_mem_itemParties input.law (capital.access.access.raw input) _ capital.checked.1.2.1

def relationBirth := RelationHistory.generate input (capital.accessVisit input endpoint)
  capital.access.port (capital.relation_present input endpoint)

def actor := (capital.executorBirth input endpoint).actor input
def relation := (capital.relationBirth input endpoint).relation input

theorem original_actor_survives_every_cross_word_successor :
    ActualBirth.lookup input endpoint (capital.access.access.raw input).request.signer =
      some (capital.executorBirth input endpoint).original := by
  apply address_before_transports input
    (fun visit => ActualBirth.lookup input visit (capital.access.access.raw input).request.signer =
      some (capital.executorBirth input endpoint).original)
    (fun visit {_next} nextEq holds => ActualBirth.lookup_retains_original_birth input visit nextEq _ _ holds)
    endpoint (capital.access.access.address input)
    (capital.access.access.address_in_original_history input endpoint)
  exact (capital.executorBirth input endpoint).generated

theorem same_asset_relation_survives_holder_rotation :
    RelationHistory.lookup input endpoint capital.access.port =
      some (capital.relationBirth input endpoint).original := by
  apply address_before_transports input
    (fun visit => RelationHistory.lookup input visit capital.access.port =
      some (capital.relationBirth input endpoint).original)
    (fun visit {_next} nextEq holds => RelationHistory.lookup_keeps_original_relation input visit nextEq _ _ holds)
    endpoint (capital.access.access.address input)
    (capital.access.access.address_in_original_history input endpoint)
  exact (capital.relationBirth input endpoint).generated

def actualSurplusOrigin : Option (Root.Financial.InstructionOrigin input) :=
  (capital.evidence.actualPosition input endpoint capital.access).map (Entry.origin input)

theorem exact_original_rows_and_current_relation :
    (capital.accessOrigin input endpoint).instruction? input = some (capital.access.access.raw input) ∧
    (capital.needOrigin input endpoint).instruction? input = some (capital.access.need.raw input) ∧
    RelationHistory.lookup input endpoint capital.access.port =
      some (capital.relationBirth input endpoint).original :=
  ⟨capital.original_origins_and_actual_before input endpoint |>.1,
    capital.original_origins_and_actual_before input endpoint |>.2.1,
    capital.same_asset_relation_survives_holder_rotation input endpoint⟩

end Capital

theorem generated_control_returns_original_history (visit : Visit input)
    (item : RootFace.Item input visit) (port : Port)
    (member : port ∈ generatedFamily input visit item) :
    ∃ capital ∈ Discovery.discovered input (actual input visit),
      capital.access.port = port ∧ FreshControl input port item.val ∧
      (capital.accessOrigin input (actual input visit)).instruction? input =
        some (capital.access.access.raw input) ∧
      (capital.needOrigin input (actual input visit)).instruction? input =
        some (capital.access.need.raw input) ∧
      RelationHistory.lookup input (actual input visit) capital.access.port =
        some (capital.relationBirth input (actual input visit)).original ∧
      (RootFace.original input visit item).instruction? input = some item.val := by
  obtain ⟨capital, generated, same, fresh⟩ := generatedFamily_actual_control input visit item port member
  exact ⟨capital, generated, same, fresh,
    capital.exact_original_rows_and_current_relation input (actual input visit) |>.1,
    capital.exact_original_rows_and_current_relation input (actual input visit) |>.2.1,
    capital.same_asset_relation_survives_holder_rotation input (actual input visit),
    RootFace.original_decodes_exact_item input visit item⟩

#print axioms Entry.ordinal_selects_exact_original
#print axioms Capital.original_actor_survives_every_cross_word_successor
#print axioms Capital.same_asset_relation_survives_holder_rotation
#print axioms Capital.exact_original_rows_and_current_relation
#print axioms generated_control_returns_original_history

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History
