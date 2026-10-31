import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Bounds

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (bound : BoundSource base scope)

abbrev Inputs := List (RawEvent Party Good Port (State Party Technology) Instrument)

structure Resident (inputs : Inputs (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) where
  originInputs : Inputs (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  original : Claim (fromHistory bound) originInputs
  history : History (fromHistory bound) original inputs
  within : History.Within bound (inputs.length + 2) history

variable {inputs : Inputs (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}

theorem claimsAt_ordinal (ordinal : Nat) (claim : Claim (fromHistory bound) inputs) (inside : claim ∈ claimsAt (fromHistory bound) inputs ordinal) :
    claim.position.ordinal = ordinal := by
  obtain ⟨position, member, decoded⟩ := List.mem_filterMap.mp inside
  rw [read_position (fromHistory bound) inputs position claim decoded]
  obtain ⟨index, _, same⟩ := List.mem_map.mp member
  cases same
  rfl

def Resident.admitAt (ordinal : Nat) (inside : ordinal < inputs.length + 2)
    (claim : {claim : Claim (fromHistory bound) inputs // claim ∈ claimsAt (fromHistory bound) inputs ordinal}) : Resident bound inputs :=
  ⟨inputs, claim.val, History.inherit (fromHistory bound) (Challenge.through (Mandate.Challenge.fromHistory bound) inputs claim.val (inputs.length + 2)),
    inherit_within bound _ _ (local_through_within bound claim.val _ _
      (by rw [claimsAt_ordinal bound ordinal claim.val claim.property]; exact inside) (Nat.le_refl _))⟩

def residentsAt (inputs : Inputs (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    List (Resident bound inputs) :=
  (List.finRange (inputs.length + 2)).flatMap fun ordinal =>
    (claimsAt (fromHistory bound) inputs ordinal.val).attach.map (Resident.admitAt bound ordinal.val ordinal.isLt)

def Resident.beforeAppend (resident : Resident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) :
    History (fromHistory bound) resident.original (nextInputs inputs word) :=
  transportHistory bound word resident.history resident.within

def Resident.afterAppend (resident : Resident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) :
    History (fromHistory bound) resident.original (nextInputs inputs word) :=
  (positionsAt (fromHistory bound) (nextInputs inputs word) (inputs.length + 2)).foldl
    (History.receive (fromHistory bound)) (resident.beforeAppend bound word)

def Resident.advance (resident : Resident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) : Resident bound (nextInputs inputs word) :=
  ⟨resident.originInputs, resident.original, resident.afterAppend bound word,
    fold_within bound _ _ _ (transported_within bound word resident.history resident.within) (by
      intro position member
      obtain ⟨index, _, same⟩ := List.mem_map.mp member
      cases same
      simp only [nextInputs, List.length_append, List.length_singleton]
      omega)⟩

theorem Resident.old_entire_state_is_the_actual_continuation_start (resident : Resident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) :
    (resident.beforeAppend bound word).state = resident.history.state :=
  transport_preserves_the_entire_generated_state bound word resident.history resident.within

def Resident.responseRun (resident : Resident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) :
    (process (fromHistory bound) resident.original).Run resident.history.state.current (resident.afterAppend bound word).state.current := by
  have actual := visitRun bound (resident.beforeAppend bound word)
    (positionsAt (fromHistory bound) (nextInputs inputs word) (inputs.length + 2))
  rw [resident.old_entire_state_is_the_actual_continuation_start bound word] at actual
  exact actual

def newborn (word : RawEvent Party Good Port (State Party Technology) Instrument) : List (Resident bound (nextInputs inputs word)) :=
  (claimsAt (fromHistory bound) (nextInputs inputs word) (inputs.length + 2)).attach.map
    (Resident.admitAt bound (inputs.length + 2) (by simp [nextInputs]))

def advanceAll (inventory : List (Resident bound inputs)) (word : RawEvent Party Good Port (State Party Technology) Instrument) :
    List (Resident bound (nextInputs inputs word)) :=
  inventory.map (fun resident => resident.advance bound word) ++ newborn bound word

theorem every_old_resident_is_actually_consumed (inventory : List (Resident bound inputs))
    (word : RawEvent Party Good Port (State Party Technology) Instrument) (resident : Resident bound inputs) (inside : resident ∈ inventory) :
    resident.advance bound word ∈ advanceAll bound inventory word :=
  List.mem_append_left _ (List.mem_map.mpr ⟨resident, inside, rfl⟩)

theorem inventory_length_preserves_every_old_and_adds_only_actual_births (inventory : List (Resident bound inputs))
    (word : RawEvent Party Good Port (State Party Technology) Instrument) :
    (advanceAll bound inventory word).length = inventory.length +
      (claimsAt (fromHistory bound) (nextInputs inputs word) (inputs.length + 2)).length := by
  simp [advanceAll, newborn]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross
