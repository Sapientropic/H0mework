import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Grants

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross

open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (bound : BoundSource base scope)

structure GrantResident (inputs : List (RawEvent Party Good Port (State Party Technology) Instrument)) where
  private mk ::
  birth : Fin (inputs.length + 1)
  grant : Grant base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val)
  actual : grant ∈ grantsAt base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val)
  history : Lifecycle.Observed.History base scope (grantCurrent bound inputs) (grantWord bound inputs) birth.val grant
  history_exact : history = Lifecycle.Observed.through inputs.length

variable {inputs : List (RawEvent Party Good Port (State Party Technology) Instrument)}

private def grantResidentAt (birth : Fin (inputs.length + 1))
    (grant : {grant // grant ∈ grantsAt base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val)}) :
    GrantResident bound inputs := ⟨birth, grant.val, grant.property, Lifecycle.Observed.through inputs.length, rfl⟩

def grantsBefore (inputs : List (RawEvent Party Good Port (State Party Technology) Instrument)) : List (GrantResident bound inputs) :=
  (List.finRange (inputs.length + 1)).flatMap fun birth =>
    (grantsAt base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val)).attach.map (grantResidentAt bound birth)

def GrantResident.advance (record : GrantResident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) : GrantResident bound (nextInputs inputs word) :=
  ⟨⟨record.birth.val, by simp only [nextInputs, List.length_append, List.length_singleton]; omega⟩,
    transportGrant bound inputs word record.birth record.grant,
    transportGrant_actual bound inputs word record.birth record.grant record.actual,
    Lifecycle.Observed.through (nextInputs inputs word).length, rfl⟩

def GrantResident.actualRun (record : GrantResident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) :
    (Lifecycle.Observed.process (base := base) (scope := scope)
      (currentAt := grantCurrent bound (nextInputs inputs word)) (wordAt := grantWord bound (nextInputs inputs word))
      (birth := record.birth.val) (grant := transportGrant bound inputs word record.birth record.grant)).Run
      record.history.state (record.advance bound word).history.state := by
  change (Lifecycle.Observed.process (base := base) (scope := scope)
    (currentAt := grantCurrent bound (nextInputs inputs word)) (wordAt := grantWord bound (nextInputs inputs word))
    (birth := record.birth.val) (grant := transportGrant bound inputs word record.birth record.grant)).Run
    record.history.state (Lifecycle.Observed.through (base := base) (scope := scope)
      (currentAt := grantCurrent bound (nextInputs inputs word)) (wordAt := grantWord bound (nextInputs inputs word))
      (birth := record.birth.val) (grant := transportGrant bound inputs word record.birth record.grant) (nextInputs inputs word).length).state
  rw [record.history_exact]
  rw [← transportGrant_entire_cut_state bound inputs word record.birth record.grant]
  simpa only [nextInputs, List.length_append, List.length_singleton] using
    (Lifecycle.Observed.fromActualCut (base := base) (scope := scope)
      (currentAt := grantCurrent bound (nextInputs inputs word)) (wordAt := grantWord bound (nextInputs inputs word))
      (birth := record.birth.val) (grant := transportGrant bound inputs word record.birth record.grant) inputs.length 1)

theorem GrantResident.original_native_admission_is_preserved (record : GrantResident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) :
    (admitGrant base scope _ _ (record.advance bound word).grant).native.target =
      (admitGrant base scope _ _ record.grant).native.target :=
  transportGrant_original_admission bound inputs word record.birth record.grant

def newbornGrants (word : RawEvent Party Good Port (State Party Technology) Instrument) : List (GrantResident bound (nextInputs inputs word)) :=
  let birth : Fin ((nextInputs inputs word).length + 1) := ⟨inputs.length + 1, by simp [nextInputs]⟩
  (grantsAt base scope (grantCurrent bound (nextInputs inputs word) birth.val)
    (grantWord bound (nextInputs inputs word) birth.val)).attach.map (grantResidentAt bound birth)

def advanceGrants (records : List (GrantResident bound inputs)) (word : RawEvent Party Good Port (State Party Technology) Instrument) :
    List (GrantResident bound (nextInputs inputs word)) :=
  records.map (fun record => record.advance bound word) ++ newbornGrants bound word

theorem every_original_grant_is_preserved (records : List (GrantResident bound inputs))
    (word : RawEvent Party Good Port (State Party Technology) Instrument) (record : GrantResident bound inputs) (inside : record ∈ records) :
    record.advance bound word ∈ advanceGrants bound records word :=
  List.mem_append_left _ (List.mem_map.mpr ⟨record, inside, rfl⟩)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross
