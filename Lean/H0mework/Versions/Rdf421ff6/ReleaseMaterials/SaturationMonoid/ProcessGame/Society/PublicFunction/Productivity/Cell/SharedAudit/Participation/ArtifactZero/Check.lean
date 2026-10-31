import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Service

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero

abbrev Observation := { occurrence : Occurrence // occurrence ∈ occurrences 25 }

def goods : List Good := [.seed, .feed, .life, .spare, .waste, .energy, .labor]

theorem every_good_is_listed (good : Good) : good ∈ goods := by cases good <;> decide

/-- Exact operation content plus the actor's own signature. -/
def cycleTag (request : RequestAt) : Nat :=
  if request.signer = 1 ∧ request.consents = [] then
    match request.operation with
    | .produce actor => if actor = 1 then 1 else 0
    | .use actor goods purpose =>
      if actor = 1 ∧ goods = [(.life, 1)] ∧ purpose = .necessity then 2
      else if actor = 1 ∧ goods = [(.spare, 1)] ∧ purpose = .maintenance then 3 else 0
    | _ => 0
  else 0

namespace Check

variable {Row : Type} (rows : List Row) (Holds : Row → Prop) [DecidablePred Holds]

structure Accepted where
  checked : ∀ row ∈ rows, Holds row

structure Rejected where
  row : Row
  original : row ∈ rows
  broken : ¬ Holds row

def failures : List (Rejected rows Holds) := rows.attach.filterMap fun row =>
  if broken : ¬ Holds row.val then some ⟨row.val, row.property, broken⟩ else none

theorem failed_check_has_an_original_row
    (failed : rows.all (fun row => decide (Holds row)) ≠ true) :
    (failures rows Holds).isEmpty = false := by
  apply List.isEmpty_eq_false_iff.mpr
  intro empty
  apply failed
  apply List.all_eq_true.mpr
  intro row member
  apply decide_eq_true
  by_contra broken
  have present : (⟨row, member, broken⟩ : Rejected rows Holds) ∈ failures rows Holds := by
    unfold failures
    apply List.mem_filterMap.mpr
    refine ⟨⟨row, member⟩, List.mem_attach _ _, ?_⟩
    rw [dif_pos broken]
  rw [empty] at present
  cases present

inductive Result
  | accepted (certificate : Accepted rows Holds)
  | rejected (failure : Rejected rows Holds)

def run : Result rows Holds :=
  if checked : rows.all (fun row => decide (Holds row)) = true then
    .accepted ⟨fun row member => of_decide_eq_true (List.all_eq_true.mp checked row member)⟩
  else .rejected ((failures rows Holds).head
    (List.isEmpty_eq_false_iff.mp (failed_check_has_an_original_row rows Holds checked)))

theorem run_accepts (checked : ∀ row ∈ rows, Holds row) :
    run rows Holds = .accepted ⟨checked⟩ := by
  have passes : rows.all (fun row => decide (Holds row)) = true := by
    apply List.all_eq_true.mpr
    intro row member
    exact decide_eq_true (checked row member)
  simp only [run, dif_pos passes]

end Check
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero
