import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Native

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Institutions.Capitalism.Universal.Source.ProgrammeFace
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

def needed (actor : Bool) : Bool := inventory.objections.any fun record =>
  record.history.isPending && (claimant inventory record == actor)

def actors : List Bool := [false,true].filter (needed inventory)

theorem needed_iff (actor : Bool) : needed inventory actor = true ↔
    ∃ record ∈ inventory.objections, record.history.isPending = true ∧ claimant inventory record = actor := by
  simp only [needed,List.any_eq_true,Bool.and_eq_true,beq_iff_eq]

theorem every_pending_original_is_covered (record : Record inventory)
    (member : record ∈ inventory.objections) (pending : record.history.isPending = true) :
    claimant inventory record ∈ actors inventory := by
  apply List.mem_filter.mpr
  refine ⟨by cases claimant inventory record <;> simp,?_⟩
  exact (needed_iff inventory _).mpr ⟨record,member,pending,rfl⟩

theorem every_emitted_actor_has_source_standing (actor : Bool) (member : actor ∈ actors inventory) :
    actor ∈ Delegation.members epoch.scope.task := by
  obtain ⟨_,needed⟩ := List.mem_filter.mp member
  obtain ⟨record,_,_,same⟩ := (needed_iff inventory actor).mp needed
  rw [← same]
  exact claimant_has_original_standing inventory record

def signatures := (actors inventory).map (Input.signature epoch)

def word : List Action :=
  if Mandate.Response.Active (current epoch inventory.inputs) then
    signatures inventory ++ (decision inventory).word else []

def after := World.submit inventory (word inventory)
def actual := World.actual inventory (word inventory)
def original (record : Record inventory) := record.advance epoch.bound (word inventory)

theorem actual_word_and_saved_cut : (actual inventory).submitted = word inventory ∧
    (actual inventory).before = current epoch inventory.inputs := World.actual_word_and_cut _ _

theorem signature_preserves_current (actor : Bool) :
    (Mandate.law base epoch.scope).step (current epoch inventory.inputs) (Input.signature epoch actor) =
      current epoch inventory.inputs := by
  unfold RawLaw.step
  split
  · apply RawCurrent.ext <;> simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,RawLaw.nextClaims,Input.signature]
  · rfl

theorem signature_prefix_preserves_current (signers : List Bool) :
    ((Mandate.law base epoch.scope).execute (current epoch inventory.inputs) 0
      (signers.map (Input.signature epoch))).final = current epoch inventory.inputs := by
  have all : ∀ start, ((Mandate.law base epoch.scope).execute (current epoch inventory.inputs) start
      (signers.map (Input.signature epoch))).final = current epoch inventory.inputs := by
    induction signers with
    | nil => intro start; rfl
    | cons actor tail ih =>
      intro start
      simp only [List.map_cons,RawLaw.execute,signature_preserves_current,ih]
  exact all 0

theorem active_word (active : Mandate.Response.Active (current epoch inventory.inputs)) :
    word inventory = signatures inventory ++ [Mandate.request epoch.scope (current epoch inventory.inputs)
      (withdrawalActor inventory active) .revoke] := by
  rw [word,if_pos active,active_decision_word inventory active]

theorem every_pending_original_uses_the_shared_source_word (record : Record inventory)
    (member : record ∈ inventory.objections) (pending : record.history.isPending = true)
    (active : Mandate.Response.Active (current epoch inventory.inputs)) :
    Input.signature epoch (claimant inventory record) ∈ signatures inventory ∧
    word inventory = signatures inventory ++ [Mandate.request epoch.scope (current epoch inventory.inputs)
      (withdrawalActor inventory active) .revoke] :=
  ⟨List.mem_map.mpr ⟨_,every_pending_original_is_covered inventory record member pending,rfl⟩,active_word inventory active⟩


theorem actors_shape : actors inventory = [] ∨ actors inventory = [false] ∨
    actors inventory = [true] ∨ actors inventory = [false,true] := by
  cases first : needed inventory false <;> cases second : needed inventory true <;>
    simp [actors,first,second]

section Active
variable (active : Mandate.Response.Active (current epoch inventory.inputs))

def items := Registered.traceItems
  (Mandate.Challenge.I (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory)))
  (ProgrammeHistory.visitAt (Mandate.Challenge.I (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory)))
    (inventory.inputs.length+2)).current

theorem items_exact : items inventory =
    ((actors inventory).zipIdx.map fun pair =>
      ⟨pair.2,current epoch inventory.inputs,Input.signature epoch pair.1⟩) ++
    [⟨(actors inventory).length,current epoch inventory.inputs,
      Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke⟩] := by
  change (Mandate.law base epoch.scope).rawItems (actual inventory).before (actual inventory).submitted = _
  rw [(actual_word_and_saved_cut inventory).1,(actual_word_and_saved_cut inventory).2,active_word inventory active]
  rcases actors_shape inventory with shape | shape | shape | shape <;>
    simp [signatures,shape,RawLaw.rawItems,RawLaw.execute,signature_preserves_current]

def position (index : Fin ((actors inventory).length+1)) :
    Mandate.Challenge.Position (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory)) :=
  ⟨inventory.inputs.length+2,⟨index.val,by
    change index.val < (items inventory).length
    rw [items_exact inventory active]
    simpa using index.isLt⟩⟩

def signing (index : Fin (actors inventory).length) :=
  position inventory active ⟨index.val,Nat.lt_succ_of_lt index.isLt⟩

def withdrawalPosition := position inventory active ⟨(actors inventory).length,Nat.lt_succ_self _⟩

theorem signing_item (index : Fin (actors inventory).length) :
    (signing inventory active index).item _ _ =
      ⟨index.val,current epoch inventory.inputs,Input.signature epoch ((actors inventory)[index.val])⟩ := by
  have same := congrArg (fun items => items[index.val]?) (items_exact inventory active)
  have bound : index.val < (items inventory).length := (signing inventory active index).index.isLt
  rw [List.getElem?_eq_getElem bound] at same
  have left : index.val < ((actors inventory).zipIdx.map fun pair =>
      (⟨pair.2,current epoch inventory.inputs,Input.signature epoch pair.1⟩ : ExecutionItem Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit)).length := by
    simp only [List.length_map,List.length_zipIdx]
    exact index.isLt
  rw [List.getElem?_append_left left,List.getElem?_eq_getElem left] at same
  change (items inventory)[index.val] = _
  simpa only [List.getElem_map,List.getElem_zipIdx,Nat.zero_add] using Option.some.inj same

theorem withdrawal_item : (withdrawalPosition inventory active).item _ _ =
    ⟨(actors inventory).length,current epoch inventory.inputs,
      Mandate.request epoch.scope (current epoch inventory.inputs) (withdrawalActor inventory active) .revoke⟩ := by
  have same := congrArg (fun items => items[(actors inventory).length]?) (items_exact inventory active)
  have bound : (actors inventory).length < (items inventory).length := (withdrawalPosition inventory active).index.isLt
  rw [List.getElem?_eq_getElem bound] at same
  simp only [List.getElem?_append,List.length_map,List.length_zipIdx,Nat.lt_irrefl,ite_false,
    Nat.sub_self,List.getElem?_cons_zero] at same
  exact Option.some.inj same

theorem emitted_positions :
    Mandate.Challenge.positionsAt (Bound (epoch := epoch)) (Mandate.Challenge.Cross.nextInputs inventory.inputs (word inventory)) (inventory.inputs.length+2) =
      ((List.finRange (actors inventory).length).map (signing inventory active)) ++ [withdrawalPosition inventory active] := by
  apply List.ext_getElem
  · simp only [Mandate.Challenge.positionsAt,List.length_map,List.length_finRange,List.length_append,List.length_singleton]
    change (items inventory).length = _
    rw [items_exact inventory active]
    simp
  · intro index left right
    by_cases before : index < (actors inventory).length
    · rw [List.getElem_append_left (by simpa only [List.length_map,List.length_finRange] using before)]
      simp [Mandate.Challenge.positionsAt,signing,position,List.getElem_finRange]
    · have last : index = (actors inventory).length := by
        simp only [List.length_append,List.length_map,List.length_finRange,List.length_singleton] at right
        omega
      subst index
      rw [List.getElem_append_right (by simp)]
      simp [Mandate.Challenge.positionsAt,withdrawalPosition,position,List.getElem_finRange]

end Active

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared
