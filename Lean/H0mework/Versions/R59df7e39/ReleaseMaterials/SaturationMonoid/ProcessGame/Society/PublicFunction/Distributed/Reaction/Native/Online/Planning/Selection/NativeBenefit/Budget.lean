import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeBenefit
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeBenefit
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {Key : Type}

theorem conjunction_work_bound {P Q : Prop} (first : Check Key P) (later : Unit → Check Key Q) :
    (conjunction first later).work.length ≤ first.work.length+1+(later ()).work.length := by
  cases h : first.decision <;> simp [conjunction,h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
theorem implication_work_bound {P Q : Prop} (first : Check Key P) (later : Unit → Check Key Q) :
    (implication first later).work.length ≤ first.work.length+1+(later ()).work.length := by
  cases h : first.decision <;> simp [implication,h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem allRows_work_bound {α : Type} (P : α → Prop) (test : (item : α) → Check Key (P item))
    (budget : α → Nat) (bounded : ∀ item,(test item).work.length ≤ budget item) (items : List α) :
    (allRows P test items).work.length ≤ (items.map (fun item => budget item+1)).sum := by
  induction items with
  | nil => simp [allRows]
  | cons head tail ih =>
      have step := conjunction_work_bound (test head) (fun _ => allRows P test tail)
      change (conjunction (test head) (fun _ => allRows P test tail)).work.length ≤ _
      simp only [List.map_cons,List.sum_cons]
      have headBound := bounded head
      exact step.trans (by omega)

theorem count_work_bound [DecidableEq Key] (key : Key) (items : List Key) :
    (count key items).work.length ≤ 3*items.length := by
  induction items with
  | nil => simp [count]
  | cons head tail ih =>
      unfold count
      split <;> simp only [List.length_append,List.length_cons,List.length_nil]
      all_goals omega

theorem countLe_work_bound [DecidableEq Key] (key : Key) (left right : List Key) :
    (countLe key left right).work.length ≤ 3*(left.length+right.length)+1 := by
  have a := count_work_bound key left
  have b := count_work_bound key right
  change ((count key left).work ++ (count key right).work ++ (naturalLe _ _).work).length ≤ _
  simp only [List.length_append]
  change (count key left).work.length+(count key right).work.length+1 ≤ _
  omega

def subpermBudget (leftLength rightLength : Nat) := leftLength*(3*(leftLength+rightLength)+2)
theorem subpermBudget_mono {left right upperLeft upperRight : Nat}
    (a : left ≤ upperLeft) (b : right ≤ upperRight) :
    subpermBudget left right ≤ subpermBudget upperLeft upperRight := by
  unfold subpermBudget
  exact Nat.mul_le_mul a (by omega)
theorem subperm_work_bound [DecidableEq Key] (left right : List Key) :
    (subperm left right).work.length ≤ subpermBudget left.length right.length := by
  change (allRows (fun key => left.count key ≤ right.count key) (fun key => countLe key left right) left).work.length ≤ _
  have bounded := allRows_work_bound (fun key => left.count key ≤ right.count key)
    (fun key => countLe key left right) (fun _ => 3*(left.length+right.length)+1)
    (fun key => countLe_work_bound key left right) left
  simpa [subpermBudget,List.sum_replicate,Nat.mul_comm] using bounded

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code} (cursor : Cursor seed driver)

def inventoryDueBudget (new previous : Feedback.Authority.Trace.Manifest Party Good Port Technology Instrument) : Nat :=
  NativeInventory.budget new + NativeInventory.budget previous +
    subpermBudget (NativeInventory.rowCount new) (NativeInventory.rowCount previous)

theorem inventoryDue_work_bound (new previous : Feedback.Authority.Trace.Manifest Party Good Port Technology Instrument) :
    (inventoryDue new previous).work.length ≤ inventoryDueBudget new previous := by
  have bound := subperm_work_bound (NativeInventory.compile new).inventory.due (NativeInventory.compile previous).inventory.due
  simp only [inventoryDue,record,transport,rekey,List.length_append,List.length_map]
  rw [NativeInventory.work_exact,NativeInventory.work_exact]
  rw [(NativeInventory.compile new).exact,(NativeInventory.compile previous).exact] at bound
  rw [(NativeInventory.compile new).exact,(NativeInventory.compile previous).exact]
  unfold inventoryDueBudget
  exact Nat.add_le_add_left (bound.trans (subpermBudget_mono (NativeInventory.due_length_bound new) (NativeInventory.due_length_bound previous))) _

/-- Only source-data shapes enter this bound; no comparison result is requested. -/
def presentBudget (new previous : Evaluation cursor.source.val.code) : Nat :=
  9 + inventoryDueBudget new.native previous.native +
      2*(Window.axes cursor.model cursor.depth).length

theorem present_work_bound (new previous : Evaluation cursor.source.val.code) :
    (present cursor new previous).work.length ≤ presentBudget cursor new previous := by
  let key := WorkKey Party Good Port Technology Instrument
  have legal := implication_work_bound (boolean (Key := key) previous.legal) (fun _ => boolean new.legal)
  have complete := implication_work_bound (boolean (Key := key) previous.complete) (fun _ => boolean new.complete)
  have keys := inventoryDue_work_bound new.native previous.native
  have axes := allRows_work_bound (fun axis => new.value axis ≤ previous.value axis)
    (fun axis => rationalLe (Key := key) (new.value axis) (previous.value axis)) (fun _ => 1)
    (fun _ => Nat.le_refl _) (Window.axes cursor.model cursor.depth)
  have third := conjunction_work_bound (inventoryDue new.native previous.native)
    (fun _ => allRows (fun axis => new.value axis ≤ previous.value axis)
      (fun axis => rationalLe (Key := key) (new.value axis) (previous.value axis)) (Window.axes cursor.model cursor.depth))
  have second := conjunction_work_bound
    (implication (boolean (Key := key) previous.complete) (fun _ => boolean new.complete)) (fun _ =>
      conjunction (inventoryDue new.native previous.native) (fun _ =>
        allRows (fun axis => new.value axis ≤ previous.value axis)
          (fun axis => rationalLe (Key := key) (new.value axis) (previous.value axis)) (Window.axes cursor.model cursor.depth)))
  have first := conjunction_work_bound
    (implication (boolean (Key := key) previous.legal) (fun _ => boolean new.legal)) (fun _ =>
      conjunction (implication (boolean previous.complete) (fun _ => boolean new.complete)) (fun _ =>
        conjunction (inventoryDue new.native previous.native) (fun _ =>
          allRows (fun axis => new.value axis ≤ previous.value axis)
            (fun axis => rationalLe (Key := key) (new.value axis) (previous.value axis)) (Window.axes cursor.model cursor.depth))))
  change (implication (boolean (Key := key) previous.legal) (fun _ => boolean new.legal)).work.length ≤ 3 at legal
  change (implication (boolean (Key := key) previous.complete) (fun _ => boolean new.complete)).work.length ≤ 3 at complete
  simp [List.sum_replicate,Nat.mul_comm] at axes
  change (present cursor new previous).work.length ≤ _ at first
  unfold presentBudget
  omega

def futureBudget (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) : Nat :=
  match new,previous with
  | some current,some original => presentBudget cursor current.evaluation original.evaluation+3
  | _,_ => 1

theorem future_work_bound (new previous : Option (Future.Recovery.Assessment.Report cursor.model)) :
    (future cursor new previous).work.length ≤ futureBudget cursor new previous := by
  cases new with
  | none => cases previous <;> simp [future,futureBudget]
  | some current =>
    cases previous with
    | none => simp [future,futureBudget]
    | some original =>
      have inside := conjunction_work_bound
        (naturalLe (Key := WorkKey Party Good Port Technology Instrument) original.consumed current.consumed)
        (fun _ => present cursor current.evaluation original.evaluation)
      have body := present_work_bound cursor current.evaluation original.evaluation
      change (conjunction (naturalLe original.consumed current.consumed)
        (fun _ => present cursor current.evaluation original.evaluation)).work.length+1 ≤ _
      change (conjunction (naturalLe original.consumed current.consumed)
        (fun _ => present cursor current.evaluation original.evaluation)).work.length ≤
          2+(present cursor current.evaluation original.evaluation).work.length at inside
      dsimp only [futureBudget]
      omega
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeBenefit
