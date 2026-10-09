import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Actual

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1AtomicDynamics.Source
noncomputable section
open CPS1ResourceExecution

theorem product_no_guard (frame : CPS1Recycling.Frame) (reaction : Reaction frame) (failure : Body.Failure) :
    ((reaction.products frame).count (.guard failure)) = 0 := by
  cases reaction with
  | capture chain => simp [Reaction.products]
  | requireAtomic => rfl
  | report state address row =>
    cases computed : Body.report? frame state address row <;> simp [Reaction.products,computed]
  | deposit state amount =>
    cases computed : Body.deposit? frame state amount <;> simp [Reaction.products,computed]
  | pulse state dt =>
    cases computed : Body.pulse? frame state dt <;> simp [Reaction.products,computed]

theorem credit_no_guard (frame : CPS1Recycling.Frame) (fired : List (Reaction frame)) (failure : Body.Failure) :
    (Inventory.credit (Reaction.products frame) fired).count (.guard failure) = 0 := by
  induction fired with
  | nil => rfl
  | cons reaction rest ih =>
    simp only [Inventory.credit,List.flatMap_cons,List.count_append,product_no_guard,ih,zero_add]

theorem execute_no_guard (frame : CPS1Recycling.Frame) (program : List (Reaction frame)) (stock : Stock frame)
    (failure : Body.Failure) (empty : stock.count (.guard failure) = 0) :
    (execute frame program stock).stock.count (.guard failure) = 0 := by
  have balance := full_inventory frame program stock (.guard failure)
  dsimp only at balance
  rw [empty,credit_no_guard] at balance
  omega

theorem raw_no_guard (frame : CPS1Recycling.Frame) (actions : List RawAction) (failure : Body.Failure) :
    (actions.flatMap (RawAction.material frame)).count (.guard failure) = 0 := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
    cases action <;> simp only [List.flatMap_cons,List.count_append,RawAction.material,List.count_cons,
      List.count_nil,reduceCtorEq,beq_iff_eq,if_false,ih,zero_add]

theorem start_no_guard (frame : CPS1Recycling.Frame) (previous : CPS1AtomicSource.Current.Occurrence frame)
    (failure : Body.Failure) : (start frame previous).stock.count (.guard failure) = 0 := by
  apply execute_no_guard
  apply List.count_eq_zero.mpr
  intro member
  rcases List.mem_map.mp member with ⟨old,_,same⟩
  cases same

theorem advance_no_guard (frame : CPS1Recycling.Frame) (cursor : Cursor frame) (actions : List RawAction)
    (failure : Body.Failure) (empty : cursor.stock.count (.guard failure) = 0) :
    (advance frame cursor actions).stock.count (.guard failure) = 0 := by
  apply execute_no_guard
  simp only [List.count_append,empty,raw_no_guard,zero_add]

theorem guard_cut (frame : CPS1Recycling.Frame) (reaction : Reaction frame) (failure : Body.Failure)
    (required : 0 < (reaction.reactants frame).count (.guard failure))
    (stock : Stock frame) (empty : stock.count (.guard failure) = 0) :
    (execute frame [reaction] stock).remaining = [reaction] ∧
      (execute frame [reaction] stock).fired = [] ∧ (execute frame [reaction] stock).stock = stock := by
  cases paid : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock with
  | error missing => simp [execute,Inventory.execute,paid]
  | ok next =>
    have balance := Inventory.fire_balance (Reaction.reactants frame) (Reaction.products frame)
      reaction stock next paid (.guard failure)
    rw [empty,product_no_guard] at balance
    omega

end
end CPS1AtomicDynamics.Source
