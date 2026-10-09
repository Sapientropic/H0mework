import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Actual

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1EnzymeBath.Source
noncomputable section
open CPS1ResourceExecution

theorem product_no_guard (frame : CPS1Recycling.Frame) (reaction : Reaction frame) (failure : CPS1AtomicDynamics.Body.Failure) :
    ((reaction.products frame).count (.guard failure)) = 0 := by
  cases reaction with
  | capture body => simp [Reaction.products]
  | attach state kind => simp [Reaction.products]
  | requireBody => rfl
  | report state address row =>
    cases computed : Joint.report? frame state address row <;> simp [Reaction.products,computed]
  | deposit state amount =>
    cases computed : Joint.deposit? frame state amount <;> simp [Reaction.products,computed]
  | pulse state dt =>
    cases computed : Joint.pulse? frame state dt <;> simp [Reaction.products,computed]

theorem credit_no_guard (frame : CPS1Recycling.Frame) (fired : List (Reaction frame)) (failure : CPS1AtomicDynamics.Body.Failure) :
    (Inventory.credit (Reaction.products frame) fired).count (.guard failure) = 0 := by
  induction fired with
  | nil => rfl
  | cons reaction rest ih =>
    simp only [Inventory.credit,List.flatMap_cons,List.count_append,product_no_guard,ih,zero_add]

theorem execute_no_guard (frame : CPS1Recycling.Frame) (program : List (Reaction frame)) (stock : Stock frame)
    (failure : CPS1AtomicDynamics.Body.Failure) (empty : stock.count (.guard failure) = 0) :
    (execute frame program stock).stock.count (.guard failure) = 0 := by
  have balance := whole_inventory frame program stock (.guard failure)
  dsimp only at balance
  rw [empty,credit_no_guard] at balance
  omega

theorem raw_no_guard (frame : CPS1Recycling.Frame) (actions : List RawAction) (failure : CPS1AtomicDynamics.Body.Failure) :
    (actions.flatMap (RawAction.material frame)).count (.guard failure) = 0 := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
    cases action <;> simp only [List.flatMap_cons,List.count_append,RawAction.material,List.count_cons,
      List.count_nil,reduceCtorEq,beq_iff_eq,if_false,ih,zero_add]

theorem start_no_guard (frame : CPS1Recycling.Frame) (previous : CPS1AtomicDynamics.Source.Occurrence frame)
    (failure : CPS1AtomicDynamics.Body.Failure) : (start frame previous).stock.count (.guard failure) = 0 := by
  apply execute_no_guard
  induction previous.current.stock with
  | nil => rfl
  | cons species rest ih =>
    cases species <;> simp only [List.map_cons,liftMaterial,List.count_cons,
      reduceCtorEq,beq_iff_eq,if_false] <;> exact ih

theorem advance_no_guard (frame : CPS1Recycling.Frame) (cursor : Cursor frame) (actions : List RawAction) (feed : List Primary.TemplateKind)
    (failure : CPS1AtomicDynamics.Body.Failure) (empty : cursor.stock.count (.guard failure) = 0) :
    (advance frame cursor actions feed).stock.count (.guard failure) = 0 := by
  apply execute_no_guard
  have components : (feed.map (rawComponent frame)).count (.guard failure) = 0 := by
    apply List.count_eq_zero.mpr
    intro member
    rcases List.mem_map.mp member with ⟨kind,_,same⟩
    cases same
  simp only [List.count_append,empty,raw_no_guard,components,zero_add]

theorem guard_cut (frame : CPS1Recycling.Frame) (reaction : Reaction frame) (failure : CPS1AtomicDynamics.Body.Failure)
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
end CPS1EnzymeBath.Source
