import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Rows
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Partner

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1EnzymeBath

private theorem row_none (rows : List (CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row)) (address : CPS1AtomicDynamics.Charged.Address)
    (absent : address ∉ rows.map Prod.fst) : CPS1AtomicDynamics.Body.row? rows address = none := by
  induction rows with
  | nil => rfl
  | cons entry rest ih =>
    have different : entry.1 ≠ address := by
      intro same
      exact absent (by simp only [List.map_cons,List.mem_cons,same,true_or])
    have tailAbsent : address ∉ rest.map Prod.fst := fun held => absent (List.mem_cons_of_mem _ held)
    simpa [CPS1AtomicDynamics.Body.row?,different] using ih tailAbsent

theorem raw_reports_paid {frame : CPS1Recycling.Frame} (joint : Joint.State frame)
    (rows : List (CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row)) (stock surplus : Stock frame)
    (unique : (rows.map Prod.fst ++ joint.rows.map Prod.fst).Nodup)
    (known : ∀ entry ∈ rows, Joint.addressPresent frame joint entry.1 = true)
    (positive : ∀ entry ∈ rows, 0 < entry.2.inertia)
    (inventory : stock.Perm (.joint joint :: rows.map (fun entry => .rawRow entry.1 entry.2) ++ surplus)) :
    let actions : List Source.RawAction := rows.map (fun entry => .report entry.1 entry.2)
    let result := execute frame (Source.program frame joint actions) stock
    result.fired.length = rows.length ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (.joint {joint with rows := rows.reverse ++ joint.rows} :: surplus) := by
  induction rows generalizing joint stock with
  | nil =>
    cases joint
    exact ⟨rfl,rfl,rfl,inventory⟩
  | cons entry rest ih =>
    have wholeUnique : (entry.1 :: (rest.map Prod.fst ++ joint.rows.map Prod.fst)).Nodup := by
      simpa only [List.map_cons,List.cons_append] using unique
    have absent : entry.1 ∉ joint.rows.map Prod.fst := by
      intro held
      exact (List.nodup_cons.mp wholeUnique).1 (List.mem_append_right _ held)
    let updated : Joint.State frame := {joint with rows := entry :: joint.rows}
    have reported : Joint.report? frame joint entry.1 entry.2 = .ok updated := by
      simp only [Joint.report?,known entry (List.mem_cons_self),Bool.not_true,Bool.false_eq_true,
        if_false,not_le.mpr (positive entry (List.mem_cons_self)),row_none joint.rows entry.1 absent]
      rfl
    have required : Reaction.reactants frame (.report joint entry.1 entry.2) = [.joint joint,.rawRow entry.1 entry.2] := by
      simp only [Reaction.reactants,reported,guards,List.append_nil]
    have available : stock.Perm (Reaction.reactants frame (.report joint entry.1 entry.2) ++
        (rest.map (fun entry => .rawRow entry.1 entry.2) ++ surplus)) := by
      simpa only [required,List.map_cons,List.cons_append,List.nil_append] using inventory
    obtain ⟨next,paid,kept⟩ := CPS1ResourceExecution.Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
      (.report joint entry.1 entry.2) _ stock available
    have nextInventory : next.Perm (.joint updated :: rest.map (fun entry => .rawRow entry.1 entry.2) ++ surplus) := by
      simpa only [Reaction.products,reported,List.singleton_append,List.cons_append,List.nil_append] using kept
    have nextUnique : (rest.map Prod.fst ++ updated.rows.map Prod.fst).Nodup := by
      change (rest.map Prod.fst ++ entry.1 :: joint.rows.map Prod.fst).Nodup
      exact (List.perm_middle : (rest.map Prod.fst ++ entry.1 :: joint.rows.map Prod.fst).Perm
        (entry.1 :: (rest.map Prod.fst ++ joint.rows.map Prod.fst))).nodup_iff.mpr wholeUnique
    have nextKnown : ∀ item ∈ rest, Joint.addressPresent frame updated item.1 = true := by
      intro item held
      exact known item (List.mem_cons_of_mem entry held)
    have nextPositive : ∀ item ∈ rest, 0 < item.2.inertia := by
      intro item held
      exact positive item (List.mem_cons_of_mem entry held)
    have after := ih updated next nextUnique nextKnown nextPositive nextInventory
    have nextState : (Source.RawAction.report entry.1 entry.2).next frame joint = updated := by
      simp only [Source.RawAction.next,reported,Except.toOption,Option.getD_some]
    have execution : execute frame (Source.program frame joint
        ((entry :: rest).map (fun item => .report item.1 item.2))) stock =
        let later := execute frame (Source.program frame updated
          (rest.map (fun item => .report item.1 item.2))) next
        {later with fired := Reaction.report joint entry.1 entry.2 :: later.fired} := by
      change execute frame (.report joint entry.1 entry.2 ::
        Source.program frame ((Source.RawAction.report entry.1 entry.2).next frame joint)
          (rest.map (fun item => .report item.1 item.2))) stock = _
      rw [nextState,execute,CPS1ResourceExecution.Inventory.execute_cons,paid]
      rfl
    dsimp only at after ⊢
    rw [execution]
    refine ⟨congrArg Nat.succ after.1,after.2.1,after.2.2.1,?_⟩
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,updated] using after.2.2.2

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
