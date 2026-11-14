import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Ports.Relations

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.PortUpdate
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)

structure Output where
  frame : Frame
  rejected : Bool
  binding : List FunctionalSubstitution.Instruction
  joint : Option Result

def Output.value (output : Output) : JointCircuit.Update := ⟨output.frame.state,output.rejected,output.binding,output.joint⟩

def oldStep (frame : Frame) : Output :=
  if JointCircuit.noAdd frame.state.arena.code then
    let source := JointCircuit.analyzed frame.state
    match source.value with
    | .contradiction => ⟨frame,true,[],some source.value⟩
    | .basis basis =>
        match JointCircuit.pick frame.state basis with
        | none => ⟨frame,false,[],some source.value⟩
        | some item =>
            ⟨PortEmbedding.bind frame item.address item.relation.right,false,[ArenaSource.selected frame.state item],some source.value⟩
  else ⟨frame,false,[],none⟩

theorem oldStep_value (frame : Frame) : (oldStep frame).value=JointCircuit.update frame.state := by
  simp only [oldStep,Output.value,JointCircuit.update]
  split
  · split
    · simp_all
    · split <;> simp_all [PortEmbedding.bind]
  · simp_all

def selected {frame : Frame} (offer : PortRelations.Offer frame) : FunctionalSubstitution.Instruction :=
  ArenaSource.selected offer.emission.target offer.item

def perform (frame : Frame) (offer : PortRelations.Offer frame) : Output :=
  ⟨PortEmbedding.bind (PortEmbedding.extend frame offer.body) offer.address offer.emission.root,
    false,[selected offer],none⟩

theorem perform_state (frame : Frame) (offer : PortRelations.Offer frame) :
    (perform frame offer).frame.state=ArenaSource.next offer.emission.target offer.address offer.emission.root := rfl

theorem perform_ports (frame : Frame) (offer : PortRelations.Offer frame) :
    (perform frame offer).frame.ports.size=frame.ports.size := by
  exact (PortEmbedding.bind_size (PortEmbedding.extend frame offer.body) offer.address offer.emission.root).trans
    (PortEmbedding.extend_size frame offer.body)

theorem perform_size (frame : Frame) (offer : PortRelations.Offer frame) :
    (perform frame offer).frame.state.arena.code.size ≤ frame.state.arena.code.size+offer.body.code.size+1 := by
  rw [perform_state,ArenaSource.next_size]
  exact PortEmbedding.append_size frame.state frame.ports offer.body

set_option maxHeartbeats 1200000 in
theorem perform_read (frame : Frame) (offer : PortRelations.Offer frame)
    (allowed : offer.allowed=true)
    (entailed : ∀ point, JointCircuit.read frame.state point=true → offer.item.relation.read point=true) (point : Nat → Bool) :
    (perform frame offer).value.read point=JointCircuit.read frame.state point := by
  have source : (perform frame offer).value.read point=
      (FunctionalAffine.legal [selected offer] point &&
        JointCircuit.read offer.emission.target (ArenaAction.Action.environment offer.emission.target.arena offer.address offer.emission.root point)) := by
    change (FunctionalAffine.legal [selected offer] point && JointCircuit.read (perform frame offer).frame.state point)=_
    rw [perform_state,JointCircuit.next_read]
  rw [source]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨guard,accepted⟩
    have fixed := FunctionalAffine.legal_fixed [selected offer] point guard
    change (selected offer).bind point=point at fixed
    have same := ArenaSource.selected_environment offer.emission.target offer.item allowed point
    change ArenaAction.Action.environment offer.emission.target.arena offer.address offer.emission.root point=(selected offer).bind point at same
    rw [same,fixed] at accepted
    exact (PortEmbedding.append_read frame.state frame.ports offer.body point).symm.trans accepted
  · intro accepted
    have fixed := ArenaSource.eligible_fixed offer.emission.target offer.item allowed point (entailed point accepted)
    have selectedFixed := (ArenaSource.selected_environment offer.emission.target offer.item allowed point).symm.trans fixed
    refine ⟨FunctionalAffine.legal_of_fixed [selected offer] point ?_,?_⟩
    · intro call member
      simp only [List.mem_singleton] at member
      exact member ▸ selectedFixed
    · change JointCircuit.read offer.emission.target (ArenaAction.Action.environment offer.emission.target.arena offer.item.address offer.item.relation.right point)=true
      rw [fixed]
      exact (PortEmbedding.append_read frame.state frame.ports offer.body point).trans accepted

set_option maxHeartbeats 1200000 in
theorem perform_transport (frame : Frame) (offer : PortRelations.Offer frame) (allowed : offer.allowed=true) (point : Nat → Bool) :
    (!(perform frame offer).rejected && JointCircuit.read (perform frame offer).frame.state point)=
      JointCircuit.read frame.state (FunctionalSubstitution.fill (perform frame offer).binding point) := by
  change JointCircuit.read (perform frame offer).frame.state point=JointCircuit.read frame.state ((selected offer).bind point)
  rw [perform_state,JointCircuit.next_read]
  have same := ArenaSource.selected_environment offer.emission.target offer.item allowed point
  change ArenaAction.Action.environment offer.emission.target.arena offer.address offer.emission.root point=(selected offer).bind point at same
  rw [same]
  exact PortEmbedding.append_read frame.state frame.ports offer.body _

theorem perform_decreases (frame : Frame) (offer : PortRelations.Offer frame) (allowed : offer.allowed=true) :
    ArenaTotal.remaining (perform frame offer).frame.state<ArenaTotal.remaining frame.state := by
  have less := JointIteration.eligible_decreases offer.emission.target offer.item allowed
  have subset : ArenaTotal.support offer.emission.target ⊆ ArenaTotal.support frame.state := by
    intro i member
    exact List.mem_toFinset.mpr (PortEmbedding.append_inputs frame.state frame.ports offer.body (List.mem_toFinset.mp member))
  exact less.trans_le (Finset.card_le_card subset)

def update (frame : Frame) : Output :=
  let old := oldStep frame
  if JointRelationUpdate.usePrevious old.value then old else
    match PortRelations.generate frame with
    | none => old
    | some offer => perform frame offer

theorem update_read (frame : Frame) (point : Nat → Bool) : (update frame).value.read point=JointCircuit.read frame.state point := by
  simp only [update]
  split
  · rw [oldStep_value,JointCircuit.update_read]
  · cases found : PortRelations.generate frame with
    | none => simp only [oldStep_value,JointCircuit.update_read]
    | some offer =>
        have spec := PortRelations.generate_spec frame offer found
        exact perform_read frame offer spec.1 spec.2.2 point

theorem update_transport (frame : Frame) (point : Nat → Bool) :
    (!(update frame).rejected && JointCircuit.read (update frame).frame.state point)=
      JointCircuit.read frame.state (FunctionalSubstitution.fill (update frame).binding point) := by
  simp only [update]
  split
  · have old := JointCircuit.update_transport frame.state point
    rw [← oldStep_value] at old
    exact old
  · cases found : PortRelations.generate frame with
    | none =>
        have old := JointCircuit.update_transport frame.state point
        rw [← oldStep_value] at old
        exact old
    | some offer => exact perform_transport frame offer (PortRelations.generate_spec frame offer found).1 point

theorem update_correct (frame : Frame) :
    (∃ point, (!(update frame).rejected && JointCircuit.read (update frame).frame.state point)=true) ↔
      ∃ point, JointCircuit.read frame.state point=true := by
  constructor
  · rintro ⟨point,accepted⟩
    exact ⟨FunctionalSubstitution.fill (update frame).binding point,(update_transport frame point).symm.trans accepted⟩
  · rintro ⟨point,accepted⟩
    have after := (update_read frame point).trans accepted
    simp only [Output.value,JointCircuit.Update.read,Bool.and_eq_true] at after
    exact ⟨point,by simp only [Bool.and_eq_true]; exact ⟨after.1.1,after.2⟩⟩


theorem oldStep_size (frame : Frame) : (oldStep frame).frame.state.arena.code.size=frame.state.arena.code.size := by
  have same := congrArg (fun out => out.state.arena.code.size) (oldStep_value frame)
  exact same.trans (JointCircuit.update_next_size frame.state)

theorem oldStep_count (frame : Frame) : (oldStep frame).frame.state.relations.length=frame.state.relations.length := by
  have same := congrArg (fun out => out.state.relations.length) (oldStep_value frame)
  exact same.trans (JointCircuit.update_relations frame.state)

theorem oldStep_ports (frame : Frame) : (oldStep frame).frame.ports.size=frame.ports.size := by
  by_cases checked : JointCircuit.noAdd frame.state.arena.code=true
  · cases source : (JointCircuit.analyzed frame.state).value with
    | contradiction =>
        have same : oldStep frame=⟨frame,true,[],some .contradiction⟩ := by simp [oldStep,checked,source]
        rw [same]
    | basis basis =>
        cases chosen : JointCircuit.pick frame.state basis with
        | none =>
            have same : oldStep frame=⟨frame,false,[],some (.basis basis)⟩ := by simp [oldStep,checked,source,chosen]
            rw [same]
        | some item =>
            have same : oldStep frame=⟨PortEmbedding.bind frame item.address item.relation.right,false,
              [ArenaSource.selected frame.state item],some (.basis basis)⟩ := by simp [oldStep,checked,source,chosen]
            rw [same]
            exact PortEmbedding.bind_size frame item.address item.relation.right
  · have same : oldStep frame=⟨frame,false,[],none⟩ := by simp [oldStep,checked]
    rw [same]

theorem oldStep_idle (frame : Frame) (empty : (oldStep frame).binding=[]) : (oldStep frame).frame=frame := by
  by_cases checked : JointCircuit.noAdd frame.state.arena.code=true
  · cases source : (JointCircuit.analyzed frame.state).value with
    | contradiction => simp only [oldStep,checked,if_true,source]
    | basis basis =>
        cases selected : JointCircuit.pick frame.state basis with
        | none => simp only [oldStep,checked,if_true,source,selected]
        | some item => simp only [oldStep,checked,if_true,source,selected,List.cons_ne_self] at empty
  · simp only [oldStep,if_neg checked]

theorem update_size (frame : Frame) : (update frame).frame.state.arena.code.size ≤ frame.state.arena.code.size+2*frame.ports.size+2 := by
  simp only [update]
  split
  · rw [oldStep_size]; omega
  · cases found : PortRelations.generate frame with
    | none => rw [oldStep_size]; omega
    | some offer =>
        have bound := perform_size frame offer
        have body := (PortRelations.generate_spec frame offer found).2.1
        change (perform frame offer).frame.state.arena.code.size ≤ _
        omega

theorem update_ports (frame : Frame) : (update frame).frame.ports.size=frame.ports.size := by
  by_cases previous : JointRelationUpdate.usePrevious (oldStep frame).value=true
  · rw [update,if_pos previous]
    exact oldStep_ports frame
  · rw [update,if_neg previous]
    cases found : PortRelations.generate frame with
    | none => exact oldStep_ports frame
    | some offer => exact perform_ports frame offer

theorem update_count (frame : Frame) : (update frame).frame.state.relations.length=frame.state.relations.length := by
  by_cases previous : JointRelationUpdate.usePrevious (oldStep frame).value=true
  · rw [update,if_pos previous]
    exact oldStep_count frame
  · rw [update,if_neg previous]
    cases found : PortRelations.generate frame with
    | none => exact oldStep_count frame
    | some offer =>
        rw [perform_state,ArenaSource.next_count]
        exact PortEmbedding.append_count frame.state frame.ports offer.body

theorem update_decreases (frame : Frame) (nonempty : (update frame).binding≠[]) :
    ArenaTotal.remaining (update frame).frame.state<ArenaTotal.remaining frame.state := by
  by_cases previous : JointRelationUpdate.usePrevious (oldStep frame).value=true
  · simp only [update,if_pos previous] at nonempty ⊢
    have old := JointIteration.update_decreases frame.state
    rw [← oldStep_value] at old
    exact old nonempty
  · simp only [update,if_neg previous] at nonempty ⊢
    cases found : PortRelations.generate frame with
    | none =>
        have old := JointIteration.update_decreases frame.state
        rw [← oldStep_value] at old
        exact old (by simpa only [found,Output.value] using nonempty)
    | some offer => exact perform_decreases frame offer (PortRelations.generate_spec frame offer found).1

theorem update_idle (frame : Frame) (empty : (update frame).binding=[]) : (update frame).frame=frame := by
  by_cases previous : JointRelationUpdate.usePrevious (oldStep frame).value=true
  · simp only [update,if_pos previous] at empty ⊢
    exact oldStep_idle frame empty
  · simp only [update,if_neg previous] at empty ⊢
    cases found : PortRelations.generate frame with
    | none => exact oldStep_idle frame (by simpa only [found] using empty)
    | some offer => simp only [found,perform,List.cons_ne_self] at empty



theorem oldStep_port_read (frame : Frame) (point : Nat → Bool) (i : Nat) (inside : i < frame.ports.size) :
    (oldStep frame).frame.read point i=frame.read (FunctionalSubstitution.fill (oldStep frame).binding point) i := by
  by_cases checked : JointCircuit.noAdd frame.state.arena.code=true
  · cases source : (JointCircuit.analyzed frame.state).value with
    | contradiction => simp [oldStep,checked,source,FunctionalSubstitution.fill]
    | basis basis =>
        cases chosen : JointCircuit.pick frame.state basis with
        | none => simp [oldStep,checked,source,chosen,FunctionalSubstitution.fill]
        | some item =>
            have same : oldStep frame=⟨PortEmbedding.bind frame item.address item.relation.right,false,
              [ArenaSource.selected frame.state item],some (.basis basis)⟩ := by simp [oldStep,checked,source,chosen]
            rw [same]
            change (PortEmbedding.bind frame item.address item.relation.right).read point i=
              frame.read ((ArenaSource.selected frame.state item).bind point) i
            rw [PortEmbedding.bind_read frame item.address item.relation.right point i inside,
              ArenaSource.selected_environment frame.state item (JointCircuit.pick_spec frame.state basis item chosen).1]
  · simp [oldStep,checked,FunctionalSubstitution.fill]

theorem perform_port_read (frame : Frame) (offer : PortRelations.Offer frame) (allowed : offer.allowed=true)
    (point : Nat → Bool) (i : Nat) (inside : i < frame.ports.size) :
    (perform frame offer).frame.read point i=frame.read (FunctionalSubstitution.fill (perform frame offer).binding point) i := by
  have nextInside : i < (PortEmbedding.extend frame offer.body).ports.size := by rw [PortEmbedding.extend_size]; exact inside
  have moved := PortEmbedding.bind_read (PortEmbedding.extend frame offer.body) offer.address offer.emission.root point i nextInside
  have kept := PortEmbedding.extend_read frame offer.body
    (ArenaAction.Action.environment offer.emission.target.arena offer.address offer.emission.root point) i inside
  have same := ArenaSource.selected_environment offer.emission.target offer.item allowed point
  have combined : (perform frame offer).frame.read point i=
      frame.read (ArenaAction.Action.environment offer.emission.target.arena offer.address offer.emission.root point) i := moved.trans kept
  change ArenaAction.Action.environment offer.emission.target.arena offer.address offer.emission.root point=(selected offer).bind point at same
  rw [same] at combined
  exact combined

theorem update_port_read (frame : Frame) (point : Nat → Bool) (i : Nat) (inside : i < frame.ports.size) :
    (update frame).frame.read point i=frame.read (FunctionalSubstitution.fill (update frame).binding point) i := by
  by_cases previous : JointRelationUpdate.usePrevious (oldStep frame).value=true
  · rw [update,if_pos previous]
    exact oldStep_port_read frame point i inside
  · rw [update,if_neg previous]
    cases found : PortRelations.generate frame with
    | none => exact oldStep_port_read frame point i inside
    | some offer => exact perform_port_read frame offer (PortRelations.generate_spec frame offer found).1 point i inside

def combine (first second : Output) : Output :=
  ⟨second.frame,second.rejected,first.binding++second.binding,second.joint⟩

theorem combine_value (first second : Output) : (combine first second).value=JointIteration.combine first.value second.value := rfl

def iterate : Nat → Frame → Output
  | 0,frame => ⟨frame,false,[],none⟩
  | fuel+1,frame =>
      let first := update frame
      if JointIteration.done first.value then first else combine first (iterate fuel first.frame)

theorem iterate_read (fuel : Nat) (frame : Frame) (point : Nat → Bool) :
    (iterate fuel frame).value.read point=JointCircuit.read frame.state point := by
  induction fuel generalizing frame with
  | zero => simp [iterate,Output.value,JointCircuit.Update.read,FunctionalAffine.legal]
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact update_read frame point
      · rename_i continuing
        have keep := JointIteration.continue_spec (update frame).value continuing
        rw [combine_value,JointIteration.combine_read,ih]
        have running : (update frame).rejected=false := keep.1
        simpa only [JointCircuit.Update.read,Output.value,running,Bool.not_false,Bool.true_and] using update_read frame point

theorem iterate_ports (fuel : Nat) (frame : Frame) : (iterate fuel frame).frame.ports.size=frame.ports.size := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      by_cases stopped : JointIteration.done (update frame).value=true
      · rw [iterate,if_pos stopped]
        exact update_ports frame
      · rw [iterate,if_neg stopped]
        exact (ih (update frame).frame).trans (update_ports frame)

theorem iterate_count (fuel : Nat) (frame : Frame) : (iterate fuel frame).frame.state.relations.length=frame.state.relations.length := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      by_cases stopped : JointIteration.done (update frame).value=true
      · rw [iterate,if_pos stopped]
        exact update_count frame
      · rw [iterate,if_neg stopped]
        exact (ih (update frame).frame).trans (update_count frame)

theorem iterate_size (fuel : Nat) (frame : Frame) :
    (iterate fuel frame).frame.state.arena.code.size ≤ frame.state.arena.code.size+fuel*(2*frame.ports.size+2) := by
  induction fuel generalizing frame with
  | zero => simp [iterate]
  | succ fuel ih =>
      have first := update_size frame
      have tail := ih (update frame).frame
      rw [update_ports] at tail
      simp only [iterate]
      split
      · nlinarith
      · change (iterate fuel (update frame).frame).frame.state.arena.code.size ≤ _
        nlinarith

def Settled (output : Output) : Prop := output.rejected=true ∨ (update output.frame).binding=[]

theorem iterate_settled (fuel : Nat) (frame : Frame) (enough : ArenaTotal.remaining frame.state ≤ fuel) : Settled (iterate fuel frame) := by
  induction fuel generalizing frame with
  | zero =>
      apply Or.inr
      change (update frame).binding=[]
      by_contra nonempty
      have less := update_decreases frame nonempty
      omega
  | succ fuel ih =>
      simp only [iterate]
      split
      · rename_i stopped
        simp only [JointIteration.done,Output.value,Bool.or_eq_true,List.isEmpty_iff] at stopped
        rcases stopped with rejected | empty
        · exact Or.inl rejected
        · exact Or.inr ((congrArg (fun f => (update f).binding) (update_idle frame empty)).trans empty)
      · rename_i continuing
        have changed := update_decreases frame (JointIteration.continue_spec (update frame).value continuing).2
        exact ih (update frame).frame (by omega)

theorem iterate_correct (fuel : Nat) (frame : Frame) :
    (∃ point, (!(iterate fuel frame).rejected && JointCircuit.read (iterate fuel frame).frame.state point)=true) ↔
      ∃ point, JointCircuit.read frame.state point=true := by
  induction fuel generalizing frame with
  | zero => simp [iterate]
  | succ fuel ih =>
      by_cases stopped : JointIteration.done (update frame).value=true
      · rw [iterate,if_pos stopped]
        exact update_correct frame
      · rw [iterate,if_neg stopped]
        change (∃ point, (!(iterate fuel (update frame).frame).rejected && JointCircuit.read (iterate fuel (update frame).frame).frame.state point)=true) ↔ _
        rw [ih]
        have live := (JointIteration.continue_spec (update frame).value stopped).1
        change (update frame).rejected=false at live
        simpa only [live,Bool.not_false,Bool.true_and] using update_correct frame

theorem fill_append (first second : List FunctionalSubstitution.Instruction) (point : Nat → Bool) :
    FunctionalSubstitution.fill (first++second) point=FunctionalSubstitution.fill first (FunctionalSubstitution.fill second point) := by
  simp only [FunctionalSubstitution.fill,List.foldr_append]

theorem iterate_port_read (fuel : Nat) (frame : Frame) (point : Nat → Bool) (i : Nat) (inside : i < frame.ports.size) :
    (iterate fuel frame).frame.read point i=frame.read (FunctionalSubstitution.fill (iterate fuel frame).binding point) i := by
  induction fuel generalizing frame point with
  | zero => rfl
  | succ fuel ih =>
      by_cases stopped : JointIteration.done (update frame).value=true
      · rw [iterate,if_pos stopped]
        exact update_port_read frame point i inside
      · rw [iterate,if_neg stopped]
        change (iterate fuel (update frame).frame).frame.read point i=
          frame.read (FunctionalSubstitution.fill ((update frame).binding++(iterate fuel (update frame).frame).binding) point) i
        rw [ih _ point (by rw [update_ports]; exact inside),fill_append,update_port_read frame _ i inside]

def run (state : ArenaSource.State) : Output := iterate state.arena.code.size (PortEmbedding.initial state)

theorem run_read (state : ArenaSource.State) (point : Nat → Bool) : (run state).value.read point=JointCircuit.read state point :=
  iterate_read _ (PortEmbedding.initial state) point

theorem run_settled (state : ArenaSource.State) : Settled (run state) :=
  iterate_settled _ (PortEmbedding.initial state) (ArenaTotal.remaining_le_nodes state)

theorem run_size (state : ArenaSource.State) :
    (run state).frame.state.arena.code.size ≤ 2*state.arena.code.size*state.arena.code.size+3*state.arena.code.size := by
  have bound := iterate_size state.arena.code.size (PortEmbedding.initial state)
  rw [PortEmbedding.initial_size] at bound
  change (run state).frame.state.arena.code.size ≤ state.arena.code.size+state.arena.code.size*(2*state.arena.code.size+2) at bound
  nlinarith



theorem oldStep_valid (frame : Frame) (valid : ArenaSource.Valid frame.state) : ArenaSource.Valid (oldStep frame).frame.state := by
  have good := JointIteration.update_valid frame.state valid
  rw [← oldStep_value] at good
  exact good

theorem perform_valid (frame : Frame) (valid : ArenaSource.Valid frame.state) (offer : PortRelations.Offer frame) :
    ArenaSource.Valid (perform frame offer).frame.state := by
  have source : ArenaSource.Valid offer.emission.target := by
    intro point accepted
    change truth ((PortEmbedding.append frame.state frame.ports offer.body).target.program.program.eval point)=true at accepted
    rw [PortEmbedding.append_program] at accepted
    exact (PortEmbedding.append_relations frame.state frame.ports offer.body point).trans (valid point accepted)
  rw [perform_state]
  exact ArenaSource.next_valid _ source _ _

theorem update_valid (frame : Frame) (valid : ArenaSource.Valid frame.state) : ArenaSource.Valid (update frame).frame.state := by
  simp only [update]
  split
  · exact oldStep_valid frame valid
  · cases found : PortRelations.generate frame with
    | none => exact oldStep_valid frame valid
    | some offer => exact perform_valid frame valid offer

theorem iterate_valid (fuel : Nat) (frame : Frame) (valid : ArenaSource.Valid frame.state) :
    ArenaSource.Valid (iterate fuel frame).frame.state := by
  induction fuel generalizing frame with
  | zero => exact valid
  | succ fuel ih =>
      simp only [iterate]
      split
      · exact update_valid frame valid
      · exact ih (update frame).frame (update_valid frame valid)

set_option maxHeartbeats 1200000 in
theorem prepared_valid {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    ArenaSource.Valid (JointRelationCost.compile formula basis).value.state := by
  rw [JointRelationCost.compile_value]
  exact JointRelationUpdate.iterate_valid _ _ (JointIteration.prepared_valid formula basis valid)

def continueFrom (previous : JointCircuit.Update) : Output :=
  if previous.rejected then ⟨PortEmbedding.initial previous.state,true,previous.binding,previous.joint⟩ else
    let next := run previous.state
    ⟨next.frame,next.rejected,previous.binding++next.binding,next.joint⟩

theorem continueFrom_read (previous : JointCircuit.Update) (point : Nat → Bool) :
    (continueFrom previous).value.read point=previous.read point := by
  by_cases rejected : previous.rejected=true
  · simp only [continueFrom,rejected,if_true,Output.value,JointCircuit.Update.read,Bool.not_true,Bool.false_and]
  · have alive : previous.rejected=false := Bool.eq_false_iff.mpr rejected
    rw [continueFrom,if_neg rejected]
    change (JointIteration.combine previous (run previous.state).value).read point=_
    rw [JointIteration.combine_read,run_read]
    simp only [JointCircuit.Update.read,alive,Bool.not_false,Bool.true_and]

theorem continueFrom_valid (previous : JointCircuit.Update) (valid : ArenaSource.Valid previous.state) :
    ArenaSource.Valid (continueFrom previous).frame.state := by
  simp only [continueFrom]
  split
  · exact valid
  · exact iterate_valid _ _ valid

theorem continueFrom_correct (previous : JointCircuit.Update) :
    (∃ point, (!(continueFrom previous).rejected && JointCircuit.read (continueFrom previous).frame.state point)=true) ↔
      ∃ point, (!previous.rejected && JointCircuit.read previous.state point)=true := by
  by_cases rejected : previous.rejected=true
  · simp only [continueFrom,rejected,if_true,Bool.not_true,Bool.false_and]
  · have alive : previous.rejected=false := Bool.eq_false_iff.mpr rejected
    rw [continueFrom,if_neg rejected]
    simp only [alive,Bool.not_false,Bool.true_and]
    exact iterate_correct _ (PortEmbedding.initial previous.state)

theorem continueFrom_settled (previous : JointCircuit.Update) : Settled (continueFrom previous) := by
  simp only [continueFrom]
  split
  · exact Or.inl rfl
  · exact run_settled _

theorem continueFrom_size (previous : JointCircuit.Update) :
    (continueFrom previous).frame.state.arena.code.size ≤ 2*previous.state.arena.code.size*previous.state.arena.code.size+3*previous.state.arena.code.size := by
  simp only [continueFrom]
  split
  · change previous.state.arena.code.size ≤ _
    nlinarith
  · exact run_size previous.state

def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : Output :=
  continueFrom (JointRelationCost.compile formula basis).value

theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) :
    (compile formula basis).value.read point=CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point) :=
  (continueFrom_read _ point).trans (JointRelationCost.compile_read formula basis valid point)

theorem compile_valid {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) : ArenaSource.Valid (compile formula basis).frame.state :=
  continueFrom_valid _ (prepared_valid formula basis valid)

theorem compile_settled {n : Nat} (formula : CNFFormula n) (basis : List Row) : Settled (compile formula basis) :=
  continueFrom_settled _

def stateDecision (state : ArenaSource.State) (rejected : Bool) : Bool := !rejected && FunctionalSubstitution.decideProgram state.program.program

theorem stateDecision_iff (state : ArenaSource.State) (valid : ArenaSource.Valid state) (rejected : Bool) :
    stateDecision state rejected=true ↔ ∃ point, (!rejected && JointCircuit.read state point)=true := by
  cases rejected <;> simp only [stateDecision,Bool.not_true,Bool.not_false,Bool.true_and,Bool.false_and,
    Bool.false_eq_true,exists_false,JointCircuit.valid_read state valid,FunctionalSubstitution.decideProgram_correct]

def decide {n : Nat} (formula : CNFFormula n) (basis : List Row) : Bool :=
  let output := compile formula basis
  stateDecision output.frame.state output.rejected

set_option maxHeartbeats 1200000 in
theorem decide_correct {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) : decide formula basis=true ↔
      ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true := by
  let previous := (JointRelationCost.compile formula basis).value
  have oldValid := prepared_valid formula basis valid
  have oldDecision : stateDecision previous.state previous.rejected=true ↔
      ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true := by
    change stateDecision (JointRelationCost.compile formula basis).value.state (JointRelationCost.compile formula basis).value.rejected=true ↔ _
    rw [JointRelationCost.compile_value]
    exact JointRelationUpdate.decide_correct formula basis valid
  have original := (stateDecision_iff previous.state oldValid previous.rejected).symm.trans oldDecision
  exact (stateDecision_iff _ (compile_valid formula basis valid) _).trans ((continueFrom_correct previous).trans original)

set_option maxHeartbeats 1200000 in
theorem compile_size {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    (compile formula basis).frame.state.arena.code.size ≤
      let first := ArenaSource.sourceBound n formula.length (Extract.literalCount formula)
      let next := 2*first*first+3*first
      2*next*next+3*next := by
  let previous := (JointRelationCost.compile formula basis).value
  let first := ArenaSource.sourceBound n formula.length (Extract.literalCount formula)
  let next := 2*first*first+3*first
  have original : previous.state.arena.code.size ≤ next := by
    change (JointRelationCost.compile formula basis).value.state.arena.code.size ≤ next
    rw [JointRelationCost.compile_value]
    exact JointRelationUpdate.compile_size formula basis valid
  apply (continueFrom_size previous).trans
  change 2*previous.state.arena.code.size*previous.state.arena.code.size+3*previous.state.arena.code.size ≤ 2*next*next+3*next
  gcongr

def projector {n : Nat} (formula : CNFFormula n) (source : Source n) : Source n :=
  let output := compile formula []
  fun point => if output.value.read (extendAssignment point) then source point else 0

set_option maxHeartbeats 1200000 in
theorem projector_original {n : Nat} (formula : CNFFormula n) (source : Source n) : projector formula source=zeroProjector formula source := by
  funext point
  simp only [projector,compile_read formula [] ⟨triangular_nil,by simp [RowsWithin]⟩,zeroProjector_apply]
  rw [FunctionalMessage.empty_formula]


end SaturationMonoid.ComplexityProjection.SATSource.PortUpdate
