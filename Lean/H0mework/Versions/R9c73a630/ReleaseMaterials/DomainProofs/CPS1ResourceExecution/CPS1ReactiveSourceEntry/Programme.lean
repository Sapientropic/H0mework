import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Cycle
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Reentry
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Source

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

namespace CPS1ReactiveSourceEntry
noncomputable section
open CPS1ElectronicSource CPS1ReactiveNuclear CPS1ReactiveJointNuclear
open CPS1ReactiveField CPS1ReactiveField.Carried
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
variable {frame : CPS1Recycling.Frame}

private theorem stock_selected {current : Occurrence frame} (source : Inlet current)
    (actual : inlet current = .ok source) : heldDeformed current.old.current.stock = some source.old := by
  unfold inlet at actual
  split at actual
  · cases actual
  · rename_i old selected
    split at actual
    · split at actual
      · cases actual
      · cases Except.ok.inj actual
        exact selected
    · cases actual

private def stockActive {current : Occurrence frame} (material : Material current) : Active frame :=
  ⟨current,initial material,initial_good material,material.source.body,material.source.actual,current.ingress.measurements.reserve⟩

private def stockCursor {current : Occurrence frame} (material : Material current)
    (germ : Germ current.old (initial material)) : SourceCursor frame :=
  ⟨⟨current,some (stockActive material),[⟨current,none,activate current⟩]⟩,.ok germ⟩

/-- The registered raw execution supplies the old-row law here, before any physical admission. -/
private def enterStock (old : CPS1Deformation.Source.Occurrence frame)
    (generated : NativeSource.GatherStock old.current.stock)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) : Entry frame := by
  classical
  let current := CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw
  let retained := SourceCursor.start current
  exact match selected : inlet current with
  | .error _ => match actual : activate current with
    | .error failure => .residual retained (.native failure)
    | .ok active => False.elim (by
        obtain ⟨source,admitted,_⟩ := activate_generated current active actual
        have impossible := selected.symm.trans admitted
        cases impossible)
  | .ok source => match actual : activate current with
    | .error failure => .residual retained (.native failure)
    | .ok _ =>
      let material : Material current := ⟨source,incomingReserve source-price source⟩
      match born : initialGerm material with
      | .error failure => .residual retained (.germ failure)
      | .ok germ =>
        if budget : 0 < material.reserve then
          let original := NativeSource.original_rows_from_stock material generated
          let rows := initial_birth_rows old actions feed raw material (stock_selected source selected) germ born original
          let aligned := initial_source_origin_aligned old actions feed raw material (stock_selected source selected) germ born original
          let cursor := stockCursor material germ
          .admitted ⟨cursor,stockActive material,rfl,rfl,germ,rfl,budget,rows,aligned⟩
        else .residual retained .exhaustedReserve

inductive Programme (frame : CPS1Recycling.Frame) (firstDepth secondDepth : Nat)
  | initialResidual (before chemical : SourceCursor frame) (failure : EntryFailure frame)
  | chemicalResidual (before : Entered frame) (first : EnteredRun before firstDepth)
      (chemical : SourceCursor frame) (failure : EntryFailure frame)
  | cycled (before : Entered frame) (first : EnteredRun before firstDepth)
      (chemical : Entered frame) (second : EnteredRun chemical secondDepth)

def Programme.current {firstDepth secondDepth : Nat} : Programme frame firstDepth secondDepth → SourceCursor frame
  | .initialResidual _ current _ => current
  | .chemicalResidual _ _ current _ => current
  | .cycled _ _ _ second => second.after.cursor

private def compileProgramme (admission : Entry frame) (firstDepth : Nat) (input : Input)
    (secondDepth : Nat) : Programme frame firstDepth secondDepth :=
  match admission with
  | .residual cursor failure =>
    .initialResidual cursor (SourceCursor.next cursor input.1.1 input.1.2 input.2) failure
  | .admitted before =>
    let first := renewEntered before firstDepth
    match reenter first.after input with
    | .residual current failure => .chemicalResidual before first current failure
    | .admitted chemical => .cycled before first chemical (renewEntered chemical secondDepth)

def programmeFromOld (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (firstDepth : Nat) (input : Input)
    (secondDepth : Nat) : Programme frame firstDepth secondDepth :=
  compileProgramme (enterFromOld old actions feed raw) firstDepth input secondDepth

private def programmeOfExecution
    (execution : Option (Σ frame : CPS1Recycling.Frame, CPS1Deformation.Source.Occurrence frame))
    (generated : ∀ source, execution = some source → NativeSource.GatherStock source.2.current.stock)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (firstDepth : Nat) (input : Input)
    (secondDepth : Nat) : Option (Σ frame : CPS1Recycling.Frame, Programme frame firstDepth secondDepth) := by
  cases execution with
  | none => exact none
  | some source =>
    exact some ⟨source.1,compileProgramme (enterStock source.2 (generated source rfl) actions feed raw)
      firstDepth input secondDepth⟩

def programmeFromSource
    (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (electronicActions : List CPS1ElectronicSource.Source.RawAction) (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (nuclearActions : List CPS1QuantumNuclear.Source.RawAction) (nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (followingActions : List CPS1Following.Source.RawAction) (followingFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (molecularActions : List CPS1MolecularFrame.Source.RawAction) (molecularFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (deformationActions : List CPS1Deformation.Source.RawAction) (deformationFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (firstDepth : Nat) (input : Input)
    (secondDepth : Nat) : Option (Σ frame : CPS1Recycling.Frame, Programme frame firstDepth secondDepth) :=
  programmeOfExecution (CPS1Deformation.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed)
    (fun source actual => NativeSource.execution_gather edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed source actual)
    actions feed raw firstDepth input secondDepth

def Programme.ActualRuns {firstDepth secondDepth : Nat}
    (programme : Programme frame firstDepth secondDepth) : Prop :=
    match programme with
    | .initialResidual _ _ _ => True
    | .chemicalResidual before first _ _ =>
      CPS1ReactiveJointNuclear.renew before.cursor firstDepth = ⟨first.after.cursor,first.pulses,0,none⟩
    | .cycled before first chemical second =>
      CPS1ReactiveJointNuclear.renew before.cursor firstDepth = ⟨first.after.cursor,first.pulses,0,none⟩ ∧
      CPS1ReactiveJointNuclear.renew chemical.cursor secondDepth = ⟨second.after.cursor,second.pulses,0,none⟩

theorem programme_two_actual_runs {firstDepth secondDepth : Nat}
    (programme : Programme frame firstDepth secondDepth) : programme.ActualRuns := by
  cases programme with
  | initialResidual before chemical failure => exact True.intro
  | chemicalResidual before first chemical failure => exact first.actual
  | cycled before first chemical second => exact ⟨first.actual,second.actual⟩

def Programme.ChemicalNext {firstDepth secondDepth : Nat}
    (programme : Programme frame firstDepth secondDepth) (input : Input) : Prop :=
  match programme with
  | .initialResidual before chemical _ =>
      chemical = SourceCursor.next before input.1.1 input.1.2 input.2
  | .chemicalResidual _ first chemical _ =>
      chemical = SourceCursor.next first.after.cursor input.1.1 input.1.2 input.2
  | .cycled _ first chemical _ =>
      chemical.cursor = SourceCursor.next first.after.cursor input.1.1 input.1.2 input.2

private theorem compile_chemical_next (admission : Entry frame) (firstDepth : Nat)
    (input : Input) (secondDepth : Nat) :
    (compileProgramme admission firstDepth input secondDepth).ChemicalNext input := by
  cases admission with
  | residual cursor failure => rfl
  | admitted before =>
    have generated := reentry_same_value (renewEntered before firstDepth).after input
    cases selected : reenter (renewEntered before firstDepth).after input <;>
      simpa only [compileProgramme,selected,Programme.ChemicalNext] using generated

theorem programme_from_old_chemical (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (firstDepth : Nat) (input : Input)
    (secondDepth : Nat) :
    (programmeFromOld old actions feed raw firstDepth input secondDepth).ChemicalNext input :=
  compile_chemical_next _ _ _ _

def Programme.beginning {firstDepth secondDepth : Nat} :
    Programme frame firstDepth secondDepth → SourceCursor frame
  | .initialResidual before _ _ => before
  | .chemicalResidual before _ _ _ => before.cursor
  | .cycled before _ _ _ => before.cursor

def Programme.chemicalBefore {firstDepth secondDepth : Nat} :
    Programme frame firstDepth secondDepth → SourceCursor frame
  | .initialResidual before _ _ => before
  | .chemicalResidual _ first _ _ => first.after.cursor
  | .cycled _ first _ _ => first.after.cursor

def Programme.chemicalAfter {firstDepth secondDepth : Nat} :
    Programme frame firstDepth secondDepth → SourceCursor frame
  | .initialResidual _ chemical _ => chemical
  | .chemicalResidual _ _ chemical _ => chemical
  | .cycled _ _ chemical _ => chemical.cursor

def Programme.Finite {firstDepth secondDepth : Nat}
    (programme : Programme frame firstDepth secondDepth) : Prop :=
  match programme with
  | .initialResidual _ _ _ => True
  | .chemicalResidual _ first _ _ =>
      first.pulses.length = firstDepth ∧ ∀ pulse ∈ first.pulses, pulse.Valid
  | .cycled _ first _ second =>
      first.pulses.length = firstDepth ∧ second.pulses.length = secondDepth ∧
      (∀ pulse ∈ first.pulses, pulse.Valid) ∧ ∀ pulse ∈ second.pulses, pulse.Valid

theorem programme_finite {firstDepth secondDepth : Nat}
    (programme : Programme frame firstDepth secondDepth) : programme.Finite := by
  cases programme with
  | initialResidual before chemical failure => exact True.intro
  | chemicalResidual before first chemical failure =>
    have ready := renew_ready before.cursor firstDepth before.ready
    have whole := renew_whole before.cursor firstDepth
    rw [first.actual] at ready whole
    exact ⟨ready.2.2.1,whole.2.2.2.2.2⟩
  | cycled before first chemical second =>
    have firstReady := renew_ready before.cursor firstDepth before.ready
    have firstWhole := renew_whole before.cursor firstDepth
    have secondReady := renew_ready chemical.cursor secondDepth chemical.ready
    have secondWhole := renew_whole chemical.cursor secondDepth
    rw [first.actual] at firstReady firstWhole
    rw [second.actual] at secondReady secondWhole
    exact ⟨firstReady.2.2.1,secondReady.2.2.1,firstWhole.2.2.2.2.2,secondWhole.2.2.2.2.2⟩

private theorem programme_before_whole {firstDepth secondDepth : Nat}
    (programme : Programme frame firstDepth secondDepth) :
    programme.chemicalBefore.native.current.old = programme.beginning.native.current.old ∧
    programme.chemicalBefore.native.current.ingress.atomic = programme.beginning.native.current.ingress.atomic ∧
    programme.chemicalBefore.native.current.ingress.pending = programme.beginning.native.current.ingress.pending ∧
    programme.chemicalBefore.native.current.ingress.stages = programme.beginning.native.current.ingress.stages ∧
    programme.chemicalBefore.native.stages = programme.beginning.native.stages := by
  cases programme with
  | initialResidual before chemical failure => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | chemicalResidual before first chemical failure =>
    have generated := renew_whole before.cursor firstDepth
    rw [first.actual] at generated
    exact ⟨generated.1,generated.2.1,generated.2.2.1,generated.2.2.2.1,generated.2.2.2.2.1⟩
  | cycled before first chemical second =>
    have generated := renew_whole before.cursor firstDepth
    rw [first.actual] at generated
    exact ⟨generated.1,generated.2.1,generated.2.2.1,generated.2.2.2.1,generated.2.2.2.2.1⟩

private theorem programme_after_whole {firstDepth secondDepth : Nat}
    (programme : Programme frame firstDepth secondDepth) :
    programme.current.native.current.old = programme.chemicalAfter.native.current.old ∧
    programme.current.native.current.ingress.atomic = programme.chemicalAfter.native.current.ingress.atomic ∧
    programme.current.native.current.ingress.pending = programme.chemicalAfter.native.current.ingress.pending ∧
    programme.current.native.current.ingress.stages = programme.chemicalAfter.native.current.ingress.stages ∧
    programme.current.native.stages = programme.chemicalAfter.native.stages := by
  cases programme with
  | initialResidual before chemical failure => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | chemicalResidual before first chemical failure => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | cycled before first chemical second =>
    have generated := renew_whole chemical.cursor secondDepth
    rw [second.actual] at generated
    exact ⟨generated.1,generated.2.1,generated.2.2.1,generated.2.2.2.1,generated.2.2.2.2.1⟩

def Programme.rowPayment {firstDepth secondDepth : Nat}
    (programme : Programme frame firstDepth secondDepth) (input : Input) :=
  let source := programme.chemicalBefore.native.current.ingress
  CPS1AddressedReactiveJoint.Rows.run
    (CPS1AddressedReactiveJoint.particles (CPS1AddressedReactiveJoint.atoms source.atomic.history
      (CPS1AddressedChemicalReaction.Source.available source.atomic.source input.1.1 input.1.2)))
    source.measurements (input.2 ++ source.pending)

def Programme.Whole {firstDepth secondDepth : Nat}
    (programme : Programme frame firstDepth secondDepth) (input : Input) : Prop :=
  programme.current.native.current.old = programme.beginning.native.current.old ∧
  programme.current.native.current.ingress.atomic = CPS1AddressedHydrolysis.Atomic.next
    programme.beginning.native.current.ingress.atomic input.1.1 input.1.2 ∧
  (programme.rowPayment input).paid ++ programme.current.native.current.ingress.pending =
    input.2 ++ programme.beginning.native.current.ingress.pending ∧
  programme.beginning.native.current.ingress.stages.Sublist programme.current.native.current.ingress.stages ∧
  programme.current.native.stages =
    (nextCursor programme.chemicalBefore.native input.1.1 input.1.2 input.2).stages

theorem programme_whole {firstDepth secondDepth : Nat}
    (programme : Programme frame firstDepth secondDepth) (input : Input)
    (actual : programme.ChemicalNext input) : programme.Whole input := by
  have chemical : programme.chemicalAfter =
      SourceCursor.next programme.chemicalBefore input.1.1 input.1.2 input.2 := by
    cases programme <;> exact actual
  have before := programme_before_whole programme
  have after := programme_after_whole programme
  have payment := CPS1AddressedReactiveJoint.source_generated_reactive_next
    programme.chemicalBefore.native.current.ingress input.1.1 input.1.2 input.2
  rw [chemical,SourceCursor.next_native] at after
  refine ⟨?_,?_,?_,?_,after.2.2.2.2⟩
  · exact after.1.trans before.1
  · exact after.2.1.trans (congrArg (fun atomic =>
      CPS1AddressedHydrolysis.Atomic.next atomic input.1.1 input.1.2) before.2.1)
  · rw [after.2.2.1]
    exact payment.2.2.2.2.1.trans (congrArg (fun pending => input.2 ++ pending) before.2.2.1)
  · rw [after.2.2.2.1,← before.2.2.2.1]
    exact payment.2.2.2.2.2.2.1

private theorem programme_of_execution_actual
    (execution : Option (Σ frame : CPS1Recycling.Frame, CPS1Deformation.Source.Occurrence frame))
    (generated : ∀ source, execution = some source → NativeSource.GatherStock source.2.current.stock)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (firstDepth : Nat) (input : Input)
    (secondDepth : Nat) :
    match programmeOfExecution execution generated actions feed raw firstDepth input secondDepth with
    | none => execution = none
    | some ⟨_,programme⟩ =>
        programme.ChemicalNext input ∧ programme.ActualRuns ∧ programme.Finite ∧ programme.Whole input := by
  cases execution with
  | none => simp only [programmeOfExecution]
  | some source =>
    simp only [programmeOfExecution]
    exact ⟨compile_chemical_next _ _ _ _,programme_two_actual_runs _,programme_finite _,
      programme_whole _ input (compile_chemical_next _ _ _ _)⟩

theorem programme_from_source_actual
    (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (electronicActions : List CPS1ElectronicSource.Source.RawAction) (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (nuclearActions : List CPS1QuantumNuclear.Source.RawAction) (nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (followingActions : List CPS1Following.Source.RawAction) (followingFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (molecularActions : List CPS1MolecularFrame.Source.RawAction) (molecularFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (deformationActions : List CPS1Deformation.Source.RawAction) (deformationFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (firstDepth : Nat) (input : Input)
    (secondDepth : Nat) :
    match programmeFromSource edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed
      actions feed raw firstDepth input secondDepth with
    | none => CPS1Deformation.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
        oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
        followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed = none
    | some ⟨_,programme⟩ =>
        programme.ChemicalNext input ∧ programme.ActualRuns ∧ programme.Finite ∧ programme.Whole input := by
  exact programme_of_execution_actual _ _ _ _ _ _ _ _

theorem programme_zero_first {secondDepth : Nat} (programme : Programme frame 0 secondDepth) :
    match programme with
    | .initialResidual _ _ _ => True
    | .chemicalResidual _ first _ _ => first.pulses = []
    | .cycled _ first _ _ => first.pulses = [] := by
  have generated := programme_finite programme
  cases programme with
  | initialResidual before chemical failure => exact True.intro
  | chemicalResidual before first chemical failure => exact List.length_eq_zero_iff.mp generated.1
  | cycled before first chemical second => exact List.length_eq_zero_iff.mp generated.1

theorem programme_zero_second {firstDepth : Nat} (programme : Programme frame firstDepth 0) :
    match programme with
    | .initialResidual _ _ _ => True
    | .chemicalResidual _ _ _ _ => True
    | .cycled _ _ _ second => second.pulses = [] := by
  have generated := programme_finite programme
  cases programme with
  | initialResidual before chemical failure => exact True.intro
  | chemicalResidual before first chemical failure => exact True.intro
  | cycled before first chemical second => exact List.length_eq_zero_iff.mp generated.2.1

theorem programme_positive_depth_fires (firstDepth secondDepth : Nat)
    (programme : Programme frame (firstDepth+1) (secondDepth+1)) :
    match programme with
    | .initialResidual _ _ _ => True
    | .chemicalResidual _ first _ _ => first.pulses ≠ []
    | .cycled _ first _ second => first.pulses ≠ [] ∧ second.pulses ≠ [] := by
  have generated := programme_finite programme
  cases programme with
  | initialResidual before chemical failure => exact True.intro
  | chemicalResidual before first chemical failure =>
    intro empty
    have impossible : 0 = firstDepth+1 := by simpa only [empty,List.length_nil] using generated.1
    omega
  | cycled before first chemical second =>
    constructor
    · intro empty
      have impossible : 0 = firstDepth+1 := by simpa only [empty,List.length_nil] using generated.1
      omega
    · intro empty
      have impossible : 0 = secondDepth+1 := by simpa only [empty,List.length_nil] using generated.2.1
      omega

private theorem programme_initial_rejection (cursor : SourceCursor frame) (failure : EntryFailure frame)
    (firstDepth : Nat) (input : Input) (secondDepth : Nat) :
    compileProgramme (.residual cursor failure) firstDepth input secondDepth =
      .initialResidual cursor (SourceCursor.next cursor input.1.1 input.1.2 input.2) failure := rfl

private theorem programme_chemical_rejection (before : Entered frame)
    (firstDepth : Nat) (input : Input) (secondDepth : Nat) (cursor : SourceCursor frame)
    (failure : EntryFailure frame)
    (rejected : reenter (renewEntered before firstDepth).after input = .residual cursor failure) :
    compileProgramme (.admitted before) firstDepth input secondDepth =
      .chemicalResidual before (renewEntered before firstDepth)
        (SourceCursor.next (renewEntered before firstDepth).after.cursor input.1.1 input.1.2 input.2) failure := by
  have same := reentry_same_value (renewEntered before firstDepth).after input
  rw [rejected] at same
  simp only [compileProgramme,rejected]
  rw [same]

private theorem initial_inlet_rejection (old : CPS1Deformation.Source.Occurrence frame)
    (generated : NativeSource.GatherStock old.current.stock)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (failure : InletFailure)
    (rejected : inlet (CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw) = .error failure) :
    enterStock old generated actions feed raw =
      .residual (SourceCursor.start (CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw))
        (.native (.inlet failure)) := by
  unfold enterStock
  dsimp only
  split
  · rename_i returned selected
    have failureSame := Except.error.inj (selected.symm.trans rejected)
    subst returned
    have native : activate (CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw) =
        .error (.inlet failure) := by simp only [activate,rejected]
    split
    · rename_i returned actual
      have failureSame := Except.error.inj (actual.symm.trans native)
      subst returned
      rfl
    · rename_i active actual
      cases native.symm.trans actual
  · rename_i source selected
    cases rejected.symm.trans selected

theorem chemical_native_rejection (before : Entered frame) (input : Input)
    (failure : CPS1ReactiveField.Carried.Failure frame)
    (rejected : advance before.active (chemicalCurrent before input) = .error failure) :
    reenter before input =
      .residual (SourceCursor.next before.cursor input.1.1 input.1.2 input.2) (.native failure) := by
  unfold reenter
  dsimp only
  split
  · rename_i returned actual
    have same := Except.error.inj (actual.symm.trans rejected)
    subst returned
    rfl
  · rename_i after actual
    cases rejected.symm.trans actual

theorem chemical_nonpositive_never_admitted (before : Entered frame) (input : Input)
    (after : Active frame) (actual : advance before.active (chemicalCurrent before input) = .ok after)
    (depleted : after.fields.reserve ≤ 0) :
    ¬ ∃ entry, reenter before input = .admitted entry := by
  intro ⟨entry,admitted⟩
  have same := reentry_same_value before input
  rw [admitted] at same
  have selected : (SourceCursor.next before.cursor input.1.1 input.1.2 input.2).native.active = some after := by
    have nativeActual := actual
    unfold chemicalCurrent at nativeActual
    rw [SourceCursor.next_native]
    simp only [nextCursor,before.held,← before.current,nativeActual,Except.toOption,Option.or]
  have activeSame : entry.active = after := Option.some.inj
    (entry.held.symm.trans ((congrArg (fun cursor : SourceCursor frame => cursor.native.active) same).trans selected))
  have positive : 0 < after.fields.reserve := activeSame ▸ entry.budget
  exact (not_lt_of_ge depleted) positive

theorem chemical_retained_stale (before : Entered frame) (input : Input)
    (failure : CPS1ReactiveField.Carried.Failure frame)
    (rejected : advance before.active (chemicalCurrent before input) = .error failure)
    (changed : chemicalCurrent before input ≠ before.active.source) :
    let cursor := SourceCursor.next before.cursor input.1.1 input.1.2 input.2
    cursor.native.active = some before.active ∧
    cursor.native.current = chemicalCurrent before input ∧
    CPS1ReactiveJointNuclear.step cursor = .error .staleActive := by
  have nativeRejected := rejected
  unfold chemicalCurrent at nativeRejected
  have held : (SourceCursor.next before.cursor input.1.1 input.1.2 input.2).native.active = some before.active := by
    rw [SourceCursor.next_native]
    simp only [nextCursor,before.held,← before.current,nativeRejected,Except.toOption,Option.or]
  have current : (SourceCursor.next before.cursor input.1.1 input.1.2 input.2).native.current =
      chemicalCurrent before input := by
    rw [SourceCursor.next_native]
    simp only [nextCursor,chemicalCurrent,← before.current]
  refine ⟨held,current,?_⟩
  unfold CPS1ReactiveJointNuclear.step
  split
  · rename_i absent
    cases absent.symm.trans held
  · rename_i active activeHeld
    have same := Option.some.inj (activeHeld.symm.trans held)
    subst active
    split
    · rfl
    · rename_i notStale
      have sourceSame := not_ne_iff.mp notStale
      exact False.elim (changed (current.symm.trans sourceSame.symm))

theorem source_programme_selected_laws
    (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (electronicActions : List CPS1ElectronicSource.Source.RawAction) (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (nuclearActions : List CPS1QuantumNuclear.Source.RawAction) (nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (followingActions : List CPS1Following.Source.RawAction) (followingFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (molecularActions : List CPS1MolecularFrame.Source.RawAction) (molecularFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (deformationActions : List CPS1Deformation.Source.RawAction) (deformationFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (firstDepth : Nat) (input : Input)
    (secondDepth : Nat)
    (output : Σ frame : CPS1Recycling.Frame, Programme frame firstDepth secondDepth)
    (selected : programmeFromSource edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed
      actions feed raw firstDepth input secondDepth = some output) :
    output.2.ChemicalNext input ∧ output.2.ActualRuns ∧ output.2.Finite ∧ output.2.Whole input := by
  have generated := programme_from_source_actual edits water additional path recycleFeed scanFeed bodyFeed depth
    oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
    followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed
    actions feed raw firstDepth input secondDepth
  rw [selected] at generated
  exact generated

theorem programme_from_source_stored_exact
    (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (electronicActions : List CPS1ElectronicSource.Source.RawAction) (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (nuclearActions : List CPS1QuantumNuclear.Source.RawAction) (nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (followingActions : List CPS1Following.Source.RawAction) (followingFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (molecularActions : List CPS1MolecularFrame.Source.RawAction) (molecularFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (deformationActions : List CPS1Deformation.Source.RawAction) (deformationFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (firstDepth : Nat) (input : Input)
    (secondDepth : Nat) :
    programmeFromSource edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed
      actions feed raw firstDepth input secondDepth =
    (CPS1Deformation.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed).map
      (fun old => (⟨old.1,programmeFromOld old.2 actions feed raw firstDepth input secondDepth⟩ :
        Σ frame : CPS1Recycling.Frame, Programme frame firstDepth secondDepth)) := by
  classical
  have entrySame : ∀ {nativeFrame : CPS1Recycling.Frame}
      (old : CPS1Deformation.Source.Occurrence nativeFrame)
      (generated : NativeSource.GatherStock old.current.stock),
      enterFromOld old actions feed raw = enterStock old generated actions feed raw := by
    intro nativeFrame old generated
    have original : ∀ source : Inlet (CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw),
        OriginalRows (⟨source,incomingReserve source-price source⟩ :
          Material (CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw)) := by
      intro source
      exact NativeSource.original_rows_from_stock _ generated
    unfold enterFromOld enterStock
    dsimp only
    repeat' first
      | contradiction
      | split
    all_goals
      try simp_all only [Except.ok.injEq,Except.error.injEq]
    all_goals
      subst_vars
      try simp_all only [Except.ok.injEq,Except.error.injEq]
    all_goals
      subst_vars
      first
      | contradiction
      | rfl
      | solve_by_elim [original]
      | (rename_i source1 selected1 germ1 born1 rows1 budget1 source2 selected2 active germ2 born2 budget2 native
         have sourceSame : source2 = source1 := Except.ok.inj (selected2.symm.trans selected1)
         subst source2
         have germSame : germ2 = germ1 := Except.ok.inj (born2.symm.trans born1)
         subst germ2
         rfl)
  have mapped : ∀
      (execution : Option (Σ nativeFrame : CPS1Recycling.Frame, CPS1Deformation.Source.Occurrence nativeFrame))
      (generated : ∀ source, execution = some source → NativeSource.GatherStock source.2.current.stock),
      programmeOfExecution execution generated actions feed raw firstDepth input secondDepth =
        execution.map (fun old => (⟨old.1,programmeFromOld old.2 actions feed raw firstDepth input secondDepth⟩ :
          Σ nativeFrame : CPS1Recycling.Frame, Programme nativeFrame firstDepth secondDepth)) := by
    intro execution generated
    cases execution with
    | none => rfl
    | some old =>
      change some (⟨old.1,compileProgramme (enterStock old.2 (generated old rfl) actions feed raw)
          firstDepth input secondDepth⟩ : Σ nativeFrame : CPS1Recycling.Frame,
          Programme nativeFrame firstDepth secondDepth) =
        some (⟨old.1,compileProgramme (enterFromOld old.2 actions feed raw) firstDepth input secondDepth⟩ :
          Σ nativeFrame : CPS1Recycling.Frame, Programme nativeFrame firstDepth secondDepth)
      rw [entrySame old.2 (generated old rfl)]
  exact mapped _ _

end
end CPS1ReactiveSourceEntry
