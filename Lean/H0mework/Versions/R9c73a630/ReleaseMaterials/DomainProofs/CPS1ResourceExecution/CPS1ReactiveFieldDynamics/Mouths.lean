import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Whole

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace CPS1ReactiveFieldDynamics
noncomputable section
variable {frame : CPS1Recycling.Frame}

theorem trace_endpoint (current final : NativeCursor frame) (pulses : List (Pulse frame))
    (trace : Trace current pulses final) (old after : NativeActive frame)
    (held : current.active = some old) (last : final.active = some after) :
    after.fields.account = old.fields.account ∧ after.fields.Ne = old.fields.Ne ∧
    after.body = old.body ∧ after.source = old.source ∧ after.paidRawReserve = old.paidRawReserve := by
  induction trace generalizing old after with
  | nil current =>
    have same := Option.some.inj (last.symm.trans held)
    subst after
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | cons current next final pulse rest actual _ ih =>
    have generated := step_generated current next pulse actual
    have same := Option.some.inj (generated.1.symm.trans held)
    subst old
    have tail := ih pulse.after after generated.2.2.1 last
    have paid := pulse_paid pulse generated.2.2.2.2.2.1
    exact ⟨tail.1.trans paid.2.2.1,tail.2.1.trans paid.2.2.2.1,
      tail.2.2.1.trans generated.2.2.2.2.2.1.2.2.2.1,
      tail.2.2.2.1.trans generated.2.2.2.2.2.1.2.2.1,
      tail.2.2.2.2.trans generated.2.2.2.2.2.1.2.2.2.2⟩

theorem renew_endpoint (current : NativeCursor frame) (depth : Nat) (ready : Ready current) :
    ∃ old after, current.active = some old ∧ (renew current depth).cursor.active = some after ∧
      0 < after.fields.reserve ∧ after.fields.Good ∧
      after.fields.account = old.fields.account ∧ after.fields.Ne = old.fields.Ne ∧
      after.body = old.body ∧ after.source = old.source ∧ after.paidRawReserve = old.paidRawReserve := by
  have generated := renew_ready current depth ready
  obtain ⟨old,held,_,_⟩ := ready
  obtain ⟨after,last,_,margin⟩ := generated.2.2.2
  exact ⟨old,after,held,last,margin,after.good,
    trace_endpoint current _ _ (renew_trace current depth) old after held last⟩

theorem renew_original_stages (current : NativeCursor frame) (depth : Nat)
    (valid : ∀ entry ∈ current.stages, entry.Valid) :
    ∀ entry ∈ (renew current depth).cursor.stages, entry.Valid := by
  rw [(renew_whole current depth).2.1]
  exact valid

theorem continue_original_stages (current : NativeCursor frame) (depth : Nat)
    (inputs : List CPS1ReactiveField.Carried.Input) (valid : ∀ entry ∈ current.stages, entry.Valid) :
    ∀ entry ∈ (continueChemical current depth inputs).cursor.stages, entry.Valid := by
  obtain ⟨generated,whole,paid⟩ := CPS1ReactiveField.Carried.advance_all_generated_stages
    (renew current depth).cursor inputs
  change ∀ entry ∈ (CPS1ReactiveField.Carried.advanceAll (renew current depth).cursor inputs).stages, entry.Valid
  rw [whole]
  intro entry held
  rcases List.mem_append.mp held with old | new
  · exact renew_original_stages current depth valid entry old
  · exact paid entry new

open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
variable (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
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
  (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) (raw : List CPS1AddressedReactiveJoint.Rows.RawAction)
  (pulseDepth : Nat)

theorem from_source_old :
    (fromSourceWhole edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
      electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
      molecularFeed deformationActions deformationFeed actions feed raw pulseDepth).map
      (fun generated => ⟨generated.1,generated.2.cursor.current.old⟩) =
    CPS1Deformation.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
      electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
      molecularFeed deformationActions deformationFeed := by
  have exactOld := CPS1ReactiveField.FinitePresentation.from_source_old edits water additional path recycleFeed
    scanFeed bodyFeed depth oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
    followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed actions feed raw
  refine Eq.trans ?_ exactOld
  unfold fromSourceWhole fromSourceNative CPS1ReactiveField.FinitePresentation.fromSourceWhole
  cases actual : CPS1ReactiveField.Carried.fromSource edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed actions feed raw with
  | none => rfl
  | some source =>
    change (some ⟨source.1,(renew source.2 pulseDepth).cursor.current.old⟩ :
      Option (Σ frame : CPS1Recycling.Frame, CPS1Deformation.Source.Occurrence frame)) =
        some ⟨source.1,source.2.current.old⟩
    exact congrArg (fun current : CPS1ReactiveField.Occurrence source.1 =>
      (some ⟨source.1,current.old⟩ : Option (Σ frame : CPS1Recycling.Frame, CPS1Deformation.Source.Occurrence frame)))
      (renew_whole source.2 pulseDepth).1

theorem source_complete :
    ∀ generated ∈ (fromSourceWhole edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
      electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
      molecularFeed deformationActions deformationFeed actions feed raw pulseDepth).toList,
      (∀ pulse ∈ generated.2.pulses, pulse.NativeValid) ∧
      (∀ entry ∈ generated.2.cursor.stages, entry.NativeValid) := by
  unfold fromSourceWhole fromSourceNative CPS1ReactiveField.Carried.fromSource
  cases original : CPS1ReactiveField.fromSource edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed
      molecularActions molecularFeed deformationActions deformationFeed actions feed raw with
  | none => intro generated held; cases held
  | some source =>
    intro generated held
    have same : generated = ⟨source.1,Presentation.whole (renew (CPS1ReactiveField.Carried.startCursor source.2) pulseDepth)⟩ := by
      simpa only [Option.map_some,Option.toList_some,List.mem_singleton] using held
    subst generated
    refine ⟨(Presentation.renew_whole_native _ _).2.2,?_⟩
    intro entry held
    rcases List.mem_map.mp held with ⟨native,member,rfl⟩
    exact ⟨native,rfl,renew_original_stages _ _
      (CPS1ReactiveField.FinitePresentation.initial_stages_valid source.2) native member⟩

theorem advance_complete (inputs : List CPS1ReactiveField.Carried.Input) :
    ∀ generated ∈ (advanceFromSourceWhole edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
      electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
      molecularFeed deformationActions deformationFeed actions feed raw pulseDepth inputs).toList,
      (∀ pulse ∈ generated.2.pulses, pulse.NativeValid) ∧
      (∀ entry ∈ generated.2.cursor.stages, entry.NativeValid) := by
  unfold advanceFromSourceWhole fromSourceNative CPS1ReactiveField.Carried.fromSource
  cases original : CPS1ReactiveField.fromSource edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed
      molecularActions molecularFeed deformationActions deformationFeed actions feed raw with
  | none => intro generated held; cases held
  | some source =>
    intro generated held
    have same : generated = ⟨source.1,Presentation.whole
        { (renew (CPS1ReactiveField.Carried.startCursor source.2) pulseDepth) with
          cursor := (CPS1ReactiveField.Carried.advanceAll
            (renew (CPS1ReactiveField.Carried.startCursor source.2) pulseDepth).cursor inputs) }⟩ := by
      simpa only [Option.map_some,Option.toList_some,List.mem_singleton] using held
    subst generated
    refine ⟨(Presentation.renew_whole_native _ _).2.2,?_⟩
    intro entry held
    rcases List.mem_map.mp held with ⟨native,member,rfl⟩
    exact ⟨native,rfl,continue_original_stages _ _ inputs
      (CPS1ReactiveField.FinitePresentation.initial_stages_valid source.2) native member⟩

end
end CPS1ReactiveFieldDynamics
