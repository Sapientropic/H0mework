import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.Closure
import H0mework.Versions.R2.Realization.Faces.ProjectionCoface

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

/-- The material at the generated next reproduces every Supply parent
material verbatim (same reads of the parent runtime) and additionally
carries the executed-delivery account, the typed delivery residuals and the
paid next-round delivery capability. -/
structure Material where
  inputs : Root.InputMaterial
  sequence : Root.SequenceMaterial
  experiment : Root.ExperimentMaterial
  response : Root.ResponseMaterial
  originalAlleles : List Ngs.Allele
  reference : Bases
  caption : String
  provenance : String × String × String
  generatedCoding : Fin 17 → Bases
  consumers : Fin 17 → (Bool × Bool) × Option (List String)
  shownReads : Nat
  originalQReads : Nat
  a8Reads : Nat
  openFrameReads : Nat
  maintenance : Longitudinal.LongitudinalMaintenance
  capability : Longitudinal.NextRoundCapability
  formulation : Longitudinal.FormulationAccount
  residuals : Longitudinal.Residuals
  supply : Supply.SupplyAccount
  delivery : Supply.PhysicalDelivery
  supplyResiduals : Supply.SupplyResiduals
  supplyCapability : Supply.SupplyCapability
  deliveryAccount : DeliveryAccount
  deliveryResiduals : DeliveryResiduals
  deliveryCapability : DeliveryCapability
  resourcePlan : CPS1ResourceExecution.Program.Plan
  editingPrograms : Target.Edits → CPS1Deamination.Source.Compilation
  editingExecution : Target.Edits → Nat → CPS1ResourceExecution.Execution
  editingContinuation : Target.Edits → Nat → Nat → CPS1ResourceExecution.Execution
  continuedCoding : Target.Edits → Nat → Nat → Option Bases
  continuedStopChain : Target.Edits → Nat → Nat → Option (List String)
  endogenousPlan : Target.Edits → Nat → Nat → Option CPS1ResourceExecution.Program.Plan
  endogenousCharging : Target.Edits → Nat → Nat → CPS1ResourceExecution.Stock →
    Option CPS1ResourceExecution.Execution
  endogenousElongation : Target.Edits → Nat → Nat → CPS1ResourceExecution.Stock →
    Option CPS1ResourceExecution.Execution
  boundaryProgram : Target.Edits → Nat → Nat → Option (List CPS1ResourceExecution.Reaction)
  boundaryExecution : Target.Edits → Nat → Nat → CPS1ResourceExecution.Stock →
    Option CPS1ResourceExecution.Execution
  boundaryRawFuel : Target.Edits → Nat → Nat → Option CPS1ResourceExecution.Stock
  recyclingFrame : Target.Edits → Nat → Nat → Option CPS1Recycling.Frame
  recyclingEvents : CPS1Recycling.SplitSite → List CPS1Recycling.RawEvent
  recyclingFreshFuel : List CPS1Recycling.RawMaterial
  recyclingExecution : Target.Edits → Nat → Nat → List CPS1Recycling.RawEvent →
    List CPS1Recycling.RawMaterial → Option (Σ frame : CPS1Recycling.Frame, CPS1Recycling.ExecutionAt frame)
  reinitiationRna : RegisteredRna
  reinitiationExecution : Target.Edits → Nat → Nat → CPS1Recycling.SplitSite →
    List CPS1Recycling.RawMaterial → List CPS1Reinitiation.RawMaterial →
      Option (Σ frame : CPS1Recycling.Frame, CPS1Reinitiation.Execution frame)
  cycleProgram : CPS1Recycling.SplitSite → Option (List CPS1Reinitiation.Handover.Reaction)
  cycleExecution : Target.Edits → Nat → Nat → CPS1Recycling.SplitSite →
    List CPS1Recycling.RawMaterial → List CPS1Reinitiation.RawMaterial →
      List CPS1Reinitiation.Handover.RawMaterial →
        Option (Σ frame : CPS1Recycling.Frame, CPS1Reinitiation.Handover.Execution frame)
  cycleRawFuel : Option (List CPS1Reinitiation.Handover.RawMaterial)
  stockRecursionExecution : Target.Edits → Nat → Nat → CPS1Recycling.SplitSite →
    List CPS1Recycling.RawMaterial → List CPS1Reinitiation.RawMaterial →
      List CPS1Reinitiation.Handover.RawMaterial → List (List CPS1StockRecursion.Dictionary.RawMaterial) →
        Option (Σ frame : CPS1Recycling.Frame, CPS1StockRecursion.Source.Observation frame)
  stockRecursionRequested : Target.Edits → Nat → Nat → CPS1Recycling.SplitSite →
    List CPS1Recycling.RawMaterial → List CPS1Reinitiation.RawMaterial →
      List CPS1Reinitiation.Handover.RawMaterial → Nat →
        Option (Σ frame : CPS1Recycling.Frame, CPS1StockRecursion.Source.Observation frame)
  stockRecursionRawFuel : List CPS1StockRecursion.Dictionary.RawMaterial
  stockRecursionProgram : CPS1Recycling.SplitSite → List CPS1StockRecursion.Dictionary.Reaction
  localChemicalExecution : type_of% CPS1LocalChemicalExecution.Source.execution
  localChemicalCapture : type_of% CPS1LocalChemicalExecution.Source.actualCapture
  localChemicalMaterial : type_of% CPS1LocalChemicalExecution.Source.RawMaterial.species
  localChemicalProgram : type_of% CPS1LocalChemicalExecution.Source.localProgram
  localChemicalAdvance : type_of% CPS1LocalChemicalExecution.Source.advance
  editingChemicalExecution : type_of% CPS1EditingChemicalJoin.Source.execution
  editingChemicalAdvance : type_of% CPS1EditingChemicalJoin.Source.advance
  editingChemicalFuel : List CPS1EditingChemicalJoin.Source.RawMaterial
  editingChemicalCycles : type_of% CPS1EditingChemicalJoin.Continuation.cycles
  atomicSourceExecution : type_of% CPS1AtomicSource.Current.execution
  atomicSourceLocalExecution : type_of% CPS1AtomicSource.Current.sourceExecution
  atomicSourceAdvance : type_of% CPS1AtomicSource.Current.advance
  atomicSourceGraph : type_of% CPS1AtomicSource.Current.graph
  atomicSourceProtons : type_of% CPS1AtomicSource.Graph.requiredProtons
  atomicDynamicsExecution : type_of% CPS1AtomicDynamics.Source.execution
  atomicDynamicsResume : type_of% CPS1AtomicDynamics.Source.resume
  atomicDynamicsMaterial : type_of% CPS1AtomicDynamics.Source.RawAction.material
  atomicDynamicsPulse : type_of% CPS1AtomicDynamics.Body.pulse?
  atomicDynamicsForce : type_of% CPS1AtomicDynamics.Body.force
  atomicDynamicsEnergy : type_of% CPS1AtomicDynamics.Body.energy
  enzymeBathExecution : type_of% CPS1EnzymeBath.Source.execution
  enzymeBathGeneratedExecution : type_of% CPS1EnzymeBath.Source.generatedExecution
  enzymeBathResume : type_of% CPS1EnzymeBath.Source.resume
  enzymeBathTemplate : type_of% CPS1EnzymeBath.Primary.template
  enzymeBathParticles : type_of% CPS1EnzymeBath.Joint.particles
  enzymeBathPulse : type_of% CPS1EnzymeBath.Joint.pulse?
  electronicExecution : type_of% CPS1ElectronicSource.Source.execution
  electronicResume : type_of% CPS1ElectronicSource.Source.resume
  electronicMaterial : type_of% CPS1ElectronicSource.Source.RawAction.material
  electronicHamiltonian : type_of% @CPS1ElectronicSource.State.hamiltonian
  electronicEnergy : type_of% @CPS1ElectronicSource.State.energy
  electronicAction : type_of% @CPS1ElectronicSource.continuousAction
  quantumNuclearExecution : type_of% @CPS1QuantumNuclear.Source.execution
  quantumNuclearResume : type_of% @CPS1QuantumNuclear.Source.resume
  quantumNuclearMaterial : type_of% @CPS1QuantumNuclear.Source.RawAction.material
  quantumNuclearPulse : type_of% @CPS1QuantumNuclear.pulse?
  quantumNuclearForce : type_of% @CPS1QuantumNuclear.nuclearForce
  quantumNuclearEnergy : type_of% @CPS1QuantumNuclear.spatialEnergyAt
  followingExecution : type_of% @CPS1Following.Source.execution
  followingResume : type_of% @CPS1Following.Source.resume
  followingMaterial : type_of% @CPS1Following.Source.RawAction.material
  followingRelocate : type_of% @CPS1Following.relocate?
  followingPulse : type_of% @CPS1Following.pulse?
  followingForce : type_of% @CPS1Following.nuclearForce
  followingEnergy : type_of% @CPS1Following.energy
  followingFields : type_of% @CPS1Following.currentFields
  followingAction : type_of% @CPS1Following.currentAction
  molecularExecution : type_of% @CPS1MolecularFrame.Source.execution
  molecularResume : type_of% @CPS1MolecularFrame.Source.resume
  molecularMaterial : type_of% @CPS1MolecularFrame.Source.RawAction.material
  molecularAdopt : type_of% @CPS1MolecularFrame.adopt?
  molecularPulse : type_of% @CPS1MolecularFrame.Material.pulse?
  molecularDeposit : type_of% @CPS1MolecularFrame.Material.deposit?
  molecularEnergy : type_of% @CPS1MolecularFrame.Material.energy
  molecularFields : type_of% @CPS1MolecularFrame.Material.currentFields
  molecularAction : type_of% @CPS1MolecularFrame.Material.action
  deformationExecution : type_of% @CPS1Deformation.Source.execution
  deformationResume : type_of% @CPS1Deformation.Source.resume
  deformationMaterial : type_of% @CPS1Deformation.Source.RawAction.material
  deformationAdopt : type_of% @CPS1Deformation.adopt?
  deformationPulse : type_of% @CPS1Deformation.Material.pulse?
  deformationDeposit : type_of% @CPS1Deformation.Material.deposit?
  deformationEnergy : type_of% @CPS1Deformation.Material.energy
  deformationFields : type_of% @CPS1Deformation.Material.currentFields
  deformationForce : type_of% @CPS1Deformation.Material.jointForce
  deformationAction : type_of% @CPS1Deformation.Material.action
  deformationJoint : type_of% @CPS1Deformation.Material.currentJoint
  positivePulse : type_of% @CPS1PositivePulse.NativeSource.autoPulse?
  positiveNext : type_of% @CPS1PositivePulse.NativeSource.next
  continuationRun : type_of% @CPS1PositiveContinuation.NativeSource.autoContinue?
  continuationNext : type_of% @CPS1PositiveContinuation.NativeSource.next
  addressedTransfer : type_of% @CPS1AddressedTransfer.NativeSource.autoTransfer?
  addressedNext : type_of% @CPS1AddressedTransfer.NativeSource.next
  addressedContinue : type_of% @CPS1AddressedRenewal.NativeSource.autoContinue?
  addressedContinueNext : type_of% @CPS1AddressedRenewal.NativeSource.next
  jointContinue : type_of% @CPS1AddressedBondRenewal.NativeSource.autoContinue?
  jointContinueNext : type_of% @CPS1AddressedBondRenewal.NativeSource.next
  interactionChannel : type_of% @CPS1AddressedInteraction.currentChannel?
  pairCurrent : type_of% @CPS1AddressedCurrentPair.currentPair?
  sourceMaterialFromSource : type_of% @CPS1AddressedChemicalReaction.Source.fromSource
  sourceMaterialNext : type_of% @CPS1AddressedChemicalReaction.Source.next
  sourceMaterialRequested : type_of% @CPS1AddressedChemicalReaction.Source.requested
  hydrolysisFromCurrent : type_of% @CPS1AddressedHydrolysis.fromCurrent
  atomicStart : type_of% @CPS1AddressedHydrolysis.Atomic.start
  atomicNext : type_of% @CPS1AddressedHydrolysis.Atomic.next
  atomicRequested : type_of% @CPS1AddressedHydrolysis.Atomic.requested
  atomicAdvanceAll : type_of% @CPS1AddressedHydrolysis.Atomic.advanceAll
  atomicFromSource : type_of% @CPS1AddressedHydrolysis.Atomic.fromSource
  reactiveStart : type_of% @CPS1AddressedReactiveJoint.start
  reactiveNext : type_of% @CPS1AddressedReactiveJoint.next
  reactiveFromSource : type_of% @CPS1AddressedReactiveJoint.fromSource
  reactiveAdvanceAll : type_of% @CPS1AddressedReactiveJoint.advanceAll
  reactiveAdmission : type_of% @CPS1AddressedReactiveJoint.admission
  fieldFromSourceWhole : type_of% @CPS1ReactiveField.FinitePresentation.fromSourceWhole
  fieldAdvanceFromSourceWhole : type_of% @CPS1ReactiveField.FinitePresentation.advanceFromSourceWhole
  fieldDynamicsFromSourceWhole : type_of% @CPS1ReactiveFieldDynamics.fromSourceWhole
  fieldDynamicsAdvanceFromSourceWhole : type_of% @CPS1ReactiveFieldDynamics.advanceFromSourceWhole

-- Complete native outputs are method results; the stored source input keeps Material in Type.
noncomputable def Material.nuclearFromSource (self : Material) (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
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
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (pulseDepth : Nat) :
    Option (Σ frame : CPS1Recycling.Frame, CPS1ReactiveNuclear.SourceCursor.Run frame) :=
  match self.deformationExecution edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed with
  | none => none
  | some old => some ⟨old.1,CPS1ReactiveNuclear.SourceCursor.renew
      (CPS1ReactiveNuclear.SourceCursor.start
        (CPS1ReactiveField.next (CPS1ReactiveField.start old.2) actions feed raw)) pulseDepth⟩

noncomputable def Material.nuclearAdvanceFromSource (self : Material) (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
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
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (pulseDepth : Nat)
    (inputs : List CPS1ReactiveField.Carried.Input) :
    Option (Σ frame : CPS1Recycling.Frame, CPS1ReactiveNuclear.SourceCursor.Run frame) :=
  (self.nuclearFromSource edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed actions feed raw pulseDepth).map (fun current =>
    ⟨current.1,{current.2 with cursor := CPS1ReactiveNuclear.SourceCursor.advanceAll current.2.cursor inputs}⟩)

noncomputable def Material.jointNuclearFromSource (self : Material) (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
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
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (pulseDepth : Nat) :
    Option (Σ frame : CPS1Recycling.Frame, CPS1ReactiveJointNuclear.Run frame) :=
  match self.deformationExecution edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed with
  | none => none
  | some old => some ⟨old.1,CPS1ReactiveJointNuclear.fromOld old.2 actions feed raw pulseDepth⟩

noncomputable def Material.jointNuclearAdvanceFromSource (self : Material) (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
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
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (pulseDepth : Nat)
    (inputs : List CPS1ReactiveField.Carried.Input) :
    Option (Σ frame : CPS1Recycling.Frame, CPS1ReactiveJointNuclear.Run frame) :=
  (self.jointNuclearFromSource edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed actions feed raw pulseDepth).map (fun current =>
    ⟨current.1,{current.2 with cursor := CPS1ReactiveNuclear.SourceCursor.advanceAll current.2.cursor inputs}⟩)

noncomputable def material : Material :=
  ⟨(Supply.readMaterial parentRuntime).inputs,(Supply.readMaterial parentRuntime).sequence,
    (Supply.readMaterial parentRuntime).experiment,(Supply.readMaterial parentRuntime).response,
    (Supply.readMaterial parentRuntime).originalAlleles,(Supply.readMaterial parentRuntime).reference,
    (Supply.readMaterial parentRuntime).caption,(Supply.readMaterial parentRuntime).provenance,
    (Supply.readMaterial parentRuntime).generatedCoding,(Supply.readMaterial parentRuntime).consumers,
    (Supply.readMaterial parentRuntime).shownReads,(Supply.readMaterial parentRuntime).originalQReads,
    (Supply.readMaterial parentRuntime).a8Reads,(Supply.readMaterial parentRuntime).openFrameReads,
    (Supply.readMaterial parentRuntime).maintenance,(Supply.readMaterial parentRuntime).capability,
    (Supply.readMaterial parentRuntime).formulation,(Supply.readMaterial parentRuntime).residuals,
    (Supply.readMaterial parentRuntime).supply,(Supply.readMaterial parentRuntime).delivery,
    (Supply.readMaterial parentRuntime).supplyResiduals,(Supply.readMaterial parentRuntime).supplyCapability,
    Source.deliveryAccount,Source.deliveryResiduals,Source.deliveryCapability,
    CPS1ResourceExecution.Program.originalPlan,CPS1Deamination.Source.sourceProgram,
    CPS1Deamination.ExecutionReadout.sourceExecution,
    CPS1Deamination.Continuation.sourceContinuation,
    CPS1Deamination.ContinuedCoding.continuedCoding,
    CPS1Deamination.ContinuedCoding.continuedStopChain,
    CPS1EndogenousTranslation.continuedPlan,CPS1EndogenousTranslation.actualCharging,
    CPS1EndogenousTranslation.actualElongation,
    CPS1InitiationTermination.UnifiedBoundary.sourceProgram,
    CPS1InitiationTermination.UnifiedBoundary.sourceExecution,
    CPS1InitiationTermination.Source.rawSourceFuel,
    CPS1Recycling.sourceFrame,CPS1Recycling.productiveEvents,CPS1Recycling.freshFuel,
    CPS1Recycling.Source.execution,Molecules.mrna,CPS1Reinitiation.Source.execution,
    (fun path => CPS1Reinitiation.Handover.programFromRna? path Source.rawMrna),
    CPS1Reinitiation.Handover.Source.execution,CPS1Reinitiation.Handover.Source.rawSourceFuel,
    CPS1StockRecursion.Source.actualObservation,CPS1StockRecursion.Source.actualRequested,
    CPS1StockRecursion.Source.rawSourceFuel,CPS1StockRecursion.Source.program,
    CPS1LocalChemicalExecution.Source.execution,CPS1LocalChemicalExecution.Source.actualCapture,
    CPS1LocalChemicalExecution.Source.RawMaterial.species,CPS1LocalChemicalExecution.Source.localProgram,
    CPS1LocalChemicalExecution.Source.advance,
    CPS1EditingChemicalJoin.Source.execution,CPS1EditingChemicalJoin.Source.advance,
    CPS1EditingChemicalJoin.Source.rawFuel,CPS1EditingChemicalJoin.Continuation.cycles,
    CPS1AtomicSource.Current.execution,CPS1AtomicSource.Current.sourceExecution,
    CPS1AtomicSource.Current.advance,CPS1AtomicSource.Current.graph,CPS1AtomicSource.Graph.requiredProtons,
    CPS1AtomicDynamics.Source.execution,
    CPS1AtomicDynamics.Source.resume,
    CPS1AtomicDynamics.Source.RawAction.material,
    CPS1AtomicDynamics.Body.pulse?,
    CPS1AtomicDynamics.Body.force,
    CPS1AtomicDynamics.Body.energy,
    CPS1EnzymeBath.Source.execution,
    CPS1EnzymeBath.Source.generatedExecution,
    CPS1EnzymeBath.Source.resume,
    CPS1EnzymeBath.Primary.template,
    CPS1EnzymeBath.Joint.particles,
    CPS1EnzymeBath.Joint.pulse?,
    CPS1ElectronicSource.Source.execution,
    CPS1ElectronicSource.Source.resume,
    CPS1ElectronicSource.Source.RawAction.material,
    CPS1ElectronicSource.State.hamiltonian,
    CPS1ElectronicSource.State.energy,
    CPS1ElectronicSource.continuousAction,
    @CPS1QuantumNuclear.Source.execution,
    @CPS1QuantumNuclear.Source.resume,
    @CPS1QuantumNuclear.Source.RawAction.material,
    @CPS1QuantumNuclear.pulse?,
    @CPS1QuantumNuclear.nuclearForce,
    @CPS1QuantumNuclear.spatialEnergyAt,
    @CPS1Following.Source.execution,
    @CPS1Following.Source.resume,
    @CPS1Following.Source.RawAction.material,
    @CPS1Following.relocate?,
    @CPS1Following.pulse?,
    @CPS1Following.nuclearForce,
    @CPS1Following.energy,
    @CPS1Following.currentFields,
    @CPS1Following.currentAction,
    @CPS1MolecularFrame.Source.execution,
    @CPS1MolecularFrame.Source.resume,
    @CPS1MolecularFrame.Source.RawAction.material,
    @CPS1MolecularFrame.adopt?,
    @CPS1MolecularFrame.Material.pulse?,
    @CPS1MolecularFrame.Material.deposit?,
    @CPS1MolecularFrame.Material.energy,
    @CPS1MolecularFrame.Material.currentFields,
    @CPS1MolecularFrame.Material.action,
    @CPS1Deformation.Source.execution,
    @CPS1Deformation.Source.resume,
    @CPS1Deformation.Source.RawAction.material,
    @CPS1Deformation.adopt?,
    @CPS1Deformation.Material.pulse?,
    @CPS1Deformation.Material.deposit?,
    @CPS1Deformation.Material.energy,
    @CPS1Deformation.Material.currentFields,
    @CPS1Deformation.Material.jointForce,
    @CPS1Deformation.Material.action,
    @CPS1Deformation.Material.currentJoint,
    @CPS1PositivePulse.NativeSource.autoPulse?,
    @CPS1PositivePulse.NativeSource.next,
    @CPS1PositiveContinuation.NativeSource.autoContinue?,
    @CPS1PositiveContinuation.NativeSource.next,
    @CPS1AddressedTransfer.NativeSource.autoTransfer?,
    @CPS1AddressedTransfer.NativeSource.next,
    @CPS1AddressedRenewal.NativeSource.autoContinue?,
    @CPS1AddressedRenewal.NativeSource.next,
    @CPS1AddressedBondRenewal.NativeSource.autoContinue?,
    @CPS1AddressedBondRenewal.NativeSource.next,
    @CPS1AddressedInteraction.currentChannel?,
    @CPS1AddressedCurrentPair.currentPair?,
    @CPS1AddressedChemicalReaction.Source.fromSource,
    @CPS1AddressedChemicalReaction.Source.next,
    @CPS1AddressedChemicalReaction.Source.requested,
    @CPS1AddressedHydrolysis.fromCurrent,
    @CPS1AddressedHydrolysis.Atomic.start,
    @CPS1AddressedHydrolysis.Atomic.next,
    @CPS1AddressedHydrolysis.Atomic.requested,
    @CPS1AddressedHydrolysis.Atomic.advanceAll,
    @CPS1AddressedHydrolysis.Atomic.fromSource,
    @CPS1AddressedReactiveJoint.start,
    @CPS1AddressedReactiveJoint.next,
    @CPS1AddressedReactiveJoint.fromSource,
    @CPS1AddressedReactiveJoint.advanceAll,
    @CPS1AddressedReactiveJoint.admission,
    @CPS1ReactiveField.FinitePresentation.fromSourceWhole,
    @CPS1ReactiveField.FinitePresentation.advanceFromSourceWhole,
    @CPS1ReactiveFieldDynamics.fromSourceWhole,
    @CPS1ReactiveFieldDynamics.advanceFromSourceWhole⟩

inductive Projection | material | certificate deriving DecidableEq, Repr

noncomputable def projectionLaw : SourceNativeProjectionLaw ParentLedger where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun face {_} occurrence _ => match face with
    | .material => SourceNativeLedgerEvolutionAt ParentLedger.source occurrence × Material
    | .certificate => PLift DeliveryClosure
  project := by
    intro face current occurrence active
    cases face with
    | material => exact (ParentLedger.ledgerCompiler.compile occurrence,material)
    | certificate => exact ⟨sourceGeneratedActualDelivery⟩

noncomputable def authoritySource := ParentBase.withProjectionCoface projectionLaw

noncomputable def componentInstallation :
    SourceNativeProjectionLaw.InstallationAt projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface ParentBase projectionLaw

noncomputable def inheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt ParentBase.projectionLaw authoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface ParentBase projectionLaw

noncomputable def authoritativeRoot : SourceNativeAuthoritativeRootClosure ParentN ParentV where
  source := authoritySource
  emitted := Supply.authoritativeRoot.emitted
  compiler_commutes := Supply.authoritativeRoot.compiler_commutes

noncomputable def livingRoot : SourceNativeLivingRootClosure ParentN ParentV :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem same_source_and_complete_ledger :
    authoritySource.restructuringSource = ParentBase.restructuringSource ∧
    authoritySource.eventInventoryAdmission = ParentBase.eventInventoryAdmission ∧
    authoritySource.lawSurface = ParentBase.lawSurface ∧
    (∀ current, authoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      Supply.authoritativeRoot.toLedgerRoot.generatedLedgerAt current) := ⟨rfl,rfl,rfl,fun _ => rfl⟩

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery
