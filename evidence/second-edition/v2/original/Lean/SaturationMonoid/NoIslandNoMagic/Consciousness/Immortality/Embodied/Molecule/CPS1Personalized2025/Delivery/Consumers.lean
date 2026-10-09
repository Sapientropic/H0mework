import SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.NativeIncidenceConsumers
import SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.PhosphorylExchangeConsumers
import SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.SameEventFunctionConsumers
import SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.BiologicalConsumers
import SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.ReactiveSourceEntryConsumers
import SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.ReactiveJointNuclearConsumers

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

theorem actual_original_operation (runtime : LivingRuntimeState process) :
    Root.OperationAt (Root.Native.erase runtime.current.visit.current) := runtime.emittedOccurrence.2.operation

theorem actual_resource_program (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    CPS1ResourceExecution.Program.planFromRna? (readMaterial runtime).inputs.mrnaNotation =
      some (readMaterial runtime).resourcePlan ∧
    CPS1ResourceExecution.ResourceContract (readMaterial runtime).resourcePlan ∧
    (readMaterial runtime.tick.next).resourcePlan = (readMaterial runtime).resourcePlan := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate), same_source_and_complete_ledger, ?_, ?_, rfl⟩
  · exact (readCertificate runtime).resourceProgram.sourceGenerated
  · exact (readCertificate runtime).resourceProgram.resources

theorem actual_editing_program (runtime : LivingRuntimeState process) (edits : Target.Edits) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).editingPrograms edits = CPS1Deamination.Source.sourceProgram edits ∧
    CPS1Deamination.Source.originalMinusAligned =
      ((readMaterial runtime).sequence.genomic ⟨false,false,false⟩).map CPS1Deamination.Base.ofOpposite ∧
    CPS1Deamination.EditingContract edits ∧
    CPS1Deamination.Source.plusReadout ((readMaterial runtime).editingPrograms edits).word =
      (readMaterial runtime).sequence.genomic edits ∧
    (readMaterial runtime.tick.next).editingPrograms edits = (readMaterial runtime).editingPrograms edits := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate), same_source_and_complete_ledger,
    rfl, rfl, ?_, ?_, rfl⟩
  · exact (readCertificate runtime).editing edits
  · exact ((readCertificate runtime).editing edits).recognition

theorem actual_editing_execution (runtime : LivingRuntimeState process) (edits : Target.Edits)
    (water : Nat) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).editingExecution edits water =
      CPS1ResourceExecution.execute ((readMaterial runtime).editingPrograms edits).reactions
        (CPS1Deamination.modelStock water) ∧
    type_of% (CPS1Deamination.ExecutionReadout.source_prefix_actual_readout edits water) ∧
    (∀ enough : ((readMaterial runtime).editingPrograms edits).steps.length ≤ water,
      type_of% (CPS1Deamination.ExecutionReadout.source_complete_actual_readout
        edits.third edits.eighth edits.ninth water enough)) ∧
    (readMaterial runtime.tick.next).editingExecution edits water =
      (readMaterial runtime).editingExecution edits water := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate), same_source_and_complete_ledger,
    rfl, ?_, ?_, rfl⟩
  · exact (readCertificate runtime).nativeEditing.prefixReadout edits water
  · intro enough
    exact (readCertificate runtime).nativeEditing.completeReadout
      edits.third edits.eighth edits.ninth water enough

theorem actual_continued_coding (runtime : LivingRuntimeState process) (edits : Target.Edits)
    (water additional : Nat) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).editingContinuation edits water additional =
      CPS1ResourceExecution.execute ((readMaterial runtime).editingExecution edits water).remaining
        (CPS1Deamination.Continuation.refillWater
          ((readMaterial runtime).editingExecution edits water).stock additional) ∧
    type_of% (CPS1Deamination.Continuation.source_continuation_update edits water additional) ∧
    type_of% (CPS1Deamination.Continuation.source_continuation_actual_readout edits water additional) ∧
    (readMaterial runtime).continuedCoding edits water additional =
      (CPS1Deamination.ExecutionReadout.readDNA
        ((readMaterial runtime).editingContinuation edits water additional).stock).map
        (CPS1Deamination.CodingReadout.codingFromGenomic ∘ CPS1Deamination.Source.plusReadout) ∧
    (readMaterial runtime).continuedStopChain edits water additional =
      some (if CPS1Deamination.CodingReadout.paidEighth edits (water+additional) then
        Source.referenceProtein ++ ["*"] else Source.referenceProtein.take 334 ++ ["*"]) ∧
    (readMaterial runtime.tick.next).editingContinuation edits water additional =
      (readMaterial runtime).editingContinuation edits water additional ∧
    (readMaterial runtime.tick.next).continuedCoding edits water additional =
      (readMaterial runtime).continuedCoding edits water additional := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate), same_source_and_complete_ledger,
    rfl, ?_, ?_, rfl, ?_, rfl, rfl⟩
  · exact (readCertificate runtime).continuedCoding.continuation edits water additional
  · exact (readCertificate runtime).continuedCoding.actualReadout edits water additional
  · exact (readCertificate runtime).continuedCoding.firstStop edits water additional

theorem actual_endogenous_translation (runtime : LivingRuntimeState process) (edits : Target.Edits)
    (water additional : Nat) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).endogenousPlan edits water additional =
      ((readMaterial runtime).continuedCoding edits water additional).bind
        (fun coding => (CPS1EndogenousTranslation.peptideFromCoding? coding).map
          CPS1ResourceExecution.Program.compile) ∧
    (readMaterial runtime).endogenousPlan edits water additional =
      some (CPS1ResourceExecution.Program.compile
        (CPS1EndogenousTranslation.selectedPeptide edits water additional)) ∧
    type_of% (CPS1EndogenousTranslation.source_charging_native edits water additional) ∧
    type_of% (CPS1EndogenousTranslation.source_elongation_native edits water additional) ∧
    type_of% (CPS1EndogenousTranslation.actual_plan_boundaries edits water additional) ∧
    (∀ stock, (readMaterial runtime).endogenousCharging edits water additional stock =
      ((readMaterial runtime).endogenousPlan edits water additional).map
        (fun plan => CPS1ResourceExecution.execute plan.charges stock)) ∧
    (∀ stock, (readMaterial runtime).endogenousElongation edits water additional stock =
      ((readMaterial runtime).endogenousPlan edits water additional).map
        (fun plan => CPS1ResourceExecution.execute plan.elongationCore stock)) ∧
    (readMaterial runtime.tick.next).endogenousPlan edits water additional =
      (readMaterial runtime).endogenousPlan edits water additional := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate), same_source_and_complete_ledger,
    ?_, ?_, ?_, ?_, ?_, (fun _ => rfl), (fun _ => rfl), rfl⟩
  · rw [readMaterial_eq]
    change CPS1EndogenousTranslation.continuedPlan edits water additional =
      (CPS1Deamination.ContinuedCoding.continuedCoding edits water additional).bind
        (fun coding => (CPS1EndogenousTranslation.peptideFromCoding? coding).map
          CPS1ResourceExecution.Program.compile)
    unfold CPS1EndogenousTranslation.continuedPlan CPS1EndogenousTranslation.continuedPeptide
      CPS1EndogenousTranslation.peptideFromCoding?
      CPS1Deamination.ContinuedCoding.continuedStopChain
    cases coding : CPS1Deamination.ContinuedCoding.continuedCoding edits water additional with
    | none => simp
    | some dna =>
      cases parsed : Coding.coding? dna with
      | none => simp [parsed]
      | some code =>
        cases labels : Coding.translate Coding.code code <;> simp [parsed, labels]
  · exact (readCertificate runtime).endogenousTranslation.generatedPlan edits water additional
  · exact (readCertificate runtime).endogenousTranslation.chargingNative edits water additional
  · exact (readCertificate runtime).endogenousTranslation.elongationNative edits water additional
  · exact (readCertificate runtime).endogenousTranslation.boundaries edits water additional

theorem actual_boundary_translation (runtime : LivingRuntimeState process) (edits : Target.Edits)
    (water additional : Nat) (raw : CPS1ResourceExecution.Stock) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).boundaryProgram edits water additional =
      some (CPS1InitiationTermination.UnifiedBoundary.compile
        (CPS1EndogenousTranslation.selectedPeptide edits water additional).2) ∧
    (readMaterial runtime).boundaryExecution edits water additional raw =
      ((readMaterial runtime).boundaryProgram edits water additional).map
        (fun program => CPS1ResourceExecution.execute program raw) ∧
    (readMaterial runtime).boundaryRawFuel edits water additional =
      CPS1InitiationTermination.Source.rawSourceFuel edits water additional ∧
    type_of% (CPS1InitiationTermination.Source.source_native_complete edits water additional) ∧
    type_of% (CPS1InitiationTermination.UnifiedBoundary.source_fine_inventory edits water additional raw) ∧
    (readMaterial runtime.tick.next).boundaryProgram edits water additional =
      (readMaterial runtime).boundaryProgram edits water additional ∧
    (readMaterial runtime.tick.next).boundaryRawFuel edits water additional =
      (readMaterial runtime).boundaryRawFuel edits water additional := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate), same_source_and_complete_ledger,
    ?_, rfl, rfl, ?_, ?_, rfl, rfl⟩
  · exact (readCertificate runtime).boundaryTranslation.program.sourceProgram edits water additional
  · exact (readCertificate runtime).boundaryTranslation.released edits water additional
  · exact (readCertificate runtime).boundaryTranslation.program.fineInventory edits water additional raw

theorem actual_recycling (runtime : LivingRuntimeState process) (edits : Target.Edits)
    (water additional : Nat) (site : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).recyclingFrame edits water additional =
      some (CPS1Recycling.Source.frame edits water additional) ∧
    (readMaterial runtime).recyclingExecution edits water additional events feed =
      some ⟨CPS1Recycling.Source.frame edits water additional,
        CPS1Recycling.run (CPS1Recycling.Source.frame edits water additional) events feed⟩ ∧
    (readMaterial runtime).recyclingEvents site = CPS1Recycling.productiveEvents site ∧
    (readMaterial runtime).recyclingFreshFuel = CPS1Recycling.freshFuel ∧
    type_of% (CPS1Recycling.Source.source_native_complete edits water additional site) ∧
    type_of% (CPS1Recycling.Source.source_bound43_and_same_message edits water additional site) ∧
    type_of% (CPS1Recycling.run_disposition (CPS1Recycling.Source.frame edits water additional) events feed) ∧
    type_of% (CPS1Recycling.run_currency_balance (CPS1Recycling.Source.frame edits water additional) events feed) ∧
    type_of% (CPS1Recycling.run_carrier_balance (CPS1Recycling.Source.frame edits water additional) events feed) ∧
    (∀ factor, type_of% (CPS1Recycling.run_actor_balance
      (CPS1Recycling.Source.frame edits water additional) events feed factor)) ∧
    (∀ aa, type_of% (CPS1Recycling.run_residue_message_balance
      (CPS1Recycling.Source.frame edits water additional) events feed aa)) ∧
    (∀ species, type_of% (CPS1Recycling.run_inventory_balance
      (CPS1Recycling.Source.frame edits water additional) events feed species)) ∧
    (∀ μ, type_of% (CPS1Recycling.run_potential
      (CPS1Recycling.Source.frame edits water additional) events feed μ)) ∧
    (∀ missing, type_of% (CPS1Recycling.run_cut
      (CPS1Recycling.Source.frame edits water additional) events feed missing)) ∧
    (readMaterial runtime.tick.next).recyclingFrame edits water additional =
      (readMaterial runtime).recyclingFrame edits water additional ∧
    (readMaterial runtime.tick.next).recyclingExecution edits water additional events feed =
      (readMaterial runtime).recyclingExecution edits water additional events feed := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate),same_source_and_complete_ledger,
    ?_,?_,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · exact (readCertificate runtime).recycling.sourceFrame edits water additional
  · exact (readCertificate runtime).recycling.execution edits water additional events feed
  · exact (readCertificate runtime).recycling.nativeComplete edits water additional site
  · exact (readCertificate runtime).recycling.bound43AndTemplate edits water additional site
  · exact (readCertificate runtime).recycling.disposition _ events feed
  · exact (readCertificate runtime).recycling.currencies _ events feed
  · exact (readCertificate runtime).recycling.carriers _ events feed
  · exact (readCertificate runtime).recycling.actors _ events feed
  · exact (readCertificate runtime).recycling.residuesAndMessage _ events feed
  · exact (readCertificate runtime).recycling.inventory _ events feed
  · exact (readCertificate runtime).recycling.potential _ events feed
  · exact (readCertificate runtime).recycling.cut _ events feed

theorem actual_reinitiation (runtime : LivingRuntimeState process) (edits : Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (feed : List CPS1Reinitiation.Handover.RawMaterial) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).reinitiationRna = Molecules.mrna ∧
    (readMaterial runtime).reinitiationExecution edits water additional path recycleFeed scanFeed =
      CPS1Reinitiation.Source.execution edits water additional path recycleFeed scanFeed ∧
    (readMaterial runtime).cycleExecution edits water additional path recycleFeed scanFeed feed =
      CPS1Reinitiation.Handover.Source.execution edits water additional path recycleFeed scanFeed feed ∧
    (readMaterial runtime).cycleProgram path =
      some (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151
        CPS1ResourceExecution.Program.originalPeptide.2) ∧
    (readMaterial runtime).cycleRawFuel =
      some (CPS1Reinitiation.Handover.rawFuel CPS1ResourceExecution.Program.originalPeptide.2) ∧
    type_of% CPS1Reinitiation.Source.execution_from_actual_stock ∧
    type_of% CPS1Reinitiation.Source.native_complete ∧
    type_of% CPS1Reinitiation.Source.paid48_and_both_message_identities ∧
    type_of% CPS1Reinitiation.Accounting.execution_conservation ∧
    type_of% CPS1Reinitiation.run_balance ∧
    type_of% CPS1Reinitiation.run_potential ∧
    type_of% CPS1Reinitiation.run_cut ∧
    type_of% CPS1Reinitiation.Handover.Source.execution_from_actual_stock ∧
    type_of% CPS1Reinitiation.Handover.Source.native_complete ∧
    type_of% CPS1Reinitiation.Handover.Source.released_editor_next_postTC_and_both_RNAs ∧
    type_of% CPS1Reinitiation.HandoverLedger.reaction_balance ∧
    type_of% CPS1Reinitiation.HandoverLedger.execution_conservation ∧
    type_of% CPS1Reinitiation.HandoverLedger.execution_site_effect ∧
    type_of% CPS1Reinitiation.HandoverLedger.execution_inventory_balance ∧
    type_of% CPS1Reinitiation.HandoverLedger.execution_potential ∧
    type_of% CPS1Reinitiation.HandoverLedger.execution_cut ∧
    (readMaterial runtime.tick.next).reinitiationExecution = (readMaterial runtime).reinitiationExecution ∧
    (readMaterial runtime.tick.next).cycleExecution = (readMaterial runtime).cycleExecution ∧
    (readMaterial runtime.tick.next).cycleRawFuel = (readMaterial runtime).cycleRawFuel := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate),same_source_and_complete_ledger,
    rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl⟩
  · exact (readCertificate runtime).reinitiation.sourceProgram path
  · exact (readCertificate runtime).reinitiation.bodyRawFuel
  · exact (readCertificate runtime).reinitiation.scanExecution
  · exact (readCertificate runtime).reinitiation.scanComplete
  · exact (readCertificate runtime).reinitiation.scanReadout
  · exact (readCertificate runtime).reinitiation.scanConservation
  · exact (readCertificate runtime).reinitiation.scanInventory
  · exact (readCertificate runtime).reinitiation.scanPotential
  · exact (readCertificate runtime).reinitiation.scanCut
  · exact (readCertificate runtime).reinitiation.bodyExecution
  · exact (readCertificate runtime).reinitiation.bodyComplete
  · exact (readCertificate runtime).reinitiation.bodyReadout
  · exact (readCertificate runtime).reinitiation.reactionBalance
  · exact (readCertificate runtime).reinitiation.conservation
  · exact (readCertificate runtime).reinitiation.siteEffect
  · exact (readCertificate runtime).reinitiation.inventory
  · exact (readCertificate runtime).reinitiation.potential
  · exact (readCertificate runtime).reinitiation.cut

theorem actual_stock_recursion (runtime : LivingRuntimeState process) (edits : Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial)
    (feeds : List (List CPS1StockRecursion.Dictionary.RawMaterial)) (depth : Nat) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).stockRecursionExecution edits water additional path recycleFeed scanFeed bodyFeed feeds =
      CPS1StockRecursion.Source.actualObservation edits water additional path recycleFeed scanFeed bodyFeed feeds ∧
    (readMaterial runtime).stockRecursionRequested edits water additional path recycleFeed scanFeed bodyFeed depth =
      CPS1StockRecursion.Source.actualRequested edits water additional path recycleFeed scanFeed bodyFeed depth ∧
    (readMaterial runtime).stockRecursionRawFuel = CPS1StockRecursion.Source.rawSourceFuel ∧
    (readMaterial runtime).stockRecursionProgram = CPS1StockRecursion.Source.program ∧
    type_of% CPS1StockRecursion.Initial.actual_stock ∧
    type_of% CPS1StockRecursion.Native.cycle_complete ∧
    type_of% CPS1StockRecursion.Source.source_program ∧
    type_of% CPS1StockRecursion.Source.raw_source_fuel_generated ∧
    type_of% CPS1StockRecursion.Source.actual_observation_from_handover ∧
    type_of% CPS1StockRecursion.Source.actual_requested_complete ∧
    type_of% CPS1StockRecursion.Source.actual_next ∧
    type_of% CPS1StockRecursion.Source.cut_continuation ∧
    type_of% CPS1StockRecursion.Source.full_depth ∧
    type_of% CPS1StockRecursion.Source.observation_stage_count ∧
    type_of% CPS1StockRecursion.Source.observation_conservation ∧
    type_of% CPS1StockRecursion.Dictionary.Accounting.execution_site_effect_computed ∧
    type_of% CPS1StockRecursion.Source.observation_inventory_balance ∧
    type_of% CPS1StockRecursion.Source.observation_potential ∧
    (readMaterial runtime.tick.next).stockRecursionExecution = (readMaterial runtime).stockRecursionExecution ∧
    (readMaterial runtime.tick.next).stockRecursionRequested = (readMaterial runtime).stockRecursionRequested ∧
    (readMaterial runtime.tick.next).stockRecursionRawFuel = (readMaterial runtime).stockRecursionRawFuel ∧
    (readMaterial runtime.tick.next).stockRecursionProgram = (readMaterial runtime).stockRecursionProgram := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate),same_source_and_complete_ledger,
    rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl⟩
  · exact (readCertificate runtime).stockRecursion.initial
  · exact (readCertificate runtime).stockRecursion.nativeCycle
  · exact (readCertificate runtime).stockRecursion.rawProgram
  · exact (readCertificate runtime).stockRecursion.rawFuel
  · exact (readCertificate runtime).stockRecursion.actualSource
  · exact (readCertificate runtime).stockRecursion.actualRequested
  · exact (readCertificate runtime).stockRecursion.generatedNext
  · exact (readCertificate runtime).stockRecursion.cutResume
  · exact (readCertificate runtime).stockRecursion.fullDepth
  · exact (readCertificate runtime).stockRecursion.stages
  · exact (readCertificate runtime).stockRecursion.conservation
  · exact (readCertificate runtime).stockRecursion.siteEffect
  · exact (readCertificate runtime).stockRecursion.inventory
  · exact (readCertificate runtime).stockRecursion.potential

theorem actual_local_chemical (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).localChemicalExecution = CPS1LocalChemicalExecution.Source.execution ∧
    (readMaterial runtime).localChemicalCapture = CPS1LocalChemicalExecution.Source.actualCapture ∧
    (readMaterial runtime).localChemicalMaterial = CPS1LocalChemicalExecution.Source.RawMaterial.species ∧
    (readMaterial runtime).localChemicalProgram = CPS1LocalChemicalExecution.Source.localProgram ∧
    (readMaterial runtime).localChemicalAdvance = CPS1LocalChemicalExecution.Source.advance ∧
    type_of% CPS1LocalChemicalExecution.Source.actual_capture_complete ∧
    type_of% CPS1LocalChemicalExecution.Source.actual_local_update ∧
    type_of% CPS1LocalChemicalExecution.hydrolyse_source_bond ∧
    type_of% CPS1LocalChemicalExecution.Dynamics.source_drive ∧
    type_of% CPS1LocalChemicalExecution.Source.chemistry_complete ∧
    type_of% CPS1LocalChemicalExecution.Chemistry.atomic_charge_balance ∧
    type_of% CPS1LocalChemicalExecution.components_all_material ∧
    type_of% CPS1LocalChemicalExecution.Source.local_stock_balance ∧
    type_of% CPS1LocalChemicalExecution.Source.local_cut_preserves_remaining ∧
    (readMaterial runtime.tick.next).localChemicalExecution = (readMaterial runtime).localChemicalExecution ∧
    (readMaterial runtime.tick.next).localChemicalCapture = (readMaterial runtime).localChemicalCapture ∧
    (readMaterial runtime.tick.next).localChemicalMaterial = (readMaterial runtime).localChemicalMaterial ∧
    (readMaterial runtime.tick.next).localChemicalProgram = (readMaterial runtime).localChemicalProgram ∧
    (readMaterial runtime.tick.next).localChemicalAdvance = (readMaterial runtime).localChemicalAdvance := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate),same_source_and_complete_ledger,
    rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · exact (readCertificate runtime).localChemical.actualCapture
  · exact (readCertificate runtime).localChemical.localUpdate
  · exact (readCertificate runtime).localChemical.sourceBond
  · exact (readCertificate runtime).localChemical.work
  · exact (readCertificate runtime).localChemical.chemistry
  · exact (readCertificate runtime).localChemical.chemistryBalance
  · exact (readCertificate runtime).localChemical.fragments
  · exact (readCertificate runtime).localChemical.inventory
  · exact (readCertificate runtime).localChemical.cut

theorem actual_editing_chemical_join (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).editingChemicalExecution = CPS1EditingChemicalJoin.Source.execution ∧
    (readMaterial runtime).editingChemicalAdvance = CPS1EditingChemicalJoin.Source.advance ∧
    (readMaterial runtime).editingChemicalFuel = CPS1EditingChemicalJoin.Source.rawFuel ∧
    (readMaterial runtime).editingChemicalCycles = CPS1EditingChemicalJoin.Continuation.cycles ∧
    type_of% CPS1EditingChemicalJoin.Source.actual_chemical_complete ∧
    type_of% CPS1EditingChemicalJoin.Source.actual_join_stock ∧
    type_of% CPS1EditingChemicalJoin.EditingStock.ammonia_count ∧
    type_of% CPS1EditingChemicalJoin.EditingStock.dna_count ∧
    type_of% CPS1EditingChemicalJoin.EditingStock.water_count ∧
    type_of% CPS1EditingChemicalJoin.Source.advance_chemical_complete ∧
    type_of% CPS1EditingChemicalJoin.Accounting.actual_chemical_counts ∧
    type_of% CPS1EditingChemicalJoin.Continuation.advance_does_not_rejoin ∧
    type_of% CPS1EditingChemicalJoin.Continuation.complete_cycles ∧
    (readMaterial runtime.tick.next).editingChemicalExecution = (readMaterial runtime).editingChemicalExecution ∧
    (readMaterial runtime.tick.next).editingChemicalAdvance = (readMaterial runtime).editingChemicalAdvance ∧
    (readMaterial runtime.tick.next).editingChemicalFuel = (readMaterial runtime).editingChemicalFuel ∧
    (readMaterial runtime.tick.next).editingChemicalCycles = (readMaterial runtime).editingChemicalCycles := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate),same_source_and_complete_ledger,
    rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl⟩
  · exact (readCertificate runtime).editingChemical.actualSource
  · exact (readCertificate runtime).editingChemical.joinedInventory
  · exact (readCertificate runtime).editingChemical.sourceAmmonia
  · exact (readCertificate runtime).editingChemical.wholeDna
  · exact (readCertificate runtime).editingChemical.remainingWater
  · exact (readCertificate runtime).editingChemical.actualUpdate
  · exact (readCertificate runtime).editingChemical.materialCounts
  · exact (readCertificate runtime).editingChemical.noRejoin
  · exact (readCertificate runtime).editingChemical.finiteCycles

theorem actual_atomic_source (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).atomicSourceExecution = CPS1AtomicSource.Current.execution ∧
    (readMaterial runtime).atomicSourceLocalExecution = CPS1AtomicSource.Current.sourceExecution ∧
    (readMaterial runtime).atomicSourceAdvance = CPS1AtomicSource.Current.advance ∧
    (readMaterial runtime).atomicSourceGraph = CPS1AtomicSource.Current.graph ∧
    (readMaterial runtime).atomicSourceProtons = CPS1AtomicSource.Graph.requiredProtons ∧
    type_of% CPS1AtomicSource.Contract.actual_atomic_complete ∧
    type_of% CPS1AtomicSource.Current.chain_material ∧
    type_of% CPS1AtomicSource.Current.chain_charge ∧
    type_of% CPS1AtomicSource.Current.chain_no_dangling ∧
    type_of% CPS1AtomicSource.SourceBudget.actual_capture_proton_budget ∧
    type_of% CPS1AtomicSource.Current.source_proton_payment ∧
    type_of% CPS1AtomicSource.Current.atomic_inventory_balance ∧
    type_of% CPS1AtomicSource.Current.atomic_cut ∧
    type_of% CPS1AtomicSource.Current.advance_retains_source ∧
    type_of% CPS1AtomicSource.Graph.source_atom_payload ∧
    type_of% CPS1AtomicSource.Graph.source_component_bond ∧
    type_of% CPS1AtomicSource.Current.cleave_valid ∧
    (readMaterial runtime.tick.next).atomicSourceExecution = (readMaterial runtime).atomicSourceExecution ∧
    (readMaterial runtime.tick.next).atomicSourceLocalExecution = (readMaterial runtime).atomicSourceLocalExecution ∧
    (readMaterial runtime.tick.next).atomicSourceAdvance = (readMaterial runtime).atomicSourceAdvance ∧
    (readMaterial runtime.tick.next).atomicSourceGraph = (readMaterial runtime).atomicSourceGraph ∧
    (readMaterial runtime.tick.next).atomicSourceProtons = (readMaterial runtime).atomicSourceProtons := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate),same_source_and_complete_ledger,
    rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · exact (readCertificate runtime).atomicSource.actualAtomic
  · exact (readCertificate runtime).atomicSource.atomMaterial
  · exact (readCertificate runtime).atomicSource.charge
  · exact (readCertificate runtime).atomicSource.noDangling
  · exact (readCertificate runtime).atomicSource.sourceProtonBudget
  · exact (readCertificate runtime).atomicSource.actualDebitInventory
  · exact (readCertificate runtime).atomicSource.inventoryBalance
  · exact (readCertificate runtime).atomicSource.cut
  · exact (readCertificate runtime).atomicSource.advanceSourceIdentity
  · exact (readCertificate runtime).atomicSource.originalAtoms
  · exact (readCertificate runtime).atomicSource.originalComponentBonds
  · exact (readCertificate runtime).atomicSource.sourceChainValidity

theorem actual_atomic_dynamics (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).atomicDynamicsExecution = CPS1AtomicDynamics.Source.execution ∧
    (readMaterial runtime).atomicDynamicsResume = CPS1AtomicDynamics.Source.resume ∧
    (readMaterial runtime).atomicDynamicsMaterial = CPS1AtomicDynamics.Source.RawAction.material ∧
    (readMaterial runtime).atomicDynamicsPulse = CPS1AtomicDynamics.Body.pulse? ∧
    (readMaterial runtime).atomicDynamicsForce = CPS1AtomicDynamics.Body.force ∧
    (readMaterial runtime).atomicDynamicsEnergy = CPS1AtomicDynamics.Body.energy ∧
    type_of% CPS1AtomicDynamics.Actual.actual_start ∧
    type_of% CPS1AtomicDynamics.Charged.generated_charge ∧
    type_of% CPS1AtomicDynamics.Charged.particles_unique ∧
    type_of% CPS1AtomicDynamics.actual_field ∧
    type_of% CPS1AtomicDynamics.Body.pulse_whole_carrier ∧
    type_of% CPS1AtomicDynamics.joint_momentum ∧
    type_of% CPS1AtomicDynamics.Body.kick_work ∧
    type_of% CPS1AtomicDynamics.Body.returned_energy ∧
    type_of% CPS1AtomicDynamics.actual_pulse ∧
    type_of% CPS1AtomicDynamics.full_inventory ∧
    type_of% CPS1AtomicDynamics.source_cut ∧
    type_of% CPS1AtomicDynamics.Source.guard_cut ∧
    type_of% CPS1AtomicDynamics.Source.advance_no_guard ∧
    type_of% CPS1AtomicDynamics.Source.continuation_source ∧
    (readMaterial runtime.tick.next).atomicDynamicsExecution = (readMaterial runtime).atomicDynamicsExecution ∧
    (readMaterial runtime.tick.next).atomicDynamicsResume = (readMaterial runtime).atomicDynamicsResume ∧
    (readMaterial runtime.tick.next).atomicDynamicsMaterial = (readMaterial runtime).atomicDynamicsMaterial ∧
    (readMaterial runtime.tick.next).atomicDynamicsPulse = (readMaterial runtime).atomicDynamicsPulse ∧
    (readMaterial runtime.tick.next).atomicDynamicsForce = (readMaterial runtime).atomicDynamicsForce ∧
    (readMaterial runtime.tick.next).atomicDynamicsEnergy = (readMaterial runtime).atomicDynamicsEnergy := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate),same_source_and_complete_ledger,
    rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact (readCertificate runtime).atomicDynamics.actualSource
  · exact (readCertificate runtime).atomicDynamics.sourceCharge
  · exact (readCertificate runtime).atomicDynamics.sourceAddresses
  · exact (readCertificate runtime).atomicDynamics.coulombForce
  · exact (readCertificate runtime).atomicDynamics.wholeCarrier
  · exact (readCertificate runtime).atomicDynamics.jointMomentum
  · exact (readCertificate runtime).atomicDynamics.sourceWork
  · exact (readCertificate runtime).atomicDynamics.energyPayment
  · exact (readCertificate runtime).atomicDynamics.actualInventory
  · exact (readCertificate runtime).atomicDynamics.inventoryBalance
  · exact (readCertificate runtime).atomicDynamics.cut
  · exact (readCertificate runtime).atomicDynamics.guardCut
  · exact (readCertificate runtime).atomicDynamics.noGuard
  · exact (readCertificate runtime).atomicDynamics.continuationSource

theorem actual_enzyme_bath (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).enzymeBathExecution = CPS1EnzymeBath.Source.execution ∧
    (readMaterial runtime).enzymeBathGeneratedExecution = CPS1EnzymeBath.Source.generatedExecution ∧
    (readMaterial runtime).enzymeBathResume = CPS1EnzymeBath.Source.resume ∧
    (readMaterial runtime).enzymeBathTemplate = CPS1EnzymeBath.Primary.template ∧
    (readMaterial runtime).enzymeBathParticles = CPS1EnzymeBath.Joint.particles ∧
    (readMaterial runtime).enzymeBathPulse = CPS1EnzymeBath.Joint.pulse? ∧
    type_of% CPS1EnzymeBath.Actual.actual_live_capture ∧
    type_of% CPS1EnzymeBath.Partner.actual_generated_partner ∧
    type_of% CPS1EnzymeBath.Primary.original_formula ∧
    type_of% CPS1EnzymeBath.Primary.original_charge ∧
    type_of% CPS1EnzymeBath.Joint.source_bonds ∧
    type_of% CPS1EnzymeBath.Joint.no_dangling ∧
    type_of% CPS1EnzymeBath.Joint.whole_material ∧
    type_of% CPS1EnzymeBath.Joint.whole_charge ∧
    type_of% CPS1EnzymeBath.Joint.particle_charge ∧
    type_of% CPS1EnzymeBath.Joint.old_particle_retained ∧
    type_of% CPS1EnzymeBath.source_component_paid ∧
    type_of% CPS1EnzymeBath.Joint.joint_field ∧
    type_of% CPS1EnzymeBath.source_joint_pulse ∧
    type_of% CPS1EnzymeBath.Joint.returned_energy ∧
    type_of% CPS1EnzymeBath.Joint.pulse_whole ∧
    type_of% CPS1EnzymeBath.whole_inventory ∧
    type_of% CPS1EnzymeBath.actual_cut ∧
    type_of% CPS1EnzymeBath.Source.guard_cut ∧
    type_of% CPS1EnzymeBath.Source.advance_no_guard ∧
    type_of% CPS1EnzymeBath.Actual.initial_pending_material ∧
    type_of% CPS1EnzymeBath.Source.source_preserved ∧
    (readMaterial runtime.tick.next).enzymeBathExecution = (readMaterial runtime).enzymeBathExecution ∧
    (readMaterial runtime.tick.next).enzymeBathGeneratedExecution = (readMaterial runtime).enzymeBathGeneratedExecution ∧
    (readMaterial runtime.tick.next).enzymeBathResume = (readMaterial runtime).enzymeBathResume ∧
    (readMaterial runtime.tick.next).enzymeBathTemplate = (readMaterial runtime).enzymeBathTemplate ∧
    (readMaterial runtime.tick.next).enzymeBathParticles = (readMaterial runtime).enzymeBathParticles ∧
    (readMaterial runtime.tick.next).enzymeBathPulse = (readMaterial runtime).enzymeBathPulse := by
  refine ⟨face_factorizes runtime (.component .material),
    face_factorizes runtime (.component .certificate),same_source_and_complete_ledger,
    rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact (readCertificate runtime).enzymeBath.actualSource
  · exact (readCertificate runtime).enzymeBath.generatedPartner
  · exact (readCertificate runtime).enzymeBath.templateMaterial
  · exact (readCertificate runtime).enzymeBath.templateCharge
  · exact (readCertificate runtime).enzymeBath.sourceBonds
  · exact (readCertificate runtime).enzymeBath.noDangling
  · exact (readCertificate runtime).enzymeBath.wholeMaterial
  · exact (readCertificate runtime).enzymeBath.wholeCharge
  · exact (readCertificate runtime).enzymeBath.particleCharge
  · exact (readCertificate runtime).enzymeBath.oldParticles
  · exact (readCertificate runtime).enzymeBath.actualComponentPayment
  · exact (readCertificate runtime).enzymeBath.jointField
  · exact (readCertificate runtime).enzymeBath.actualPulse
  · exact (readCertificate runtime).enzymeBath.energyPayment
  · exact (readCertificate runtime).enzymeBath.wholeCarrier
  · exact (readCertificate runtime).enzymeBath.inventory
  · exact (readCertificate runtime).enzymeBath.cut
  · exact (readCertificate runtime).enzymeBath.guardCut
  · exact (readCertificate runtime).enzymeBath.rawNoGuard
  · exact (readCertificate runtime).enzymeBath.pendingMaterial
  · exact (readCertificate runtime).enzymeBath.sourceResume

theorem actual_electronic_source (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (readMaterial runtime).electronicExecution = CPS1ElectronicSource.Source.execution ∧
    (readMaterial runtime).electronicResume = CPS1ElectronicSource.Source.resume ∧
    (readMaterial runtime).electronicMaterial = CPS1ElectronicSource.Source.RawAction.material ∧
    (@Material.electronicHamiltonian (readMaterial runtime)) = @CPS1ElectronicSource.State.hamiltonian ∧
    (@Material.electronicEnergy (readMaterial runtime)) = @CPS1ElectronicSource.State.energy ∧
    (@Material.electronicAction (readMaterial runtime)) = @CPS1ElectronicSource.continuousAction ∧
    type_of% @CPS1ElectronicSource.actual_electronic_source ∧
    type_of% @CPS1ElectronicSource.normalized_synthesis ∧
    type_of% @CPS1ElectronicEvolution.Source.source_occupation ∧
    type_of% @CPS1ElectronicSource.normalized_nuclear_integrable ∧
    type_of% @CPS1ElectronicSource.normalized_pair_integrable ∧
    type_of% @CPS1ElectronicSource.source_hamiltonian_hermitian ∧
    type_of% @CPS1ElectronicSource.continuous_action_exact ∧
    type_of% @CPS1ElectronicSource.actual_continuous_midpoint ∧
    type_of% @CPS1ElectronicSource.current_continuous_fields ∧
    type_of% @CPS1ElectronicSource.same_native_net_charge ∧
    type_of% @CPS1ElectronicSource.actual_native_response ∧
    type_of% @CPS1ElectronicSource.actual_native_current ∧
    type_of% @CPS1ElectronicSource.Actual.prepare_actual ∧
    type_of% @CPS1ElectronicSource.capture_paid ∧
    type_of% @CPS1ElectronicSource.capture_price_actual ∧
    type_of% @CPS1ElectronicSource.pulse_paid ∧
    type_of% @CPS1ElectronicSource.deposit_paid ∧
    type_of% @CPS1ElectronicSource.execution_safe ∧
    type_of% @CPS1ElectronicSource.whole_inventory ∧
    type_of% @CPS1ElectronicSource.whole_potential ∧
    type_of% @CPS1ElectronicSource.actual_cut ∧
    type_of% @CPS1ElectronicSource.true_guard_cut ∧
    type_of% @CPS1ElectronicSource.legacy_requireCarrier_cut ∧
    type_of% @CPS1ElectronicSource.Actual.raw_cut_suffix ∧
    type_of% @CPS1ElectronicSource.Source.source_preserved ∧
    type_of% @CPS1ElectronicSource.resume_safe ∧
    (readMaterial runtime.tick.next).electronicExecution = (readMaterial runtime).electronicExecution ∧
    (readMaterial runtime.tick.next).electronicResume = (readMaterial runtime).electronicResume ∧
    (readMaterial runtime.tick.next).electronicMaterial = (readMaterial runtime).electronicMaterial ∧
    (@Material.electronicHamiltonian (readMaterial runtime.tick.next)) = (@Material.electronicHamiltonian (readMaterial runtime)) ∧
    (@Material.electronicEnergy (readMaterial runtime.tick.next)) = (@Material.electronicEnergy (readMaterial runtime)) ∧
    (@Material.electronicAction (readMaterial runtime.tick.next)) = (@Material.electronicAction (readMaterial runtime)) := by
  refine ⟨face_factorizes runtime (.component .material),face_factorizes runtime (.component .certificate),same_source_and_complete_ledger,rfl,rfl,rfl,
    rfl,rfl,rfl,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,rfl,
    rfl,rfl,rfl,rfl,rfl⟩
  · exact (readCertificate runtime).electronicSource.actualSource
  · exact (readCertificate runtime).electronicSource.sourceNormalizer
  · exact (readCertificate runtime).electronicSource.sourceOccupation
  · exact (readCertificate runtime).electronicSource.nuclearDomain
  · exact (readCertificate runtime).electronicSource.pairDomain
  · exact (readCertificate runtime).electronicSource.sourceHamiltonian
  · exact (readCertificate runtime).electronicSource.boundedProjection
  · exact (readCertificate runtime).electronicSource.projectedEquation
  · exact (readCertificate runtime).electronicSource.sourceFields
  · exact (readCertificate runtime).electronicSource.nativeNetCharge
  · exact (readCertificate runtime).electronicSource.nativeResponse
  · exact (readCertificate runtime).electronicSource.nativeCurrent
  · exact (readCertificate runtime).electronicSource.actualCapture
  · exact (readCertificate runtime).electronicSource.capturePayment
  · exact (readCertificate runtime).electronicSource.energyReplacement
  · exact (readCertificate runtime).electronicSource.pulsePayment
  · exact (readCertificate runtime).electronicSource.depositPayment
  · exact (readCertificate runtime).electronicSource.generatedInventory
  · exact (readCertificate runtime).electronicSource.inventory
  · exact (readCertificate runtime).electronicSource.potential
  · exact (readCertificate runtime).electronicSource.cut
  · exact (readCertificate runtime).electronicSource.guardCut
  · exact (readCertificate runtime).electronicSource.legacyPhaseCut
  · exact (readCertificate runtime).electronicSource.pending
  · exact (readCertificate runtime).electronicSource.sourceResume
  · exact (readCertificate runtime).electronicSource.continuationFields

theorem actual_quantum_nuclear (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (@Material.quantumNuclearExecution (readMaterial runtime)) = @CPS1QuantumNuclear.Source.execution ∧
    (@Material.quantumNuclearResume (readMaterial runtime)) = @CPS1QuantumNuclear.Source.resume ∧
    (@Material.quantumNuclearMaterial (readMaterial runtime)) = @CPS1QuantumNuclear.Source.RawAction.material ∧
    (@Material.quantumNuclearPulse (readMaterial runtime)) = @CPS1QuantumNuclear.pulse? ∧
    (@Material.quantumNuclearForce (readMaterial runtime)) = @CPS1QuantumNuclear.nuclearForce ∧
    (@Material.quantumNuclearEnergy (readMaterial runtime)) = @CPS1QuantumNuclear.spatialEnergyAt ∧
    type_of% @CPS1QuantumNuclear.actual_execution_source ∧
    type_of% @CPS1QuantumNuclear.normalized_integral_expansion ∧
    type_of% @CPS1QuantumNuclear.normalized_nuclear_line ∧
    type_of% @CPS1QuantumNuclear.original_total_energy ∧
    type_of% @CPS1QuantumNuclear.actual_source_force ∧
    type_of% @CPS1QuantumNuclear.pulse_grounded ∧
    type_of% @CPS1QuantumNuclear.nuclear_actual ∧
    type_of% @CPS1QuantumNuclear.pulse_paid ∧
    type_of% @CPS1QuantumNuclear.pulse_source ∧
    type_of% @CPS1QuantumNuclear.pulse_atoms_and_bonds ∧
    type_of% @CPS1QuantumNuclear.pulse_good ∧
    type_of% @CPS1QuantumNuclear.current_fields ∧
    type_of% @CPS1QuantumNuclear.source_stock ∧
    type_of% @CPS1QuantumNuclear.whole_inventory ∧
    type_of% @CPS1QuantumNuclear.actual_cut ∧
    type_of% @CPS1QuantumNuclear.true_guard_cut ∧
    type_of% @CPS1QuantumNuclear.inherited_guard_cut ∧
    type_of% @CPS1QuantumNuclear.legacy_requireCarrier_cut ∧
    type_of% @CPS1QuantumNuclear.pending_same ∧
    type_of% @CPS1QuantumNuclear.Source.source_preserved ∧
    type_of% @CPS1QuantumNuclear.resume_good ∧
    type_of% @CPS1QuantumNuclear.resume_noGuard ∧
    (@Material.quantumNuclearExecution (readMaterial runtime.tick.next)) = (@Material.quantumNuclearExecution (readMaterial runtime)) ∧
    (@Material.quantumNuclearResume (readMaterial runtime.tick.next)) = (@Material.quantumNuclearResume (readMaterial runtime)) ∧
    (@Material.quantumNuclearMaterial (readMaterial runtime.tick.next)) = (@Material.quantumNuclearMaterial (readMaterial runtime)) ∧
    (@Material.quantumNuclearPulse (readMaterial runtime.tick.next)) = (@Material.quantumNuclearPulse (readMaterial runtime)) ∧
    (@Material.quantumNuclearForce (readMaterial runtime.tick.next)) = (@Material.quantumNuclearForce (readMaterial runtime)) ∧
    (@Material.quantumNuclearEnergy (readMaterial runtime.tick.next)) = (@Material.quantumNuclearEnergy (readMaterial runtime)) := by
  refine ⟨face_factorizes runtime (.component .material),face_factorizes runtime (.component .certificate),same_source_and_complete_ledger,rfl,rfl,rfl,
    rfl,rfl,rfl,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,rfl,rfl,rfl,rfl,rfl,
    rfl⟩
  · exact (readCertificate runtime).quantumNuclear.actualSource
  · exact (readCertificate runtime).quantumNuclear.sourceIntegral
  · exact (readCertificate runtime).quantumNuclear.sourceDerivative
  · exact (readCertificate runtime).quantumNuclear.originalEnergy
  · exact (readCertificate runtime).quantumNuclear.sourceForce
  · exact (readCertificate runtime).quantumNuclear.currentGrounded
  · exact (readCertificate runtime).quantumNuclear.actualPulse
  · exact (readCertificate runtime).quantumNuclear.payment
  · exact (readCertificate runtime).quantumNuclear.wholeSource
  · exact (readCertificate runtime).quantumNuclear.atomsBonds
  · exact (readCertificate runtime).quantumNuclear.occupation
  · exact (readCertificate runtime).quantumNuclear.currentFields
  · exact (readCertificate runtime).quantumNuclear.generatedStock
  · exact (readCertificate runtime).quantumNuclear.inventory
  · exact (readCertificate runtime).quantumNuclear.cut
  · exact (readCertificate runtime).quantumNuclear.trueGuardCut
  · exact (readCertificate runtime).quantumNuclear.inheritedGuardCut
  · exact (readCertificate runtime).quantumNuclear.legacyCut
  · exact (readCertificate runtime).quantumNuclear.pending
  · exact (readCertificate runtime).quantumNuclear.sourceResume
  · exact (readCertificate runtime).quantumNuclear.continuationGood
  · exact (readCertificate runtime).quantumNuclear.continuationNoGuard

theorem actual_following (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (@Material.followingExecution (readMaterial runtime)) = @CPS1Following.Source.execution ∧
    (@Material.followingResume (readMaterial runtime)) = @CPS1Following.Source.resume ∧
    (@Material.followingMaterial (readMaterial runtime)) = @CPS1Following.Source.RawAction.material ∧
    (@Material.followingRelocate (readMaterial runtime)) = @CPS1Following.relocate? ∧
    (@Material.followingPulse (readMaterial runtime)) = @CPS1Following.pulse? ∧
    (@Material.followingForce (readMaterial runtime)) = @CPS1Following.nuclearForce ∧
    (@Material.followingEnergy (readMaterial runtime)) = @CPS1Following.energy ∧
    (@Material.followingFields (readMaterial runtime)) = @CPS1Following.currentFields ∧
    (@Material.followingAction (readMaterial runtime)) = @CPS1Following.currentAction ∧
    type_of% @CPS1Following.actual_execution_source ∧
    type_of% @CPS1Following.relocate_actual ∧
    type_of% @CPS1Following.relocate_paid ∧
    type_of% @CPS1Following.relocate_grounded ∧
    type_of% @CPS1Following.relative_source ∧
    type_of% @CPS1Following.relative_particles ∧
    type_of% @CPS1Following.physical_kinetic_exact ∧
    type_of% @CPS1Following.moving_nuclear_integral ∧
    type_of% @CPS1Following.moving_pair_integral ∧
    type_of% @CPS1Following.physical_energy_exact ∧
    type_of% @CPS1Following.physical_fock_exact ∧
    type_of% @CPS1Following.moving_basis_curve ∧
    type_of% @CPS1Following.translate_slater_map ∧
    type_of% @CPS1Following.source_momentum_hermitian ∧
    type_of% @CPS1Following.moving_midpoint ∧
    type_of% @CPS1Following.actual_source_force ∧
    type_of% @CPS1Following.pulse_lab_energy_line ∧
    type_of% @CPS1Following.pulse_actual ∧
    type_of% @CPS1Following.pulse_paid ∧
    type_of% @CPS1Following.pulse_source ∧
    type_of% @CPS1Following.pulse_node_rows ∧
    type_of% @CPS1Following.pulse_gather ∧
    type_of% @CPS1Following.pulse_row_momentum ∧
    type_of% @CPS1Following.pulse_mass ∧
    type_of% @CPS1Following.pulse_centre ∧
    type_of% @CPS1Following.pulse_centre_velocity ∧
    type_of% @CPS1Following.source_stock ∧
    type_of% @CPS1Following.current_fields ∧
    type_of% @CPS1Following.current_charge ∧
    type_of% @CPS1Following.whole_inventory ∧
    type_of% @CPS1Following.actual_cut ∧
    type_of% @CPS1Following.true_guard_cut ∧
    type_of% @CPS1Following.inherited_guard_cut ∧
    type_of% @CPS1Following.pending_same ∧
    type_of% @CPS1Following.Source.source_preserved ∧
    type_of% @CPS1Following.resume_good ∧
    type_of% @CPS1Following.resume_noGuard ∧
    (@Material.followingExecution (readMaterial runtime.tick.next)) = (@Material.followingExecution (readMaterial runtime)) ∧
    (@Material.followingResume (readMaterial runtime.tick.next)) = (@Material.followingResume (readMaterial runtime)) ∧
    (@Material.followingMaterial (readMaterial runtime.tick.next)) = (@Material.followingMaterial (readMaterial runtime)) ∧
    (@Material.followingRelocate (readMaterial runtime.tick.next)) = (@Material.followingRelocate (readMaterial runtime)) ∧
    (@Material.followingPulse (readMaterial runtime.tick.next)) = (@Material.followingPulse (readMaterial runtime)) ∧
    (@Material.followingForce (readMaterial runtime.tick.next)) = (@Material.followingForce (readMaterial runtime)) ∧
    (@Material.followingEnergy (readMaterial runtime.tick.next)) = (@Material.followingEnergy (readMaterial runtime)) ∧
    (@Material.followingFields (readMaterial runtime.tick.next)) = (@Material.followingFields (readMaterial runtime)) ∧
    (@Material.followingAction (readMaterial runtime.tick.next)) = (@Material.followingAction (readMaterial runtime)) := by
  refine ⟨face_factorizes runtime (.component .material),face_factorizes runtime (.component .certificate),same_source_and_complete_ledger,
    rfl,rfl,rfl,rfl,rfl,rfl,
    rfl,rfl,rfl,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,rfl,rfl,
    rfl,rfl,rfl,rfl,rfl,rfl,
    rfl⟩
  · exact (readCertificate runtime).following.actualSource
  · exact (readCertificate runtime).following.relocation
  · exact (readCertificate runtime).following.relocationPayment
  · exact (readCertificate runtime).following.relocationGrounded
  · exact (readCertificate runtime).following.relativeSource
  · exact (readCertificate runtime).following.relativeParticles
  · exact (readCertificate runtime).following.kinetic
  · exact (readCertificate runtime).following.nuclearIntegral
  · exact (readCertificate runtime).following.pairIntegral
  · exact (readCertificate runtime).following.physicalEnergy
  · exact (readCertificate runtime).following.physicalFock
  · exact (readCertificate runtime).following.basisMotion
  · exact (readCertificate runtime).following.slaterMap
  · exact (readCertificate runtime).following.momentumHermitian
  · exact (readCertificate runtime).following.movingMidpoint
  · exact (readCertificate runtime).following.forceFormula
  · exact (readCertificate runtime).following.forceDerivative
  · exact (readCertificate runtime).following.actualPulse
  · exact (readCertificate runtime).following.payment
  · exact (readCertificate runtime).following.wholeSource
  · exact (readCertificate runtime).following.actualRows
  · exact (readCertificate runtime).following.coverage
  · exact (readCertificate runtime).following.rowMomentum
  · exact (readCertificate runtime).following.mass
  · exact (readCertificate runtime).following.actualCentre
  · exact (readCertificate runtime).following.actualVelocity
  · exact (readCertificate runtime).following.generatedStock
  · exact (readCertificate runtime).following.currentFields
  · exact (readCertificate runtime).following.nativeCharge
  · exact (readCertificate runtime).following.inventory
  · exact (readCertificate runtime).following.cut
  · exact (readCertificate runtime).following.trueGuardCut
  · exact (readCertificate runtime).following.inheritedGuardCut
  · exact (readCertificate runtime).following.pending
  · exact (readCertificate runtime).following.sourceResume
  · exact (readCertificate runtime).following.continuationGood
  · exact (readCertificate runtime).following.continuationNoGuard

theorem actual_molecular (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (@Material.molecularExecution (readMaterial runtime)) = @CPS1MolecularFrame.Source.execution ∧
    (@Material.molecularResume (readMaterial runtime)) = @CPS1MolecularFrame.Source.resume ∧
    (@Material.molecularMaterial (readMaterial runtime)) = @CPS1MolecularFrame.Source.RawAction.material ∧
    (@Material.molecularAdopt (readMaterial runtime)) = @CPS1MolecularFrame.adopt? ∧
    (@Material.molecularPulse (readMaterial runtime)) = @CPS1MolecularFrame.Material.pulse? ∧
    (@Material.molecularDeposit (readMaterial runtime)) = @CPS1MolecularFrame.Material.deposit? ∧
    (@Material.molecularEnergy (readMaterial runtime)) = @CPS1MolecularFrame.Material.energy ∧
    (@Material.molecularFields (readMaterial runtime)) = @CPS1MolecularFrame.Material.currentFields ∧
    (@Material.molecularAction (readMaterial runtime)) = @CPS1MolecularFrame.Material.action ∧
    type_of% @CPS1MolecularFrame.actual_execution_source ∧
    type_of% @CPS1MolecularFrame.actual_nuclei_complete ∧
    type_of% @CPS1MolecularFrame.raw_field_source ∧
    type_of% @CPS1MolecularFrame.raw_jet_curve_derivative ∧
    type_of% @CPS1MolecularFrame.nucleus_fields_independent ∧
    type_of% @CPS1MolecularFrame.normalized_span ∧
    type_of% @CPS1MolecularFrame.generated_enough ∧
    type_of% @CPS1MolecularFrame.FiniteNormed.gs_coefficients_step.{0,0,0} ∧
    type_of% @CPS1MolecularFrame.source_coefficient_gram ∧
    type_of% @CPS1MolecularFrame.basis_jet_zero ∧
    type_of% @CPS1MolecularFrame.basis_jet_value ∧
    type_of% @CPS1MolecularFrame.kinetic_integral_expansion ∧
    type_of% @CPS1MolecularFrame.basis_nuclear_integrable ∧
    type_of% @CPS1MolecularFrame.basis_pair_integrable ∧
    type_of% @CPS1MolecularFrame.nuclear_integral_expansion ∧
    type_of% @CPS1MolecularFrame.pair_integral_expansion ∧
    type_of% @CPS1MolecularFrame.fock_hermitian ∧
    type_of% @CPS1MolecularFrame.frame_curve_derivative ∧
    type_of% @CPS1MolecularFrame.current_frame_unit ∧
    type_of% @CPS1MolecularFrame.spatial_hamiltonian_selfadjoint ∧
    type_of% @CPS1MolecularFrame.source_projection_controlled ∧
    type_of% @CPS1MolecularFrame.source_frame_lift ∧
    type_of% @CPS1MolecularFrame.source_vertical_gram_rate ∧
    type_of% @CPS1MolecularFrame.adopt_actual ∧
    type_of% @CPS1MolecularFrame.adopt_good ∧
    type_of% @CPS1MolecularFrame.adopt_paid ∧
    type_of% @CPS1MolecularFrame.adopt_grounded ∧
    type_of% @CPS1MolecularFrame.adopted_source ∧
    type_of% @CPS1MolecularFrame.pulse_actual ∧
    type_of% @CPS1MolecularFrame.pulse_paid ∧
    type_of% @CPS1MolecularFrame.pulse_source ∧
    type_of% @CPS1MolecularFrame.actual_midpoint ∧
    type_of% @CPS1MolecularFrame.source_stock ∧
    type_of% @CPS1MolecularFrame.current_fields ∧
    type_of% @CPS1MolecularFrame.current_charge ∧
    type_of% @CPS1MolecularFrame.whole_inventory ∧
    type_of% @CPS1MolecularFrame.actual_cut ∧
    type_of% @CPS1MolecularFrame.true_guard_cut ∧
    type_of% @CPS1MolecularFrame.inherited_guard_cut ∧
    type_of% @CPS1MolecularFrame.failed_reaction_cannot_fire ∧
    type_of% @CPS1MolecularFrame.legacy_phase_cut ∧
    type_of% @CPS1MolecularFrame.pending_same ∧
    type_of% @CPS1MolecularFrame.Source.source_preserved ∧
    type_of% @CPS1MolecularFrame.resume_good ∧
    type_of% @CPS1MolecularFrame.resume_noGuard ∧
    (@Material.molecularExecution (readMaterial runtime.tick.next)) = (@Material.molecularExecution (readMaterial runtime)) ∧
    (@Material.molecularResume (readMaterial runtime.tick.next)) = (@Material.molecularResume (readMaterial runtime)) ∧
    (@Material.molecularMaterial (readMaterial runtime.tick.next)) = (@Material.molecularMaterial (readMaterial runtime)) ∧
    (@Material.molecularAdopt (readMaterial runtime.tick.next)) = (@Material.molecularAdopt (readMaterial runtime)) ∧
    (@Material.molecularPulse (readMaterial runtime.tick.next)) = (@Material.molecularPulse (readMaterial runtime)) ∧
    (@Material.molecularDeposit (readMaterial runtime.tick.next)) = (@Material.molecularDeposit (readMaterial runtime)) ∧
    (@Material.molecularEnergy (readMaterial runtime.tick.next)) = (@Material.molecularEnergy (readMaterial runtime)) ∧
    (@Material.molecularFields (readMaterial runtime.tick.next)) = (@Material.molecularFields (readMaterial runtime)) ∧
    (@Material.molecularAction (readMaterial runtime.tick.next)) = (@Material.molecularAction (readMaterial runtime)) := by
  refine ⟨face_factorizes runtime (.component .material),face_factorizes runtime (.component .certificate),same_source_and_complete_ledger,rfl,rfl,rfl,
    rfl,rfl,rfl,rfl,rfl,rfl,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,rfl,rfl,rfl,
    rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact (readCertificate runtime).molecular.actualSource
  · exact (readCertificate runtime).molecular.allNuclei
  · exact (readCertificate runtime).molecular.rawSource
  · exact (readCertificate runtime).molecular.rawRate
  · exact (readCertificate runtime).molecular.sourceIndependence
  · exact (readCertificate runtime).molecular.wholeSpan
  · exact (readCertificate runtime).molecular.rank
  · exact (readCertificate runtime).molecular.canonicalCoefficients
  · exact (readCertificate runtime).molecular.coefficientGram
  · exact (readCertificate runtime).molecular.basis
  · exact (readCertificate runtime).molecular.basisValue
  · exact (readCertificate runtime).molecular.kinetic
  · exact (readCertificate runtime).molecular.nuclearIntegrable
  · exact (readCertificate runtime).molecular.pairIntegrable
  · exact (readCertificate runtime).molecular.nuclearIntegral
  · exact (readCertificate runtime).molecular.pairIntegral
  · exact (readCertificate runtime).molecular.physicalFock
  · exact (readCertificate runtime).molecular.frameRate
  · exact (readCertificate runtime).molecular.frameUnit
  · exact (readCertificate runtime).molecular.spatialHamiltonian
  · exact (readCertificate runtime).molecular.projection
  · exact (readCertificate runtime).molecular.wholeLift
  · exact (readCertificate runtime).molecular.vertical
  · exact (readCertificate runtime).molecular.adoption
  · exact (readCertificate runtime).molecular.adoptionGood
  · exact (readCertificate runtime).molecular.adoptionPayment
  · exact (readCertificate runtime).molecular.adoptionGrounded
  · exact (readCertificate runtime).molecular.adoptionSource
  · exact (readCertificate runtime).molecular.actualPulse
  · exact (readCertificate runtime).molecular.pulsePayment
  · exact (readCertificate runtime).molecular.wholeSource
  · exact (readCertificate runtime).molecular.midpoint
  · exact (readCertificate runtime).molecular.generatedStock
  · exact (readCertificate runtime).molecular.currentFields
  · exact (readCertificate runtime).molecular.nativeCharge
  · exact (readCertificate runtime).molecular.inventory
  · exact (readCertificate runtime).molecular.cut
  · exact (readCertificate runtime).molecular.trueGuardCut
  · exact (readCertificate runtime).molecular.inheritedGuardCut
  · exact (readCertificate runtime).molecular.failedCannotFire
  · exact (readCertificate runtime).molecular.legacyPhase
  · exact (readCertificate runtime).molecular.pending
  · exact (readCertificate runtime).molecular.sourceResume
  · exact (readCertificate runtime).molecular.continuationGood
  · exact (readCertificate runtime).molecular.continuationNoGuard


theorem actual_deformation (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    type_of% same_source_and_complete_ledger ∧
    (@Material.deformationExecution (readMaterial runtime)) = @CPS1Deformation.Source.execution ∧
    (@Material.deformationResume (readMaterial runtime)) = @CPS1Deformation.Source.resume ∧
    (@Material.deformationMaterial (readMaterial runtime)) = @CPS1Deformation.Source.RawAction.material ∧
    (@Material.deformationAdopt (readMaterial runtime)) = @CPS1Deformation.adopt? ∧
    (@Material.deformationPulse (readMaterial runtime)) = @CPS1Deformation.Material.pulse? ∧
    (@Material.deformationDeposit (readMaterial runtime)) = @CPS1Deformation.Material.deposit? ∧
    (@Material.deformationEnergy (readMaterial runtime)) = @CPS1Deformation.Material.energy ∧
    (@Material.deformationFields (readMaterial runtime)) = @CPS1Deformation.Material.currentFields ∧
    (@Material.deformationForce (readMaterial runtime)) = @CPS1Deformation.Material.jointForce ∧
    (@Material.deformationAction (readMaterial runtime)) = @CPS1Deformation.Material.action ∧
    (@Material.deformationJoint (readMaterial runtime)) = @CPS1Deformation.Material.currentJoint ∧
    type_of% @CPS1Deformation.actual_execution_source ∧
    type_of% @CPS1Deformation.raw_jet_source ∧
    type_of% @CPS1Deformation.basis_hasFDerivAt ∧
    type_of% @CPS1Deformation.frame_hasFDerivAt ∧
    type_of% @CPS1Deformation.gram_hasFDerivAt ∧
    type_of% @CPS1Deformation.source_gram_unit ∧
    type_of% @CPS1Deformation.covariant_tangent_apply ∧
    type_of% @CPS1Deformation.occupied_connection_tangent ∧
    type_of% @CPS1Deformation.full_source_frame_lift ∧
    type_of% @CPS1Deformation.nuclear_energy_source ∧
    type_of% @CPS1Deformation.nuclear_energy_hasFDerivAt ∧
    type_of% @CPS1Deformation.energy_hasFDerivAt ∧
    type_of% @CPS1Deformation.energy_with_momenta_hasFDerivAt ∧
    type_of% @CPS1Deformation.occupied_physical_hasFDerivAt ∧
    type_of% @CPS1Deformation.occupied_physical_differential_apply ∧
    type_of% @CPS1Deformation.occupied_physical_joint_apply ∧
    type_of% @CPS1Deformation.physical_fock_hermitian ∧
    type_of% @CPS1Deformation.occupied_rank_full ∧
    type_of% @CPS1Deformation.normalized_fields ∧
    type_of% @CPS1Deformation.normalize_generated ∧
    type_of% @CPS1Deformation.normalization_span_exact ∧
    type_of% @CPS1Deformation.normalization_current_fields ∧
    type_of% @CPS1Deformation.normed_basis_complete ∧
    type_of% @CPS1Deformation.canonical_readback_fields ∧
    type_of% @CPS1Deformation.physical_fock_response_equation ∧
    type_of% @CPS1Deformation.physical_action_fields ∧
    type_of% @CPS1Deformation.physical_fock_midpoint ∧
    type_of% @CPS1Deformation.adopt_actual ∧
    type_of% @CPS1Deformation.adopt_good ∧
    type_of% @CPS1Deformation.adopt_paid ∧
    type_of% @CPS1Deformation.adopt_grounded ∧
    type_of% @CPS1Deformation.adopt_source ∧
    type_of% @CPS1Deformation.adopt_at_generated_current ∧
    type_of% @CPS1Deformation.pulse_actual ∧
    type_of% @CPS1Deformation.pulse_good ∧
    type_of% @CPS1Deformation.pulse_paid ∧
    type_of% @CPS1Deformation.pulse_grounded ∧
    type_of% @CPS1Deformation.pulse_same_source ∧
    type_of% @CPS1Deformation.pulse_force_generated ∧
    type_of% @CPS1Deformation.pulse_nuclear_work ∧
    type_of% @CPS1Deformation.actual_midpoint ∧
    type_of% @CPS1Deformation.pulse_zero_time ∧
    type_of% @CPS1Deformation.deposit_actual ∧
    type_of% @CPS1Deformation.deposit_paid ∧
    type_of% @CPS1Deformation.source_stock ∧
    type_of% @CPS1Deformation.current_fields ∧
    type_of% @CPS1Deformation.current_charge ∧
    type_of% @CPS1Deformation.current_joint_addresses ∧
    type_of% @CPS1Deformation.current_joint_source ∧
    type_of% @CPS1Deformation.whole_inventory ∧
    type_of% @CPS1Deformation.actual_cut ∧
    type_of% @CPS1Deformation.true_guard_cut ∧
    type_of% @CPS1Deformation.inherited_guard_cut ∧
    type_of% @CPS1Deformation.failed_reaction_cannot_fire ∧
    type_of% @CPS1Deformation.legacy_phase_cut ∧
    type_of% @CPS1Deformation.pending_same ∧
    type_of% @CPS1Deformation.Source.source_preserved ∧
    type_of% @CPS1Deformation.resume_good ∧
    type_of% @CPS1Deformation.resume_noGuard ∧
    (@Material.deformationExecution (readMaterial runtime.tick.next)) = (@Material.deformationExecution (readMaterial runtime)) ∧
    (@Material.deformationResume (readMaterial runtime.tick.next)) = (@Material.deformationResume (readMaterial runtime)) ∧
    (@Material.deformationMaterial (readMaterial runtime.tick.next)) = (@Material.deformationMaterial (readMaterial runtime)) ∧
    (@Material.deformationAdopt (readMaterial runtime.tick.next)) = (@Material.deformationAdopt (readMaterial runtime)) ∧
    (@Material.deformationPulse (readMaterial runtime.tick.next)) = (@Material.deformationPulse (readMaterial runtime)) ∧
    (@Material.deformationDeposit (readMaterial runtime.tick.next)) = (@Material.deformationDeposit (readMaterial runtime)) ∧
    (@Material.deformationEnergy (readMaterial runtime.tick.next)) = (@Material.deformationEnergy (readMaterial runtime)) ∧
    (@Material.deformationFields (readMaterial runtime.tick.next)) = (@Material.deformationFields (readMaterial runtime)) ∧
    (@Material.deformationForce (readMaterial runtime.tick.next)) = (@Material.deformationForce (readMaterial runtime)) ∧
    (@Material.deformationAction (readMaterial runtime.tick.next)) = (@Material.deformationAction (readMaterial runtime)) ∧
    (@Material.deformationJoint (readMaterial runtime.tick.next)) = (@Material.deformationJoint (readMaterial runtime)) := by
  refine ⟨face_factorizes runtime (.component .material),face_factorizes runtime (.component .certificate),same_source_and_complete_ledger,rfl,rfl,rfl,
    rfl,rfl,rfl,rfl,rfl,rfl,
    rfl,rfl,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,
    ?_,rfl,rfl,rfl,rfl,rfl,
    rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact (readCertificate runtime).deformation.actualSource
  · exact (readCertificate runtime).deformation.sourceField
  · exact (readCertificate runtime).deformation.fieldFrechet
  · exact (readCertificate runtime).deformation.frameFrechet
  · exact (readCertificate runtime).deformation.gramFrechet
  · exact (readCertificate runtime).deformation.sourceUnit
  · exact (readCertificate runtime).deformation.covariantTangent
  · exact (readCertificate runtime).deformation.tangentGram
  · exact (readCertificate runtime).deformation.fullLift
  · exact (readCertificate runtime).deformation.nuclearEnergy
  · exact (readCertificate runtime).deformation.nuclearFrechet
  · exact (readCertificate runtime).deformation.fullFrechet
  · exact (readCertificate runtime).deformation.currentMomentumFrechet
  · exact (readCertificate runtime).deformation.electronicFrechet
  · exact (readCertificate runtime).deformation.electronicGradient
  · exact (readCertificate runtime).deformation.electronicFullJoint
  · exact (readCertificate runtime).deformation.physicalFock
  · exact (readCertificate runtime).deformation.normalizationRank
  · exact (readCertificate runtime).deformation.canonicalNormalization
  · exact (readCertificate runtime).deformation.normalizationGood
  · exact (readCertificate runtime).deformation.normalizationSpan
  · exact (readCertificate runtime).deformation.currentNormalization
  · exact (readCertificate runtime).deformation.wholeBasis
  · exact (readCertificate runtime).deformation.wholeBasisReadback
  · exact (readCertificate runtime).deformation.fockResponse
  · exact (readCertificate runtime).deformation.fockAction
  · exact (readCertificate runtime).deformation.fockMidpoint
  · exact (readCertificate runtime).deformation.adoption
  · exact (readCertificate runtime).deformation.adoptionGood
  · exact (readCertificate runtime).deformation.adoptionPayment
  · exact (readCertificate runtime).deformation.adoptionGrounded
  · exact (readCertificate runtime).deformation.adoptionSource
  · exact (readCertificate runtime).deformation.generatedAdoption
  · exact (readCertificate runtime).deformation.actualPulse
  · exact (readCertificate runtime).deformation.pulseGood
  · exact (readCertificate runtime).deformation.pulsePayment
  · exact (readCertificate runtime).deformation.pulseGrounded
  · exact (readCertificate runtime).deformation.wholeSource
  · exact (readCertificate runtime).deformation.force
  · exact (readCertificate runtime).deformation.nuclearWork
  · exact (readCertificate runtime).deformation.actualMidpoint
  · exact (readCertificate runtime).deformation.zeroTime
  · exact (readCertificate runtime).deformation.actualDeposit
  · exact (readCertificate runtime).deformation.depositPayment
  · exact (readCertificate runtime).deformation.generatedStock
  · exact (readCertificate runtime).deformation.currentFields
  · exact (readCertificate runtime).deformation.nativeCharge
  · exact (readCertificate runtime).deformation.wholeAddresses
  · exact (readCertificate runtime).deformation.wholeJoint
  · exact (readCertificate runtime).deformation.inventory
  · exact (readCertificate runtime).deformation.cut
  · exact (readCertificate runtime).deformation.trueGuardCut
  · exact (readCertificate runtime).deformation.inheritedGuardCut
  · exact (readCertificate runtime).deformation.failedCannotFire
  · exact (readCertificate runtime).deformation.legacyPhase
  · exact (readCertificate runtime).deformation.pending
  · exact (readCertificate runtime).deformation.sourceResume
  · exact (readCertificate runtime).deformation.continuationGood
  · exact (readCertificate runtime).deformation.continuationNoGuard

structure InstalledActualDelivery : Prop where
  completeParent : Supply.InstalledPhysicalSupply
  source : DeliveryClosure
  sourceLedger : type_of% same_source_and_complete_ledger
  exactOccurrenceAndNext : type_of% exact_parent_and_literal_next
  allFaces : ∀ runtime face, type_of% (face_factorizes runtime face)
  inheritedElevenFaces : type_of% original_eleven_faces_retained
  parentPhysicalSupply : Supply.PhysicalSupplyClosure
  parentLongitudinal : Longitudinal.LongitudinalClosure
  parentJointAlleles : Ngs.JointAlleleClosure
  parentProgram : OriginalProgramClosure
  originalOperation : Root.OperationAt (Root.Native.erase afterParent.current.visit.current)
  actualConsumer : type_of% next_consumes_actual_delivery
  resourceConsumer : type_of% (actual_resource_program afterParent)
  editingConsumer : ∀ edits, type_of% (actual_editing_program afterParent edits)
  executionConsumer : ∀ edits water, type_of% (actual_editing_execution afterParent edits water)
  continuedCodingConsumer : ∀ edits water additional,
    type_of% (actual_continued_coding afterParent edits water additional)
  endogenousTranslationConsumer : ∀ edits water additional,
    type_of% (actual_endogenous_translation afterParent edits water additional)
  boundaryTranslationConsumer : ∀ edits water additional raw,
    type_of% (actual_boundary_translation afterParent edits water additional raw)
  recyclingConsumer : ∀ edits water additional site events feed,
    type_of% (actual_recycling afterParent edits water additional site events feed)
  reinitiationConsumer : ∀ edits water additional path recycleFeed scanFeed feed,
    type_of% (actual_reinitiation afterParent edits water additional path recycleFeed scanFeed feed)
  stockRecursionConsumer : ∀ edits water additional path recycleFeed scanFeed bodyFeed feeds depth,
    type_of% (actual_stock_recursion afterParent edits water additional path recycleFeed scanFeed bodyFeed feeds depth)
  localChemicalConsumer : type_of% (actual_local_chemical afterParent)
  editingChemicalConsumer : type_of% (actual_editing_chemical_join afterParent)
  atomicSourceConsumer : type_of% (actual_atomic_source afterParent)
  atomicDynamicsConsumer : type_of% (actual_atomic_dynamics afterParent)
  enzymeBathConsumer : type_of% (actual_enzyme_bath afterParent)
  electronicConsumer : type_of% (actual_electronic_source afterParent)
  quantumNuclearConsumer : type_of% (actual_quantum_nuclear afterParent)
  followingConsumer : type_of% (actual_following afterParent)
  molecularConsumer : type_of% (actual_molecular afterParent)
  deformationConsumer : type_of% (actual_deformation afterParent)
  positiveConsumer : type_of% (actual_positive afterParent)
  continuationConsumer : type_of% (actual_continuation afterParent)
  addressedConsumer : type_of% (actual_addressed afterParent)
  addressedRenewalConsumer : type_of% (actual_addressed_renewal afterParent)
  bondRenewalConsumer : type_of% (actual_bond_renewal afterParent)
  interactionConsumer : type_of% (actual_interaction afterParent)
  pairCurrentConsumer : type_of% (actual_pair_current afterParent)
  sourceMaterialConsumer : type_of% (actual_source_material_lineage afterParent)
  atomicHydrolysisConsumer : type_of% (actual_atomic_hydrolysis afterParent)
  reactiveJointConsumer : type_of% (actual_reactive_joint afterParent)
  reactiveFieldConsumer : type_of% (actual_reactive_field afterParent)
  reactiveFieldStageConsumer : type_of% (@actual_field_stage_paid afterParent)
  reactiveFieldGeneratedStageConsumer : type_of% (@actual_field_generated_stages afterParent)
  reactiveFieldDynamicsConsumer : type_of% (actual_reactive_field_dynamics afterParent)
  reactiveFieldDynamicsStepConsumer : type_of% (@actual_field_dynamics_step afterParent)
  reactiveFieldDynamicsPulseConsumer : type_of% (@actual_field_dynamics_pulse_paid afterParent)
  reactiveFieldDynamicsFiniteConsumer : type_of% (@actual_field_dynamics_finite afterParent)
  reactiveFieldDynamicsGeneratedConsumer : type_of% (@actual_field_dynamics_generated_pulses afterParent)
  reactiveNuclearConsumer : type_of% (actual_reactive_nuclear afterParent)
  reactiveNuclearSourceReadout : type_of% (@nuclear_source_readout_exact afterParent)
  reactiveNuclearAdvanceReadout : type_of% (@nuclear_advance_readout_exact afterParent)
  reactiveNuclearAtomicConsumer : type_of% (@actual_nuclear_chemical_next afterParent)

  reactiveJointNuclearConsumer : type_of% (actual_reactive_joint_nuclear afterParent)
  reactiveJointNuclearSourceReadout : type_of% (@joint_nuclear_source_readout_exact afterParent)
  reactiveJointNuclearAdvanceReadout : type_of% (@joint_nuclear_advance_readout_exact afterParent)
  reactiveJointNuclearStepConsumer : type_of% (@actual_joint_nuclear_step afterParent)
  reactiveJointNuclearFiniteConsumer : type_of% (@actual_joint_nuclear_finite_chemical afterParent)
  reactiveJointNuclearChemicalConsumer : type_of% (@actual_joint_nuclear_chemical_next afterParent)
  sourceEntryConsumer : type_of% (actual_source_entry afterParent)
  sourceEntrySelectedConsumer : type_of% (@actual_source_entry_selected afterParent)
  sourceEntryReadoutConsumer : type_of% (@source_entry_readout_exact afterParent)
  liveEditingConsumer : type_of% (actual_live_editing afterParent)
  liveEditingSelectedConsumer : type_of% (@actual_live_editing_selected afterParent)
  liveEditingReadoutConsumer : type_of% (@live_editing_readout_exact afterParent)
  biologicalRepairConsumer : type_of% (actual_biological_repair afterParent)
  biologicalRepairMethodConsumer : type_of% (@biological_repair_method_exact afterParent)
  biologicalRepairSelectedConsumer : type_of% (@actual_biological_repair_selected afterParent)
  sameEventFunctionConsumer : type_of% (actual_same_event_function afterParent)
  sameEventFunctionMethodConsumer : type_of% (@same_event_function_method_exact afterParent)
  sameEventFunctionSelectedConsumer : type_of% (@actual_same_event_function_selected afterParent)
  phosphorylExchangeConsumer : type_of% (actual_phosphoryl_exchange afterParent)
  phosphorylExchangeMethodConsumer : type_of% (@phosphoryl_exchange_method_exact afterParent)
  phosphorylExchangeSelectedConsumer : type_of% (@actual_phosphoryl_exchange_selected afterParent)
  nativeIncidenceConsumer : type_of% (@native_incidence_root_consumer afterParent)

theorem sourceGeneratedCPS1ActualDeliveryAtNext : InstalledActualDelivery :=
  ⟨complete_parent,readCertificate afterParent,same_source_and_complete_ledger,
   exact_parent_and_literal_next,face_factorizes,original_eleven_faces_retained,
   inherited_complete_physical_supply afterParent,inherited_complete_longitudinal afterParent,
   inherited_complete_joint_alleles afterParent,inherited_complete_program afterParent,
   actual_original_operation afterParent,next_consumes_actual_delivery,
   actual_resource_program afterParent,actual_editing_program afterParent,
   actual_editing_execution afterParent,actual_continued_coding afterParent,
   actual_endogenous_translation afterParent,actual_boundary_translation afterParent,actual_recycling afterParent,
   actual_reinitiation afterParent,actual_stock_recursion afterParent,actual_local_chemical afterParent,actual_editing_chemical_join afterParent,actual_atomic_source afterParent,actual_atomic_dynamics afterParent,actual_enzyme_bath afterParent,actual_electronic_source afterParent,actual_quantum_nuclear afterParent,actual_following afterParent,actual_molecular afterParent,actual_deformation afterParent,actual_positive afterParent,actual_continuation afterParent,actual_addressed afterParent,actual_addressed_renewal afterParent,actual_bond_renewal afterParent,actual_interaction afterParent,actual_pair_current afterParent,actual_source_material_lineage afterParent,actual_atomic_hydrolysis afterParent,actual_reactive_joint afterParent,actual_reactive_field afterParent,@actual_field_stage_paid afterParent,@actual_field_generated_stages afterParent,actual_reactive_field_dynamics afterParent,@actual_field_dynamics_step afterParent,@actual_field_dynamics_pulse_paid afterParent,@actual_field_dynamics_finite afterParent,@actual_field_dynamics_generated_pulses afterParent,actual_reactive_nuclear afterParent,
   @nuclear_source_readout_exact afterParent,@nuclear_advance_readout_exact afterParent,
   @actual_nuclear_chemical_next afterParent,
   actual_reactive_joint_nuclear afterParent,
   @joint_nuclear_source_readout_exact afterParent,
   @joint_nuclear_advance_readout_exact afterParent,
   @actual_joint_nuclear_step afterParent,
   @actual_joint_nuclear_finite_chemical afterParent,
   @actual_joint_nuclear_chemical_next afterParent,
   actual_source_entry afterParent,
   @actual_source_entry_selected afterParent,
   @source_entry_readout_exact afterParent,
   actual_live_editing afterParent,
   @actual_live_editing_selected afterParent,
   @live_editing_readout_exact afterParent,
   actual_biological_repair afterParent,
   @biological_repair_method_exact afterParent,
   @actual_biological_repair_selected afterParent,
   actual_same_event_function afterParent,
   @same_event_function_method_exact afterParent,
   @actual_same_event_function_selected afterParent,
   actual_phosphoryl_exchange afterParent,
   @phosphoryl_exchange_method_exact afterParent,
   @actual_phosphoryl_exchange_selected afterParent,
   @native_incidence_root_consumer afterParent⟩

end

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery
