import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKReceiptSourceData

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback
open Complex MeasureTheory Set
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open RootInquiryCompletion
open CofinalHistorySettlement
open private traceBranches_append from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed
noncomputable section
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (depth : Nat) (half : OriginalKCombCalculation.Half observation)

private def appendSourceExposure {X : Type} (prior fresh : RootedAccountedUnfolding X) :
    RootedAccountedUnfolding X :=
  match prior with
  | .occur origin branches => .occur origin (branches.append (AccountedBranches.singleton fresh))

private theorem append_source_exposure_trace {X : Type} (prior fresh : RootedAccountedUnfolding X) :
    (appendSourceExposure prior fresh).trace = prior.trace ++ fresh.trace := by
  cases prior with
  | occur origin branches =>
    change origin :: RootedAccountedUnfolding.traceBranches
      (branches.append (AccountedBranches.singleton fresh)) = _
    rw [traceBranches_append]
    change origin :: (RootedAccountedUnfolding.traceBranches branches ++ (fresh.trace ++ [])) =
      origin :: (RootedAccountedUnfolding.traceBranches branches ++ fresh.trace)
    rw [List.append_nil]

def wholeDebtRCalculationInventory :=
  SourceHistoryCommon.seed
    (priorSourceCalculationInventory observation nontrivial depth half)
    (SourceOperationPaidRelations.exposure (wholeDebtRSourceTrace observation nontrivial depth half))

/-- Both literal calculations enter the existing frame before its source inventory emits. -/
def waveSourceCalculationInventory :=
  SourceHistoryCommon.seed
    (wholeDebtRCalculationInventory observation nontrivial depth half)
    (SourceOperationPaidRelations.exposure (wholeDebtRWaveSourceTrace observation nontrivial depth half))

def reciprocalSourceCalculationInventory :=
  appendSourceExposure (waveSourceCalculationInventory observation nontrivial depth half)
    (SourceOperationPaidRelations.exposure (wholeDebtRReciprocalSourceTrace observation nontrivial depth half))

def primitiveMobiusSourceExposure (index : Fin 3) :=
  SourceOperationPaidRelations.exposure (wholeDebtRPrimitiveMobiusSourceTrace observation nontrivial depth half index)

def primitiveMobiusTraceBlocks :=
  (primitiveMobiusSourceExposure observation nontrivial depth half 0).trace ++
    (primitiveMobiusSourceExposure observation nontrivial depth half 1).trace ++
      (primitiveMobiusSourceExposure observation nontrivial depth half 2).trace

def primitiveSourceCalculationInventory :=
  appendSourceExposure
    (appendSourceExposure
      (appendSourceExposure (reciprocalSourceCalculationInventory observation nontrivial depth half)
        (primitiveMobiusSourceExposure observation nontrivial depth half 0))
      (primitiveMobiusSourceExposure observation nontrivial depth half 1))
    (primitiveMobiusSourceExposure observation nontrivial depth half 2)

def jointMobiusSourceExposure (field : Fin 2) :=
  SourceOperationPaidRelations.exposure (wholeDebtRJointMobiusSourceTrace observation nontrivial depth half field)

def jointMobiusTraceBlocks :=
  (jointMobiusSourceExposure observation nontrivial depth half 0).trace ++
    (jointMobiusSourceExposure observation nontrivial depth half 1).trace

def jointSourceCalculationInventory :=
  appendSourceExposure
    (appendSourceExposure (primitiveSourceCalculationInventory observation nontrivial depth half)
      (jointMobiusSourceExposure observation nontrivial depth half 0))
    (jointMobiusSourceExposure observation nontrivial depth half 1)

def returnJordanSourceExposure (field : Fin 2) :=
  SourceOperationPaidRelations.exposure (returnJordanSourceTrace observation nontrivial depth half field)

def returnJordanTraceBlocks :=
  (returnJordanSourceExposure observation nontrivial depth half 0).trace ++
    (returnJordanSourceExposure observation nontrivial depth half 1).trace

def returnJordanSourceCalculationInventory :=
  appendSourceExposure
    (appendSourceExposure (jointSourceCalculationInventory observation nontrivial depth half)
      (returnJordanSourceExposure observation nontrivial depth half 0))
    (returnJordanSourceExposure observation nontrivial depth half 1)

def forcedSourceExposure :=
  SourceOperationPaidRelations.exposure (forcedSourceTrace observation nontrivial depth half)

def forcedTraceBlocks := (forcedSourceExposure observation nontrivial depth half).trace

def forcedSourceCalculationInventory :=
  appendSourceExposure (returnJordanSourceCalculationInventory observation nontrivial depth half)
    (forcedSourceExposure observation nontrivial depth half)

def returnJetSourceExposure (field : Fin 2) :=
  SourceOperationPaidRelations.exposure (returnJetSourceTrace observation nontrivial depth half field)

def returnJetTraceBlocks :=
  (returnJetSourceExposure observation nontrivial depth half 0).trace ++
    (returnJetSourceExposure observation nontrivial depth half 1).trace

def returnJetSourceCalculationInventory :=
  appendSourceExposure
    (appendSourceExposure (forcedSourceCalculationInventory observation nontrivial depth half)
      (returnJetSourceExposure observation nontrivial depth half 0))
    (returnJetSourceExposure observation nontrivial depth half 1)

def paNativePortSourceExposure (field : Fin 2) :=
  SourceOperationPaidRelations.exposure (paNativePortSourceTrace observation nontrivial depth half field)

def paNativePortTraceBlocks :=
  (paNativePortSourceExposure observation nontrivial depth half 0).trace ++
    (paNativePortSourceExposure observation nontrivial depth half 1).trace

def paNativePortSourceCalculationInventory :=
  appendSourceExposure
    (appendSourceExposure (returnJetSourceCalculationInventory observation nontrivial depth half)
      (paNativePortSourceExposure observation nontrivial depth half 0))
    (paNativePortSourceExposure observation nontrivial depth half 1)

def paNativeCayleySourceExposure (field : Fin 3) :=
  SourceOperationPaidRelations.exposure (paNativeCayleySourceTrace observation nontrivial depth half field)

def paNativeCayleyTraceBlocks :=
  (paNativeCayleySourceExposure observation nontrivial depth half 0).trace ++
    (paNativeCayleySourceExposure observation nontrivial depth half 1).trace ++
      (paNativeCayleySourceExposure observation nontrivial depth half 2).trace

def sourceCalculationInventory :=
  appendSourceExposure
    (appendSourceExposure
      (appendSourceExposure (paNativePortSourceCalculationInventory observation nontrivial depth half)
        (paNativeCayleySourceExposure observation nontrivial depth half 0))
      (paNativeCayleySourceExposure observation nontrivial depth half 1))
    (paNativeCayleySourceExposure observation nontrivial depth half 2)

def nativeMobiusTraceBlocks :=
  primitiveMobiusTraceBlocks observation nontrivial depth half ++
    jointMobiusTraceBlocks observation nontrivial depth half ++
      returnJordanTraceBlocks observation nontrivial depth half ++
      forcedTraceBlocks observation nontrivial depth half ++
      returnJetTraceBlocks observation nontrivial depth half ++
      paNativePortTraceBlocks observation nontrivial depth half ++
      paNativeCayleyTraceBlocks observation nontrivial depth half

theorem source_calculation_inventory_suffix :
    (sourceCalculationInventory observation nontrivial depth half).trace =
      (reciprocalSourceCalculationInventory observation nontrivial depth half).trace ++
        nativeMobiusTraceBlocks observation nontrivial depth half := by
  simp only [sourceCalculationInventory, paNativePortSourceCalculationInventory, paNativeCayleyTraceBlocks, returnJetSourceCalculationInventory, paNativePortTraceBlocks, forcedSourceCalculationInventory, returnJetTraceBlocks, returnJordanSourceCalculationInventory, jointSourceCalculationInventory, primitiveSourceCalculationInventory, append_source_exposure_trace,
    nativeMobiusTraceBlocks, primitiveMobiusTraceBlocks, jointMobiusTraceBlocks, returnJordanTraceBlocks, forcedTraceBlocks, List.append_assoc]

def reciprocalSourceCalculationInventorySegment : SourceInventoryTraceSegment
    (reciprocalSourceCalculationInventory observation nontrivial depth half)
    (sourceCalculationInventory observation nontrivial depth half) :=
  ⟨[], nativeMobiusTraceBlocks observation nontrivial depth half, by
    simpa only [List.nil_append] using source_calculation_inventory_suffix observation nontrivial depth half⟩

def sourceCalculationPriorSegment : SourceInventoryTraceSegment
    (waveSourceCalculationInventory observation nontrivial depth half)
    (sourceCalculationInventory observation nontrivial depth half) :=
  (show SourceInventoryTraceSegment
    (waveSourceCalculationInventory observation nontrivial depth half)
    (reciprocalSourceCalculationInventory observation nontrivial depth half) from
      ⟨[], (SourceOperationPaidRelations.exposure
        (wholeDebtRReciprocalSourceTrace observation nontrivial depth half)).trace, by
          simpa only [reciprocalSourceCalculationInventory, List.nil_append] using append_source_exposure_trace
            (waveSourceCalculationInventory observation nontrivial depth half)
            (SourceOperationPaidRelations.exposure (wholeDebtRReciprocalSourceTrace observation nontrivial depth half))⟩).trans
    (reciprocalSourceCalculationInventorySegment observation nontrivial depth half)

def reciprocalSourceCalculationSegment : SourceInventoryTraceSegment
    (SourceOperationPaidRelations.exposure (wholeDebtRReciprocalSourceTrace observation nontrivial depth half))
    (sourceCalculationInventory observation nontrivial depth half) :=
  (show SourceInventoryTraceSegment
    (SourceOperationPaidRelations.exposure (wholeDebtRReciprocalSourceTrace observation nontrivial depth half))
    (reciprocalSourceCalculationInventory observation nontrivial depth half) from
      ⟨(waveSourceCalculationInventory observation nontrivial depth half).trace, [], by
        simpa only [reciprocalSourceCalculationInventory, List.append_nil] using append_source_exposure_trace
          (waveSourceCalculationInventory observation nontrivial depth half)
          (SourceOperationPaidRelations.exposure (wholeDebtRReciprocalSourceTrace observation nontrivial depth half))⟩).trans
    (reciprocalSourceCalculationInventorySegment observation nontrivial depth half)

def primitiveMobiusSourceCalculationSegment (index : Fin 3) : SourceInventoryTraceSegment
    (primitiveMobiusSourceExposure observation nontrivial depth half index)
    (sourceCalculationInventory observation nontrivial depth half) := by
  refine Fin.cases ?_ (fun rest => Fin.cases ?_
    (fun last => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) last) rest) index
  · refine ⟨(reciprocalSourceCalculationInventory observation nontrivial depth half).trace,
      (primitiveMobiusSourceExposure observation nontrivial depth half 1).trace ++
        (primitiveMobiusSourceExposure observation nontrivial depth half 2).trace ++
        jointMobiusTraceBlocks observation nontrivial depth half ++
        returnJordanTraceBlocks observation nontrivial depth half ++
      forcedTraceBlocks observation nontrivial depth half ++
        returnJetTraceBlocks observation nontrivial depth half ++
        paNativePortTraceBlocks observation nontrivial depth half ++
        paNativeCayleyTraceBlocks observation nontrivial depth half, ?_⟩
    simpa only [nativeMobiusTraceBlocks, primitiveMobiusTraceBlocks, jointMobiusTraceBlocks, returnJordanTraceBlocks, forcedTraceBlocks, List.append_assoc] using
      source_calculation_inventory_suffix observation nontrivial depth half
  · refine ⟨(reciprocalSourceCalculationInventory observation nontrivial depth half).trace ++
      (primitiveMobiusSourceExposure observation nontrivial depth half 0).trace,
      (primitiveMobiusSourceExposure observation nontrivial depth half 2).trace ++
        jointMobiusTraceBlocks observation nontrivial depth half ++
        returnJordanTraceBlocks observation nontrivial depth half ++
      forcedTraceBlocks observation nontrivial depth half ++
        returnJetTraceBlocks observation nontrivial depth half ++
        paNativePortTraceBlocks observation nontrivial depth half ++
        paNativeCayleyTraceBlocks observation nontrivial depth half, ?_⟩
    have index_eq : ((0 : Fin 2).succ : Fin 3)=1 := rfl
    simpa only [index_eq, nativeMobiusTraceBlocks, primitiveMobiusTraceBlocks, jointMobiusTraceBlocks, returnJordanTraceBlocks, forcedTraceBlocks, List.append_assoc] using
      source_calculation_inventory_suffix observation nontrivial depth half
  · refine ⟨(reciprocalSourceCalculationInventory observation nontrivial depth half).trace ++
      (primitiveMobiusSourceExposure observation nontrivial depth half 0).trace ++
        (primitiveMobiusSourceExposure observation nontrivial depth half 1).trace,
      jointMobiusTraceBlocks observation nontrivial depth half ++
        returnJordanTraceBlocks observation nontrivial depth half ++
      forcedTraceBlocks observation nontrivial depth half ++
        returnJetTraceBlocks observation nontrivial depth half ++
        paNativePortTraceBlocks observation nontrivial depth half ++
        paNativeCayleyTraceBlocks observation nontrivial depth half, ?_⟩
    have index_eq : ((0 : Fin 1).succ.succ : Fin 3)=2 := rfl
    simpa only [index_eq, nativeMobiusTraceBlocks, primitiveMobiusTraceBlocks, jointMobiusTraceBlocks, returnJordanTraceBlocks, forcedTraceBlocks, List.append_assoc, List.append_nil] using
      source_calculation_inventory_suffix observation nontrivial depth half

def jointMobiusSourceCalculationSegment (field : Fin 2) : SourceInventoryTraceSegment
    (jointMobiusSourceExposure observation nontrivial depth half field)
    (sourceCalculationInventory observation nontrivial depth half) := by
  refine Fin.cases ?_ (fun rest => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) rest) field
  · refine ⟨(primitiveSourceCalculationInventory observation nontrivial depth half).trace,
      (jointMobiusSourceExposure observation nontrivial depth half 1).trace ++
        returnJordanTraceBlocks observation nontrivial depth half ++
      forcedTraceBlocks observation nontrivial depth half ++
        returnJetTraceBlocks observation nontrivial depth half ++
        paNativePortTraceBlocks observation nontrivial depth half ++
        paNativeCayleyTraceBlocks observation nontrivial depth half, ?_⟩
    simp only [sourceCalculationInventory, paNativePortSourceCalculationInventory, paNativeCayleyTraceBlocks, returnJetSourceCalculationInventory, paNativePortTraceBlocks, forcedSourceCalculationInventory, returnJetTraceBlocks, returnJordanSourceCalculationInventory, jointSourceCalculationInventory, append_source_exposure_trace, returnJordanTraceBlocks, forcedTraceBlocks, List.append_assoc]
  · refine ⟨(primitiveSourceCalculationInventory observation nontrivial depth half).trace ++
      (jointMobiusSourceExposure observation nontrivial depth half 0).trace,
      returnJordanTraceBlocks observation nontrivial depth half ++
      forcedTraceBlocks observation nontrivial depth half ++
        returnJetTraceBlocks observation nontrivial depth half ++
        paNativePortTraceBlocks observation nontrivial depth half ++
        paNativeCayleyTraceBlocks observation nontrivial depth half, ?_⟩
    have index_eq : ((0 : Fin 1).succ : Fin 2) = 1 := rfl
    simp only [index_eq, sourceCalculationInventory, paNativePortSourceCalculationInventory, paNativeCayleyTraceBlocks, returnJetSourceCalculationInventory, paNativePortTraceBlocks, forcedSourceCalculationInventory, returnJetTraceBlocks, returnJordanSourceCalculationInventory, jointSourceCalculationInventory, append_source_exposure_trace, returnJordanTraceBlocks, forcedTraceBlocks, List.append_assoc]

def returnJordanSourceCalculationSegment (field : Fin 2) : SourceInventoryTraceSegment
    (returnJordanSourceExposure observation nontrivial depth half field)
    (sourceCalculationInventory observation nontrivial depth half) := by
  refine Fin.cases ?_ (fun rest => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) rest) field
  · refine ⟨(jointSourceCalculationInventory observation nontrivial depth half).trace,
      (returnJordanSourceExposure observation nontrivial depth half 1).trace ++
        forcedTraceBlocks observation nontrivial depth half ++
        returnJetTraceBlocks observation nontrivial depth half ++
        paNativePortTraceBlocks observation nontrivial depth half ++
        paNativeCayleyTraceBlocks observation nontrivial depth half, ?_⟩
    simp only [sourceCalculationInventory, paNativePortSourceCalculationInventory, paNativeCayleyTraceBlocks, returnJetSourceCalculationInventory, paNativePortTraceBlocks, forcedSourceCalculationInventory, returnJetTraceBlocks, returnJordanSourceCalculationInventory, append_source_exposure_trace, forcedTraceBlocks, List.append_assoc]
  · refine ⟨(jointSourceCalculationInventory observation nontrivial depth half).trace ++
      (returnJordanSourceExposure observation nontrivial depth half 0).trace,
      forcedTraceBlocks observation nontrivial depth half ++
        returnJetTraceBlocks observation nontrivial depth half ++
        paNativePortTraceBlocks observation nontrivial depth half ++
        paNativeCayleyTraceBlocks observation nontrivial depth half, ?_⟩
    have index_eq : ((0 : Fin 1).succ : Fin 2) = 1 := rfl
    simp only [index_eq, sourceCalculationInventory, paNativePortSourceCalculationInventory, paNativeCayleyTraceBlocks, returnJetSourceCalculationInventory, paNativePortTraceBlocks, forcedSourceCalculationInventory, returnJetTraceBlocks, returnJordanSourceCalculationInventory, append_source_exposure_trace, forcedTraceBlocks, List.append_assoc]

def forcedSourceCalculationSegment : SourceInventoryTraceSegment
    (forcedSourceExposure observation nontrivial depth half)
    (sourceCalculationInventory observation nontrivial depth half) :=
  ⟨(returnJordanSourceCalculationInventory observation nontrivial depth half).trace,
    returnJetTraceBlocks observation nontrivial depth half ++
        paNativePortTraceBlocks observation nontrivial depth half ++
        paNativeCayleyTraceBlocks observation nontrivial depth half, by
    simp only [sourceCalculationInventory, paNativePortSourceCalculationInventory, paNativeCayleyTraceBlocks, returnJetSourceCalculationInventory, paNativePortTraceBlocks, forcedSourceCalculationInventory, returnJetTraceBlocks,
      append_source_exposure_trace, List.append_assoc]⟩

def returnJetSourceCalculationSegment (field : Fin 2) : SourceInventoryTraceSegment
    (returnJetSourceExposure observation nontrivial depth half field)
    (sourceCalculationInventory observation nontrivial depth half) := by
  refine Fin.cases ?_ (fun rest => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) rest) field
  · refine ⟨(forcedSourceCalculationInventory observation nontrivial depth half).trace,
      (returnJetSourceExposure observation nontrivial depth half 1).trace ++
      paNativePortTraceBlocks observation nontrivial depth half ++
        paNativeCayleyTraceBlocks observation nontrivial depth half, ?_⟩
    simp only [sourceCalculationInventory, paNativePortSourceCalculationInventory, paNativeCayleyTraceBlocks, returnJetSourceCalculationInventory, paNativePortTraceBlocks, append_source_exposure_trace, List.append_assoc]
  · refine ⟨(forcedSourceCalculationInventory observation nontrivial depth half).trace ++
      (returnJetSourceExposure observation nontrivial depth half 0).trace,
      paNativePortTraceBlocks observation nontrivial depth half ++
        paNativeCayleyTraceBlocks observation nontrivial depth half, ?_⟩
    have index_eq : ((0 : Fin 1).succ : Fin 2) = 1 := rfl
    simp only [index_eq, sourceCalculationInventory, paNativePortSourceCalculationInventory, paNativeCayleyTraceBlocks, returnJetSourceCalculationInventory, paNativePortTraceBlocks, append_source_exposure_trace, List.append_assoc]

def paNativePortSourceCalculationSegment (field : Fin 2) : SourceInventoryTraceSegment
    (paNativePortSourceExposure observation nontrivial depth half field)
    (sourceCalculationInventory observation nontrivial depth half) := by
  refine Fin.cases ?_ (fun rest => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) rest) field
  · refine ⟨(returnJetSourceCalculationInventory observation nontrivial depth half).trace,
      (paNativePortSourceExposure observation nontrivial depth half 1).trace ++
        paNativeCayleyTraceBlocks observation nontrivial depth half, ?_⟩
    simp only [sourceCalculationInventory, paNativePortSourceCalculationInventory, paNativeCayleyTraceBlocks,
      append_source_exposure_trace, List.append_assoc]
  · refine ⟨(returnJetSourceCalculationInventory observation nontrivial depth half).trace ++
      (paNativePortSourceExposure observation nontrivial depth half 0).trace,
      paNativeCayleyTraceBlocks observation nontrivial depth half, ?_⟩
    have index_eq : ((0 : Fin 1).succ : Fin 2) = 1 := rfl
    simp only [index_eq, sourceCalculationInventory, paNativePortSourceCalculationInventory,
      paNativeCayleyTraceBlocks, append_source_exposure_trace, List.append_assoc]

def paNativeCayleySourceCalculationSegment (field : Fin 3) : SourceInventoryTraceSegment
    (paNativeCayleySourceExposure observation nontrivial depth half field)
    (sourceCalculationInventory observation nontrivial depth half) := by
  refine Fin.cases ?_ (fun rest => Fin.cases ?_
    (fun last => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) last) rest) field
  · refine ⟨(paNativePortSourceCalculationInventory observation nontrivial depth half).trace,
      (paNativeCayleySourceExposure observation nontrivial depth half 1).trace ++
        (paNativeCayleySourceExposure observation nontrivial depth half 2).trace, ?_⟩
    simp only [sourceCalculationInventory, append_source_exposure_trace, List.append_assoc]
  · refine ⟨(paNativePortSourceCalculationInventory observation nontrivial depth half).trace ++
      (paNativeCayleySourceExposure observation nontrivial depth half 0).trace,
      (paNativeCayleySourceExposure observation nontrivial depth half 2).trace, ?_⟩
    have index_eq : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
    simp only [index_eq, sourceCalculationInventory, append_source_exposure_trace, List.append_assoc]
  · refine ⟨(paNativePortSourceCalculationInventory observation nontrivial depth half).trace ++
      (paNativeCayleySourceExposure observation nontrivial depth half 0).trace ++
        (paNativeCayleySourceExposure observation nontrivial depth half 1).trace, [], ?_⟩
    have index_eq : ((0 : Fin 1).succ.succ : Fin 3) = 2 := rfl
    simp only [index_eq, sourceCalculationInventory, append_source_exposure_trace,
      List.append_assoc, List.append_nil]

theorem pa_native_cayley_source_preserved (field : Fin 3) (event)
    (present : event ∈ (paNativeCayleySourceExposure observation nontrivial depth half field).trace) :
    event ∈ (sourceCalculationInventory observation nontrivial depth half).trace :=
  (paNativeCayleySourceCalculationSegment observation nontrivial depth half field).present event present


theorem pa_native_port_source_preserved (field : Fin 2) (event)
    (present : event ∈ (paNativePortSourceExposure observation nontrivial depth half field).trace) :
    event ∈ (sourceCalculationInventory observation nontrivial depth half).trace :=
  (paNativePortSourceCalculationSegment observation nontrivial depth half field).present event present

theorem return_jet_source_preserved (field : Fin 2) (event)
    (present : event ∈ (returnJetSourceExposure observation nontrivial depth half field).trace) :
    event ∈ (sourceCalculationInventory observation nontrivial depth half).trace :=
  (returnJetSourceCalculationSegment observation nontrivial depth half field).present event present

theorem forced_source_preserved (event)
    (present : event ∈ (forcedSourceExposure observation nontrivial depth half).trace) :
    event ∈ (sourceCalculationInventory observation nontrivial depth half).trace :=
  (forcedSourceCalculationSegment observation nontrivial depth half).present event present

theorem return_jordan_source_preserved (field : Fin 2) (event)
    (present : event ∈ (returnJordanSourceExposure observation nontrivial depth half field).trace) :
    event ∈ (sourceCalculationInventory observation nontrivial depth half).trace :=
  (returnJordanSourceCalculationSegment observation nontrivial depth half field).present event present

theorem whole_debt_R_joint_mobius_source_preserved (field : Fin 2) (event)
    (present : event ∈ (jointMobiusSourceExposure observation nontrivial depth half field).trace) :
    event ∈ (sourceCalculationInventory observation nontrivial depth half).trace :=
  (jointMobiusSourceCalculationSegment observation nontrivial depth half field).present event present

theorem whole_debt_R_calculations_preserved (event)
    (present : event ∈ (wholeDebtRCalculationInventory observation nontrivial depth half).trace) :
    event ∈ (sourceCalculationInventory observation nontrivial depth half).trace :=
  (sourceCalculationPriorSegment observation nontrivial depth half).present event
    ((SourceHistoryCommon.parallel_left _ _ _).1 _ present)

theorem prior_source_calculations_preserved (event)
    (present : event ∈ (priorSourceCalculationInventory observation nontrivial depth half).trace) :
    event ∈ (sourceCalculationInventory observation nontrivial depth half).trace :=
  whole_debt_R_calculations_preserved observation nontrivial depth half event
    ((SourceHistoryCommon.parallel_left _ _ _).1 _ present)

theorem whole_debt_R_source_preserved (event)
    (present : event ∈
      (SourceOperationPaidRelations.exposure (wholeDebtRSourceTrace observation nontrivial depth half)).trace) :
    event ∈ (sourceCalculationInventory observation nontrivial depth half).trace :=
  whole_debt_R_calculations_preserved observation nontrivial depth half event
    ((SourceHistoryCommon.parallel_right _ _ _).1 _ present)

theorem whole_debt_R_wave_source_preserved (event)
    (present : event ∈
      (SourceOperationPaidRelations.exposure (wholeDebtRWaveSourceTrace observation nontrivial depth half)).trace) :
    event ∈ (sourceCalculationInventory observation nontrivial depth half).trace :=
  (sourceCalculationPriorSegment observation nontrivial depth half).present event
    ((SourceHistoryCommon.parallel_right _ _ _).1 _ present)

theorem whole_debt_R_reciprocal_source_preserved (event)
    (present : event ∈ (SourceOperationPaidRelations.exposure
      (wholeDebtRReciprocalSourceTrace observation nontrivial depth half)).trace) :
    event ∈ (sourceCalculationInventory observation nontrivial depth half).trace :=
  (reciprocalSourceCalculationSegment observation nontrivial depth half).present event present

theorem source_calculation_inventory_trace :
    (sourceCalculationInventory observation nontrivial depth half).trace =
      (wholeDebtRCalculationInventory observation nontrivial depth half).root ::
        ((wholeDebtRCalculationInventory observation nontrivial depth half).trace ++
          ((SourceOperationPaidRelations.exposure
            (wholeDebtRWaveSourceTrace observation nontrivial depth half)).trace ++
           ((SourceOperationPaidRelations.exposure
            (wholeDebtRReciprocalSourceTrace observation nontrivial depth half)).trace ++
              nativeMobiusTraceBlocks observation nontrivial depth half))) := by
  rw [source_calculation_inventory_suffix, reciprocalSourceCalculationInventory, append_source_exposure_trace]
  have seed_trace {X : Type} (left right : RootedAccountedUnfolding X) :
      (SourceHistoryCommon.seed left right).trace =
        left.root :: (left.trace ++ (right.trace ++ [])) := rfl
  rw [waveSourceCalculationInventory, seed_trace]
  simp only [List.append_nil, List.cons_append, List.append_assoc]

def priorSourcePaidInventory :=
  SourceHistoryCommon.seed
    (SourceOperationPaidRelations.exposure (receipt observation nontrivial depth half).2.1.2)
    (waveSourceCalculationInventory observation nontrivial depth half)

def sourcePaidInventory :=
  SourceHistoryCommon.seed
    (SourceOperationPaidRelations.exposure (receipt observation nontrivial depth half).2.1.2)
    (sourceCalculationInventory observation nontrivial depth half)

def sourcePaidInventoryPriorSegment : SourceInventoryTraceSegment
    (priorSourcePaidInventory observation nontrivial depth half)
    (sourcePaidInventory observation nontrivial depth half) := by
  refine ⟨[], (SourceOperationPaidRelations.exposure
    (wholeDebtRReciprocalSourceTrace observation nontrivial depth half)).trace ++
      nativeMobiusTraceBlocks observation nontrivial depth half, ?_⟩
  have seed_trace {X : Type} (left right : RootedAccountedUnfolding X) :
      (SourceHistoryCommon.seed left right).trace =
        left.root :: (left.trace ++ (right.trace ++ [])) := rfl
  rw [sourcePaidInventory, priorSourcePaidInventory, seed_trace, seed_trace,
    source_calculation_inventory_suffix, reciprocalSourceCalculationInventory, append_source_exposure_trace]
  simp only [List.nil_append, List.append_nil, List.cons_append, List.append_assoc]

def reciprocalSourceSegment : SourceInventoryTraceSegment
    (SourceOperationPaidRelations.exposure (wholeDebtRReciprocalSourceTrace observation nontrivial depth half))
    (sourcePaidInventory observation nontrivial depth half) :=
  (reciprocalSourceCalculationSegment observation nontrivial depth half).trans
    (SourceInventoryTraceSegment.right
      (SourceOperationPaidRelations.exposure (receipt observation nontrivial depth half).2.1.2)
      (sourceCalculationInventory observation nontrivial depth half))

def primitiveMobiusSourceSegment (index : Fin 3) : SourceInventoryTraceSegment
    (primitiveMobiusSourceExposure observation nontrivial depth half index)
    (sourcePaidInventory observation nontrivial depth half) :=
  (primitiveMobiusSourceCalculationSegment observation nontrivial depth half index).trans
    (SourceInventoryTraceSegment.right
      (SourceOperationPaidRelations.exposure (receipt observation nontrivial depth half).2.1.2)
      (sourceCalculationInventory observation nontrivial depth half))

theorem whole_debt_R_primitive_mobius_source_preserved (index : Fin 3) (event)
    (present : event ∈ (primitiveMobiusSourceExposure observation nontrivial depth half index).trace) :
    event ∈ (sourceCalculationInventory observation nontrivial depth half).trace :=
  (primitiveMobiusSourceCalculationSegment observation nontrivial depth half index).present event present

def jointMobiusSourceSegment (field : Fin 2) : SourceInventoryTraceSegment
    (jointMobiusSourceExposure observation nontrivial depth half field)
    (sourcePaidInventory observation nontrivial depth half) :=
  (jointMobiusSourceCalculationSegment observation nontrivial depth half field).trans
    (SourceInventoryTraceSegment.right
      (SourceOperationPaidRelations.exposure (receipt observation nontrivial depth half).2.1.2)
      (sourceCalculationInventory observation nontrivial depth half))

def returnJordanSourceSegment (field : Fin 2) : SourceInventoryTraceSegment
    (returnJordanSourceExposure observation nontrivial depth half field)
    (sourcePaidInventory observation nontrivial depth half) :=
  (returnJordanSourceCalculationSegment observation nontrivial depth half field).trans
    (SourceInventoryTraceSegment.right
      (SourceOperationPaidRelations.exposure (receipt observation nontrivial depth half).2.1.2)
      (sourceCalculationInventory observation nontrivial depth half))

def forcedSourceSegment : SourceInventoryTraceSegment
    (forcedSourceExposure observation nontrivial depth half)
    (sourcePaidInventory observation nontrivial depth half) :=
  (forcedSourceCalculationSegment observation nontrivial depth half).trans
    (SourceInventoryTraceSegment.right
      (SourceOperationPaidRelations.exposure (receipt observation nontrivial depth half).2.1.2)
      (sourceCalculationInventory observation nontrivial depth half))

def returnJetSourceSegment (field : Fin 2) : SourceInventoryTraceSegment
    (returnJetSourceExposure observation nontrivial depth half field)
    (sourcePaidInventory observation nontrivial depth half) :=
  (returnJetSourceCalculationSegment observation nontrivial depth half field).trans
    (SourceInventoryTraceSegment.right
      (SourceOperationPaidRelations.exposure (receipt observation nontrivial depth half).2.1.2)
      (sourceCalculationInventory observation nontrivial depth half))

def paNativePortSourceSegment (field : Fin 2) : SourceInventoryTraceSegment
    (paNativePortSourceExposure observation nontrivial depth half field)
    (sourcePaidInventory observation nontrivial depth half) :=
  (paNativePortSourceCalculationSegment observation nontrivial depth half field).trans
    (SourceInventoryTraceSegment.right
      (SourceOperationPaidRelations.exposure (receipt observation nontrivial depth half).2.1.2)
      (sourceCalculationInventory observation nontrivial depth half))

def paNativeCayleySourceSegment (field : Fin 3) : SourceInventoryTraceSegment
    (paNativeCayleySourceExposure observation nontrivial depth half field)
    (sourcePaidInventory observation nontrivial depth half) :=
  (paNativeCayleySourceCalculationSegment observation nontrivial depth half field).trans
    (SourceInventoryTraceSegment.right
      (SourceOperationPaidRelations.exposure (receipt observation nontrivial depth half).2.1.2)
      (sourceCalculationInventory observation nontrivial depth half))

private def waveStepPrefix :=
  let comb := SourceOperationPaidRelations.exposure (receipt observation nontrivial depth half).2.1.2
  let old := wholeDebtRCalculationInventory observation nontrivial depth half
  comb.root :: (comb.trace ++
    (old.root :: (old.trace ++ [.generator (wholeDebtRWaveSourceCode observation nontrivial depth half)])))

def wholeDebtRWaveStepOffset := (waveStepPrefix observation nontrivial depth half).length

/-- The literal Fin slot is retained even when two paid words have equal syntax. -/
def wholeDebtRWaveStepOccurrence
    (index : Fin (SourceOperationPaidRelations.words
      (wholeDebtRWaveSourceTrace observation nontrivial depth half)).length) :
    SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence
      (sourcePaidInventory observation nontrivial depth half) := by
  let words := SourceOperationPaidRelations.words (wholeDebtRWaveSourceTrace observation nontrivial depth half)
  let front := waveStepPrefix observation nontrivial depth half
  refine ⟨front ++ (words.take index.val).map PresentedRelationEventAt.relation,
    words.get index, (words.drop (index.val + 1)).map PresentedRelationEventAt.relation ++
      ((SourceOperationPaidRelations.exposure
        (wholeDebtRReciprocalSourceTrace observation nontrivial depth half)).trace ++ nativeMobiusTraceBlocks observation nontrivial depth half), ?_⟩
  have exposure :
      (SourceOperationPaidRelations.exposure
        (wholeDebtRWaveSourceTrace observation nontrivial depth half)).trace =
      PresentedRelationEventAt.generator (wholeDebtRWaveSourceCode observation nontrivial depth half) ::
        words.map PresentedRelationEventAt.relation := by
    change _ :: RootedAccountedUnfolding.traceBranches
      (SourceOperationPaidRelations.events (wholeDebtRWaveSourceTrace observation nontrivial depth half)) = _
    rw [SourceOperationPaidRelations.events_trace]
  have paid :
      (sourcePaidInventory observation nontrivial depth half).trace =
        front ++ words.map PresentedRelationEventAt.relation ++
          ((SourceOperationPaidRelations.exposure
            (wholeDebtRReciprocalSourceTrace observation nontrivial depth half)).trace ++ nativeMobiusTraceBlocks observation nontrivial depth half) := by
    have seed_trace {X : Type} (left right : RootedAccountedUnfolding X) :
        (SourceHistoryCommon.seed left right).trace =
          left.root :: (left.trace ++ (right.trace ++ [])) := rfl
    rw [sourcePaidInventory, seed_trace, source_calculation_inventory_trace, exposure]
    simp only [front, waveStepPrefix, List.append_nil, List.nil_append, List.cons_append, List.append_assoc]
  have split : words = words.take index.val ++ words.get index :: words.drop (index.val + 1) := by
    change words = words.take index.val ++ words[index.val] :: words.drop (index.val + 1)
    rw [List.getElem_cons_drop index.isLt, List.take_append_drop]
  have mapped : words.map PresentedRelationEventAt.relation =
      (words.take index.val).map PresentedRelationEventAt.relation ++
        PresentedRelationEventAt.relation (words.get index) ::
          (words.drop (index.val + 1)).map PresentedRelationEventAt.relation := by
    simpa only [List.map_append, List.map_cons] using
      congrArg (List.map PresentedRelationEventAt.relation) split
  exact paid.trans ((congrArg (fun tail => front ++ tail ++
    ((SourceOperationPaidRelations.exposure
      (wholeDebtRReciprocalSourceTrace observation nontrivial depth half)).trace ++ nativeMobiusTraceBlocks observation nontrivial depth half)) mapped).trans
    (by simp only [List.append_assoc, List.cons_append]))

theorem whole_debt_R_wave_step_word
    (index : Fin (SourceOperationPaidRelations.words
      (wholeDebtRWaveSourceTrace observation nontrivial depth half)).length) :
    (wholeDebtRWaveStepOccurrence observation nontrivial depth half index).word =
      (SourceOperationPaidRelations.words
        (wholeDebtRWaveSourceTrace observation nontrivial depth half)).get index := rfl

theorem whole_debt_R_wave_step_before_length
    (index : Fin (SourceOperationPaidRelations.words
      (wholeDebtRWaveSourceTrace observation nontrivial depth half)).length) :
    (wholeDebtRWaveStepOccurrence observation nontrivial depth half index).before.length =
      wholeDebtRWaveStepOffset observation nontrivial depth half + index.val := by
  change (waveStepPrefix observation nontrivial depth half ++
    ((SourceOperationPaidRelations.words
      (wholeDebtRWaveSourceTrace observation nontrivial depth half)).take index.val).map
        PresentedRelationEventAt.relation).length = _
  simp only [List.length_append, List.length_map, List.length_take]
  rw [Nat.min_eq_left (Nat.le_of_lt index.isLt)]
  rfl

theorem whole_debt_R_wave_step_positions :
    StrictMono (fun index : Fin (SourceOperationPaidRelations.words
      (wholeDebtRWaveSourceTrace observation nontrivial depth half)).length =>
      (wholeDebtRWaveStepOccurrence observation nontrivial depth half index).before.length) := by
  intro left right less
  change (wholeDebtRWaveStepOccurrence observation nontrivial depth half left).before.length <
    (wholeDebtRWaveStepOccurrence observation nontrivial depth half right).before.length
  rw [whole_debt_R_wave_step_before_length, whole_debt_R_wave_step_before_length]
  exact Nat.add_lt_add_left less _

def frame : Frame where
  N := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.World
    (sourceRoot observation nontrivial) (sourceVisit observation nontrivial depth) (sourceReader observation nontrivial depth half)
  V := RootGeneratedDebtActivationJointSource.OwnerFree.vocabulary
    (sourceRoot observation nontrivial).toAuthoritativeRoot (sourceVisit observation nontrivial depth).current
    (sourceReader observation nontrivial depth half)
  old := endpoint observation nontrivial depth half
  registered := registered observation nontrivial depth half
  packetAt := S.packet (sourceRoot observation nontrivial) (sourceVisit observation nontrivial depth)
    emptyEffectU7 emptyEffectU7Calculus (sourceReader observation nontrivial depth half)
  environment := fun {_current} _occurrence => nextEnvironment observation nontrivial depth half
  depth := 0
  inventory := some (sourcePaidInventory observation nontrivial depth half)

def firstTarget := RootGeneratedDebtActivationJointSource.Successor.Inquiry.targetAt
  (endpoint observation nontrivial depth half)
  (S.endpointInput (sourceRoot observation nontrivial) (sourceVisit observation nontrivial depth)
    emptyEffectU7 emptyEffectU7Calculus (sourceReader observation nontrivial depth half)).query
  (registered observation nontrivial depth half)
  (S.packet (sourceRoot observation nontrivial) (sourceVisit observation nontrivial depth)
    emptyEffectU7 emptyEffectU7Calculus (sourceReader observation nontrivial depth half))
  ((endpoint observation nontrivial depth half).authorityAt
    (S.endpointInput (sourceRoot observation nontrivial) (sourceVisit observation nontrivial depth)
      emptyEffectU7 emptyEffectU7Calculus (sourceReader observation nontrivial depth half)).query)
  (firstStep observation nontrivial depth half) (first_action observation nontrivial depth half)
  ((endpoint observation nontrivial depth half).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
    (endpoint observation nontrivial depth half).visit)

theorem first_next : (firstTarget observation nontrivial depth half).targetAnswerAndNext.nextCurrent =
    (frame observation nontrivial depth half).currentPresentation.erase.current :=
  (firstTarget observation nontrivial depth half).targetAnswerAndNext_next_eq

theorem updated_environment (occurrence) :
    (Native.input (material observation nontrivial depth half occurrence)).environment =
      nextEnvironment observation nontrivial depth half := by
  change (receipt observation nontrivial depth half).1.environment +
    (nextEnvironment observation nontrivial depth half - (receipt observation nontrivial depth half).1.environment) = _
  exact add_sub_cancel _ _

theorem completed_expression : (receipt observation nontrivial depth half).2.1.1 =
    .const (receipt observation nontrivial depth half).2.2.1 :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression OriginalKCombCalculation.Base
    (sourceVisit observation nontrivial depth).current
    (fun _ => (receipt observation nontrivial depth half).1)

theorem literal_residual (occurrence) :
    (Native.expression (material observation nontrivial depth half occurrence)).eval
      (Native.input (material observation nontrivial depth half occurrence)).environment =
    (receipt observation nontrivial depth half).1.expression.eval (nextEnvironment observation nontrivial depth half) -
      (receipt observation nontrivial depth half).2.2.1 := by
  rw [Native.expression_eval, updated_environment]
  change _ - (receipt observation nontrivial depth half).2.1.1.eval _ = _
  rw [completed_expression]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
