import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeAdoptionExecution

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeAdoptionProbe
noncomputable section
open CPS1ResourceExecution CPS1AtomicDynamics CPS1ElectronicSource CPS1SameEventFunction CPS1PhosphorylExchange
open NativePaidEvent NativeAmmoniaDynamics NativeCPContinuationProbe NativePrepareNextProbe NativePrepareBinding
open NativeResumableProbe

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {native : Common before step raw} {current : NativeCurrent native}
  {paid : SourceGeneratedPaidReturn native current} {continuation : CPNativeContinuation paid}
variable (returned : NativePrepareNext paid continuation) (germ : NativeOriginGerm returned.occurrence)

inductive LedgerStage (returned : NativePrepareNext paid continuation) (germ : NativeOriginGerm returned.occurrence)
  | prior (stage : NativePrepareNextProbe.LedgerStage returned.occurrence)
  | native (execution : Execution returned germ)

/-- The active state is variable. The remaining stock is proved to contain no
second physical mother, and the full account stays anchored to the same source. -/
structure NativeSourceCurrent (returned : NativePrepareNext paid continuation) (germ : NativeOriginGerm returned.occurrence) where
  active : NativeActive current
  stock : List (Species returned germ)
  tail : List (Species returned germ)
  stockActual : stock = .active active :: tail
  tailPhysical : tail.filterMap (Species.physical? returned germ) = []
  tailRemaining : tail.filterMap (Species.live? returned germ) = current.remaining
  account : active.state.energy + active.state.reserve =
    returned.occurrence.physical.energy + returned.occurrence.physical.reserve
  pending : List CPS1Deformation.Source.RawAction
  stages : List (LedgerStage returned germ)
  cut : Option (Species returned germ)

def NativeSourceCurrent.state (source : NativeSourceCurrent returned germ) : PostState current := source.active.state

def NativeSourceCurrent.charged (_source : NativeSourceCurrent returned germ) : ChargedState native current :=
  returned.occurrence.charged

def NativeSourceCurrent.sourceRestriction (_source : NativeSourceCurrent returned germ) : CPS1ReactiveNuclear.SourceCursor frame :=
  germ.sourceRestriction

def adopted_current : NativeSourceCurrent returned germ := by
  refine ⟨prepared_active returned germ,(runAdoptions returned germ).stock,
    .spentActive :: .spentMolecular :: residualStock returned germ,?_,?_,?_,rfl,
    returned.next.pending.drop (runAdoptions returned germ).fired.length,
    returned.next.stages.map LedgerStage.prior ++ [.native (runAdoptions returned germ)],
    (runAdoptions returned germ).missing⟩
  · rw [adoption_execution_exact]
    rfl
  · simp only [List.filterMap_cons,Species.physical?,residual_physical]
  · simp only [List.filterMap_cons,Species.live?,residual_live]

theorem adopted_stock : (adopted_current returned germ).stock = (runAdoptions returned germ).stock := rfl

theorem adopted_state : (adopted_current returned germ).state = returned.occurrence.physical := rfl

theorem adopted_pending : (adopted_current returned germ).pending = [] := by
  change returned.next.pending.drop (runAdoptions returned germ).fired.length = []
  rw [returned.next_exact,adoption_execution_exact]
  rfl

theorem adopted_cut : (adopted_current returned germ).cut = none := by
  change (runAdoptions returned germ).missing = none
  rw [adoption_execution_exact]

theorem adopted_stages : (adopted_current returned germ).stages =
    returned.next.stages.map LedgerStage.prior ++ [.native (runAdoptions returned germ)] := rfl

variable {returned germ}

def runPulse (source : NativeSourceCurrent returned germ) : Execution returned germ :=
  Inventory.execute (reactants returned germ) (products returned germ) [.pulse source.active] source.stock

theorem fire_pulse (source : NativeSourceCurrent returned germ) :
    Inventory.fire (reactants returned germ) (products returned germ) (Event.pulse source.active) source.stock =
      .ok (.active (pulse_active source.active) :: .spentPulse source.state :: source.tail) := by
  classical
  rw [source.stockActual]
  simp [Inventory.fire,Inventory.consume,reactants,products,NativeSourceCurrent.state]

theorem pulse_execution_exact (source : NativeSourceCurrent returned germ) : runPulse source =
    ⟨[.pulse source.active],[],.active (pulse_active source.active) :: .spentPulse source.state :: source.tail,none⟩ := by
  rw [runPulse,Inventory.execute_cons,fire_pulse]

def advanceSource (source : NativeSourceCurrent returned germ) : NativeSourceCurrent returned germ := by
  refine ⟨pulse_active source.active,(runPulse source).stock,.spentPulse source.state :: source.tail,
    ?_,?_,?_,?_,source.pending,source.stages ++ [.native (runPulse source)],(runPulse source).missing⟩
  · rw [pulse_execution_exact]
  · simpa only [List.filterMap_cons,Species.physical?] using source.tailPhysical
  · simpa only [List.filterMap_cons,Species.live?] using source.tailRemaining
  · exact (native_result_account (advanceNative source.state)).trans source.account

theorem advance_state (source : NativeSourceCurrent returned germ) :
    (advanceSource source).state = (advanceNative source.state).next := rfl

theorem source_physical (source : NativeSourceCurrent returned germ) :
    source.stock.filterMap (Species.physical? returned germ) = [source.state] := by
  rw [source.stockActual]
  simp only [List.filterMap_cons,Species.physical?,source.tailPhysical,NativeSourceCurrent.state]

theorem source_remaining (source : NativeSourceCurrent returned germ) :
    source.stock.filterMap (Species.live? returned germ) = current.remaining := by
  rw [source.stockActual]
  simp only [List.filterMap_cons,Species.live?,source.tailRemaining]

theorem source_full_inventory (source : NativeSourceCurrent returned germ) :
    source.charged = paid.parent.products.serial.after ∧
    source.charged.spent = paid.parent.products.serial.after.spent ∧
    source.stock.filterMap (Species.live? returned germ) = current.remaining :=
  ⟨rfl,rfl,source_remaining source⟩

theorem source_electrons (source : NativeSourceCurrent returned germ) :
    Matrix.trace (source.state.occupied * source.state.occupied.conjTranspose) = (electronCount native.nodes : ℂ) :=
  post_electron_number source.state

theorem source_field (source : NativeSourceCurrent returned germ) :
    CPS1ElectronicEvolution.fields (rawField current) source.state.rawC =
      CPS1ElectronicEvolution.fields (basis current) source.state.occupied := post_fields source.state

theorem advance_pending (source : NativeSourceCurrent returned germ) :
    (advanceSource source).pending = source.pending := rfl

theorem advance_stages (source : NativeSourceCurrent returned germ) :
    (advanceSource source).stages = source.stages ++ [.native (runPulse source)] := rfl

theorem advance_cut (source : NativeSourceCurrent returned germ) : (advanceSource source).cut = none := by
  change (runPulse source).missing = none
  rw [pulse_execution_exact]

structure NativeAdoptedNext (returned : NativePrepareNext paid continuation) (germ : NativeOriginGerm returned.occurrence) where
  adopted : NativeSourceCurrent returned germ
  adoptedActual : adopted = adopted_current returned germ
  result : NativePhysicalResult adopted.state
  resultActual : result = advanceNative adopted.state
  execution : Execution returned germ
  executionActual : execution = runPulse adopted
  next : NativeSourceCurrent returned germ
  nextActual : next = advanceSource adopted

namespace NativeAdoptedNext
variable (result : NativeAdoptedNext returned germ)

theorem physical_actual : result.next.state = result.result.next := by
  rw [result.nextActual,advance_state,result.resultActual]

theorem adopted_physical : result.adopted.state = returned.occurrence.physical := by
  rw [result.adoptedActual,adopted_state]

theorem adoption_paid : result.adopted.stock = (runAdoptions returned germ).stock ∧
    result.adopted.pending = [] ∧ result.adopted.cut = none := by
  rw [result.adoptedActual]
  exact ⟨adopted_stock returned germ,adopted_pending returned germ,adopted_cut returned germ⟩

theorem actual_execution : result.execution =
    ⟨[.pulse result.adopted.active],[],
      .active (pulse_active result.adopted.active) :: .spentPulse result.adopted.state :: result.adopted.tail,none⟩ := by
  rw [result.executionActual,pulse_execution_exact]

theorem next_stock : result.next.stock = result.execution.stock := by
  rw [result.nextActual,result.executionActual]
  rfl

theorem next_pending : result.next.pending = [] := by
  rw [result.nextActual,advance_pending]
  exact result.adoption_paid.2.1

theorem next_stages : result.next.stages = result.adopted.stages ++ [.native result.execution] := by
  rw [result.nextActual,advance_stages,result.executionActual]

theorem next_cut : result.next.cut = none := by
  rw [result.nextActual,advance_cut]

theorem next_whole : result.next.charged = paid.parent.products.serial.after ∧
    result.next.charged.spent = paid.parent.products.serial.after.spent ∧
    result.next.stock.filterMap (Species.live? returned germ) = current.remaining := source_full_inventory result.next

/-- This consumes the actual next state, rather than returning to the frozen
paid.physical or the initial prepared state. -/
theorem resume_actual : (advanceSource result.next).state = (advanceNative result.next.state).next :=
  advance_state result.next

end NativeAdoptedNext

theorem source_generated_native_adopted_next (returned : NativePrepareNext paid continuation)
    (germ : NativeOriginGerm returned.occurrence) : Nonempty (NativeAdoptedNext returned germ) := by
  let adopted := adopted_current returned germ
  exact ⟨⟨adopted,rfl,advanceNative adopted.state,rfl,runPulse adopted,rfl,advanceSource adopted,rfl⟩⟩

end
end CPS1MaterialIncidence.NativeAdoptionProbe
