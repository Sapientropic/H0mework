import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativePreparedOccurrence

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativePrepareNextProbe
noncomputable section
open CPS1ResourceExecution CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open NativePaidEvent NativeAmmoniaDynamics NativeCPContinuationProbe

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {continuation : CPNativeContinuation paid}

/-- The two phases denote the same full mother. Source cuts carry no material. -/
inductive Species (occurrence : NativeOccurrence paid continuation)
  | evolved
  | prepared
  | remaining (material : CPS1ReactiveField.LiveMaterial frame)
  | sourceCut (missing : CPS1Deformation.Species frame)

noncomputable instance {occurrence : NativeOccurrence paid continuation} : DecidableEq (Species occurrence) :=
  Classical.decEq _

inductive Event (occurrence : NativeOccurrence paid continuation)
  | prepare

abbrev Execution (occurrence : NativeOccurrence paid continuation) :=
  Inventory.Execution (Species occurrence) (Event occurrence)

def reactants {occurrence : NativeOccurrence paid continuation} : Event occurrence → List (Species occurrence)
  | .prepare => [.evolved]

def products {occurrence : NativeOccurrence paid continuation} : Event occurrence → List (Species occurrence)
  | .prepare => [.prepared]

def initialStock (occurrence : NativeOccurrence paid continuation) : List (Species occurrence) :=
  .evolved :: current.remaining.map Species.remaining

def sourceSpecies (occurrence : NativeOccurrence paid continuation) : StockItem source → Species occurrence
  | .evolved _ => .evolved
  | .remaining material => .remaining material

theorem initial_inventory (occurrence : NativeOccurrence paid continuation) :
    (inventory current).map (sourceSpecies occurrence) = initialStock occurrence := by
  simp only [inventory,List.map_cons,List.map_map,sourceSpecies,Function.comp_def,initialStock]

def preparedStock (occurrence : NativeOccurrence paid continuation) : List (Species occurrence) :=
  .prepared :: current.remaining.map Species.remaining

def Species.live? {occurrence : NativeOccurrence paid continuation} : Species occurrence → Option (CPS1ReactiveField.LiveMaterial frame)
  | .remaining material => some material
  | _ => none

def Species.mother? {occurrence : NativeOccurrence paid continuation} : Species occurrence → Bool
  | .evolved | .prepared => true
  | _ => false

def Species.physical {occurrence : NativeOccurrence paid continuation} : Species occurrence → Option (PostState current)
  | .evolved | .prepared => some occurrence.physical
  | _ => none

def Species.preparedFace {occurrence : NativeOccurrence paid continuation} : Species occurrence → Option (NativePrepared occurrence)
  | .prepared => some (native_prepared occurrence)
  | _ => none

inductive LedgerStage (occurrence : NativeOccurrence paid continuation)
  | retained (execution : CPS1Deformation.Execution frame)
  | native (execution : Execution occurrence)

structure Cursor (occurrence : NativeOccurrence paid continuation) where
  stock : List (Species occurrence)
  pending : List CPS1Deformation.Source.RawAction
  stages : List (LedgerStage occurrence)
  cut : Option (Species occurrence)

def prepareRequest : CPS1Deformation.Source.RawAction := .old (.old (.old (.old .prepare)))

def startCursor (occurrence : NativeOccurrence paid continuation) (coarse : CPS1Deformation.Source.Cursor frame) :
    Cursor occurrence :=
  ⟨initialStock occurrence,coarse.pending,coarse.stages.map LedgerStage.retained,coarse.cut.map Species.sourceCut⟩

/-- A source tick executes the requested head and preserves the later adopt requests. -/
def program {occurrence : NativeOccurrence paid continuation} (current : Cursor occurrence) : List (Event occurrence) := by
  classical
  exact if current.pending.head? = some prepareRequest then [.prepare] else []

def runPrepare {occurrence : NativeOccurrence paid continuation} (current : Cursor occurrence) : Execution occurrence :=
  Inventory.execute reactants products (program current) current.stock

def advancePrepare {occurrence : NativeOccurrence paid continuation} (current : Cursor occurrence) : Cursor occurrence :=
  let execution := runPrepare current
  ⟨execution.stock,current.pending.drop execution.fired.length,
    current.stages ++ [.native execution],execution.missing⟩

theorem fire_prepare (occurrence : NativeOccurrence paid continuation) :
    Inventory.fire reactants products (Event.prepare : Event occurrence) (initialStock occurrence) =
      .ok (preparedStock occurrence) := by
  classical
  simp [Inventory.fire,Inventory.consume,reactants,products,initialStock,preparedStock]

theorem prepare_no_repeat (occurrence : NativeOccurrence paid continuation) :
    Inventory.fire reactants products (Event.prepare : Event occurrence) (preparedStock occurrence) =
      .error Species.evolved := by
  classical
  simp [Inventory.fire,Inventory.consume,reactants,preparedStock]

theorem execution_requested (occurrence : NativeOccurrence paid continuation) (coarse : CPS1Deformation.Source.Cursor frame)
    (requested : coarse.pending.head? = some prepareRequest) :
    runPrepare (startCursor occurrence coarse) = ⟨[.prepare],[],preparedStock occurrence,none⟩ := by
  classical
  have selected : program (startCursor occurrence coarse) = [.prepare] := by
    simp only [program,startCursor,requested,if_pos]
  rw [runPrepare,selected,Inventory.execute_cons]
  simp only [startCursor]
  rw [fire_prepare]

theorem advance_requested (occurrence : NativeOccurrence paid continuation) (coarse : CPS1Deformation.Source.Cursor frame)
    (requested : coarse.pending.head? = some prepareRequest) :
    advancePrepare (startCursor occurrence coarse) =
      ⟨preparedStock occurrence,coarse.pending.drop 1,
        coarse.stages.map LedgerStage.retained ++ [.native ⟨[.prepare],[],preparedStock occurrence,none⟩],none⟩ := by
  rw [advancePrepare,execution_requested occurrence coarse requested]
  rfl

theorem prepared_remaining (occurrence : NativeOccurrence paid continuation) :
    (preparedStock occurrence).filterMap Species.live? = current.remaining := by
  have residual (materials : List (CPS1ReactiveField.LiveMaterial frame)) :
      (materials.map (Species.remaining : _ → Species occurrence)).filterMap Species.live? = materials := by
    induction materials with
    | nil => rfl
    | cons material rest ih =>
      simpa only [List.map_cons,List.filterMap_cons,Species.live?] using congrArg (material :: ·) ih
  simp only [preparedStock,List.filterMap_cons,Species.live?,residual]

theorem prepared_single_mother (occurrence : NativeOccurrence paid continuation) :
    ((preparedStock occurrence).filter Species.mother?).length = 1 := by
  have residual (materials : List (CPS1ReactiveField.LiveMaterial frame)) :
      (materials.map (Species.remaining : _ → Species occurrence)).filter Species.mother? = [] := by
    induction materials with
    | nil => rfl
    | cons material rest ih =>
      simpa only [List.map_cons,List.filter_cons,Species.mother?,Bool.false_eq_true,if_false] using ih
  simp only [preparedStock,List.filter_cons,Species.mother?,ite_true,residual,List.length_cons,List.length_nil]

theorem prepared_physical (occurrence : NativeOccurrence paid continuation) :
    (preparedStock occurrence).filterMap Species.physical = [continuation.after] := by
  simp [preparedStock,Species.physical,List.filterMap_map,Function.comp_def,NativeOccurrence.physical]

theorem prepare_balance (occurrence : NativeOccurrence paid continuation) (species : Species occurrence) :
    (initialStock occurrence).count species + ([Species.prepared] : List (Species occurrence)).count species =
      (preparedStock occurrence).count species + ([Species.evolved] : List (Species occurrence)).count species :=
  Inventory.fire_balance reactants products Event.prepare _ _ (fire_prepare occurrence) species

end
end CPS1MaterialIncidence.NativePrepareNextProbe
