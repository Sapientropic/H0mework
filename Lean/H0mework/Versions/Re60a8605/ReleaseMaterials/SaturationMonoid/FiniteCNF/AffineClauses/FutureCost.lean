import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Future
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.ForgetCost

/-!
The measured execution shares each actual future support, generates the projection,
and groups its overlapping cells before covering. Peak cells are returned by the
same execution. The total source-record bound is polynomial in that measured peak;
the lowered volume calls form a subaccount of sourceCells, not an additional cost.
Counter evaluation and whole-machine bit scheduling remain separate.
-/

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineClauses.FutureCost
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineCarrier (Cells Valid storage)
open AffineCarrier.Cost (cellBound)

structure Execution extends JointCost.Execution where
  peakCells : Nat
  deriving Repr

def step (n : Nat) (clause : Clause) (remaining : Formula) (cells : Cells) : Execution :=
  let future := AffineClauseProduct.Cost.support remaining
  let acted := clauseAction clause cells
  let projected := AffineForget.Cost.cells n future.value acted.value
  let covered := AffineGroupCover.compact n projected.value
  ⟨⟨covered.value,future.visits+acted.visits+projected.visits+covered.cells+
    2*(formulaSize remaining+future.value.length+storage cells+storage acted.value+
      storage projected.value+storage covered.value)+13,
    covered.machineSteps,covered.maxInput⟩,max cells.length acted.value.length⟩

theorem step_value (n : Nat) (clause : Clause) (remaining : Formula) (cells : Cells) :
    (step n clause remaining cells).value=Future.step n clause remaining cells := by
  simp only [step,AffineClauseProduct.Cost.support_value,AffineForget.Cost.cells_value,Future.step]

theorem step_valid (n : Nat) (clause : Clause) (remaining : Formula) (cells : Cells) :
    Valid n (step n clause remaining cells).value := by
  rw [step_value]
  exact Future.step_valid n clause remaining cells

theorem step_output (n : Nat) (clause : Clause) (remaining : Formula) (cells : Cells) :
    (step n clause remaining cells).value.length ≤ (step n clause remaining cells).peakCells := by
  have projected := AffineForget.Cost.cells_length n (AffineClauseProduct.Cost.support remaining).value (clauseAction clause cells).value
  have covered := AffineGroupCover.compact_count n _ (AffineForget.Cost.cells_valid n
    (AffineClauseProduct.Cost.support remaining).value (clauseAction clause cells).value)
  exact (covered.trans projected).trans (Nat.le_max_right _ _)

theorem actionBudget_mono (n a b c d e f : Nat) (ab : a ≤ b) (cd : c ≤ d) (ef : e ≤ f) :
    Cost.actionBudget n a c e ≤ Cost.actionBudget n b d f := by
  unfold Cost.actionBudget Cost.cutBudget Cost.branchesBudget
  gcongr

theorem projectionBudget_mono (n small large count ceiling : Nat) (first : small ≤ large) (second : count ≤ ceiling) :
    AffineForget.Cost.cellsBudget n small count ≤ AffineForget.Cost.cellsBudget n large ceiling := by
  unfold AffineForget.Cost.cellsBudget AffineForget.Cost.generateBudget AffineForget.Cost.sourceBudget
    AffineForget.Cost.selectBudget AffineForget.Cost.eraseBudget AffineForget.Cost.eraseRowBudget
    AffineForget.Cost.modelBudget
  gcongr

theorem groupBudget_mono (n small large : Nat) (bound : small ≤ large) :
    AffineGroupCover.compactBudget n small ≤ AffineGroupCover.compactBudget n large := by
  unfold AffineGroupCover.compactBudget AffineGroupCover.partitionRound AffineGroupCover.insertBudget
    AffineGroupCover.insertRound AffineGroupCover.compressionRound AffineJointCover.Cost.compactBudget
    AffineJointCover.Cost.hullBudget AffineJointCover.Cost.volumeBudget
    AffineCollect.Cost.collectBudget AffineCollect.Cost.scanBudget AffineCollect.Cost.leftBudget
  gcongr

def stepBudget (n size peak : Nat) : Nat :=
  AffineClauseProduct.Cost.supportBudget size+Cost.actionBudget n peak size size+
    AffineForget.Cost.cellsBudget n size peak+AffineGroupCover.compactBudget n peak+
      4*size+8*peak*cellBound n+13

theorem step_cells (n size : Nat) (clause : Clause) (remaining : Formula)
    (inside : RowsWithin n clause) (cells : Cells) (valid : Valid n cells)
    (formulaBound : formulaSize (clause::remaining) ≤ size) :
    (step n clause remaining cells).sourceCells ≤ stepBudget n size (step n clause remaining cells).peakCells := by
  have sizes : clause.length ≤ size ∧ Gates.rowTerms clause ≤ size ∧ formulaSize remaining ≤ size := by
    rw [Cost.formulaSize_cons,AffineCollect.Cost.rows_size] at formulaBound
    omega
  let future := AffineClauseProduct.Cost.support remaining
  let acted := clauseAction clause cells
  let projected := AffineForget.Cost.cells n future.value acted.value
  let covered := AffineGroupCover.compact n projected.value
  let peak := max cells.length acted.value.length
  have inputCount : cells.length ≤ peak := Nat.le_max_left _ _
  have actedCount : acted.value.length ≤ peak := Nat.le_max_right _ _
  have actedValid := clauseAction_valid n clause inside cells valid
  have projectedValid := AffineForget.Cost.cells_valid n future.value acted.value
  have coveredValid := AffineGroupCover.compact_valid n projected.value projectedValid
  have projectedCount := (AffineForget.Cost.cells_length n future.value acted.value).trans actedCount
  have coveredCount := (AffineGroupCover.compact_count n projected.value projectedValid).trans projectedCount
  have supported := AffineClauseProduct.Cost.support_length remaining
  have supportBound : future.value.length ≤ size := supported.trans
    ((AffineClauseProduct.Cost.terms_le_size remaining).trans sizes.2.2)
  have supportVisits := AffineClauseProduct.Cost.support_visits remaining
  have supportCost : future.visits ≤ AffineClauseProduct.Cost.supportBudget size := by
    apply supportVisits.trans
    unfold AffineClauseProduct.Cost.supportBudget
    gcongr <;> exact sizes.2.2
  have actedCost := (Cost.action_visits n clause inside cells valid).trans
    (actionBudget_mono n _ _ _ _ _ _ inputCount sizes.1 sizes.2.1)
  have projectedCost := (AffineForget.Cost.cells_visits n future.value acted.value actedValid).trans
    (projectionBudget_mono n _ size _ peak supportBound actedCount)
  have coveredCost := (AffineGroupCover.compact_cells n projected.value projectedValid).trans
    (groupBudget_mono n _ peak projectedCount)
  have inputStorage := (AffineCarrier.Cost.storage_bound n cells valid).trans (Nat.mul_le_mul_right (cellBound n) inputCount)
  have actedStorage := (AffineCarrier.Cost.storage_bound n acted.value actedValid).trans (Nat.mul_le_mul_right (cellBound n) actedCount)
  have projectedStorage := (AffineCarrier.Cost.storage_bound n projected.value projectedValid).trans (Nat.mul_le_mul_right (cellBound n) projectedCount)
  have coveredStorage := (AffineCarrier.Cost.storage_bound n covered.value coveredValid).trans (Nat.mul_le_mul_right (cellBound n) coveredCount)
  change future.visits+acted.visits+projected.visits+covered.cells+
    2*(formulaSize remaining+future.value.length+storage cells+storage acted.value+storage projected.value+storage covered.value)+13 ≤ _
  change _ ≤ stepBudget n size peak
  unfold stepBudget
  dsimp only [acted,projected,covered] at *
  nlinarith

def run (n : Nat) : Formula → Cells → Execution
  | [],cells => ⟨⟨cells,2*storage cells+1,0,0⟩,cells.length⟩
  | clause::rest,cells =>
      let current := step n clause rest cells
      let next := run n rest current.value
      ⟨⟨next.value,current.sourceCells+next.sourceCells+2*storage next.value+7,
        current.volumeSteps+next.volumeSteps,max current.volumeInput next.volumeInput⟩,
        max current.peakCells next.peakCells⟩

theorem run_value (n : Nat) (formula : Formula) (cells : Cells) :
    (run n formula cells).value=Future.run n formula cells := by
  induction formula generalizing cells with
  | nil => rfl
  | cons clause rest ih => simp only [run,Future.run,ih,step_value]

theorem run_valid (n : Nat) (formula : Formula) (cells : Cells) (valid : Valid n cells) :
    Valid n (run n formula cells).value := by
  rw [run_value]
  exact Future.run_valid n formula cells valid

theorem run_input (n : Nat) (formula : Formula) (cells : Cells) : cells.length ≤ (run n formula cells).peakCells := by
  cases formula with
  | nil => rfl
  | cons clause rest =>
      exact (Nat.le_max_left cells.length (clauseAction clause cells).value.length).trans (Nat.le_max_left _ _)

theorem run_output (n : Nat) (formula : Formula) (cells : Cells) :
    (run n formula cells).value.length ≤ (run n formula cells).peakCells := by
  induction formula generalizing cells with
  | nil => rfl
  | cons clause rest ih => exact (ih (step n clause rest cells).value).trans (Nat.le_max_right _ _)

theorem stepBudget_mono (n a b p q : Nat) (size : a ≤ b) (peak : p ≤ q) :
    stepBudget n a p ≤ stepBudget n b q := by
  have acted := actionBudget_mono n p q a b a b peak size size
  have projected := projectionBudget_mono n a b p q size peak
  have covered := groupBudget_mono n p q peak
  unfold stepBudget AffineClauseProduct.Cost.supportBudget
  gcongr

def runBudget (n size count peak : Nat) : Nat :=
  count*(stepBudget n size peak+2*peak*cellBound n+7)+2*peak*cellBound n+1

theorem runBudget_mono (n a b c d p q : Nat) (size : a ≤ b) (count : c ≤ d) (peak : p ≤ q) :
    runBudget n a c p ≤ runBudget n b d q := by
  have step := stepBudget_mono n a b p q size peak
  unfold runBudget
  gcongr

theorem run_cells_bound (n size peak : Nat) (formula : Formula) (inside : Within n formula)
    (cells : Cells) (valid : Valid n cells) (records : formulaSize formula ≤ size)
    (measured : (run n formula cells).peakCells ≤ peak) :
    (run n formula cells).sourceCells ≤ runBudget n size formula.length peak := by
  induction formula generalizing cells with
  | nil =>
      have stored := (AffineCarrier.Cost.storage_bound n cells valid).trans
        (Nat.mul_le_mul_right (cellBound n) measured)
      simp only [run,runBudget,List.length_nil,Nat.zero_mul,Nat.zero_add]
      nlinarith
  | cons clause rest ih =>
      have headPeak : (step n clause rest cells).peakCells ≤ peak := (Nat.le_max_left _ _).trans measured
      have tailPeak : (run n rest (step n clause rest cells).value).peakCells ≤ peak := (Nat.le_max_right _ _).trans measured
      have first := (step_cells n size clause rest (inside clause (by simp)) cells valid records).trans
        (stepBudget_mono n size size _ peak (Nat.le_refl _) headPeak)
      have restRecords : formulaSize rest ≤ size := by rw [Cost.formulaSize_cons] at records; omega
      have restInside : Within n rest := fun c member => inside c (by simp [member])
      have second := ih restInside (step n clause rest cells).value (step_valid n clause rest cells) restRecords tailPeak
      have output := (AffineCarrier.Cost.storage_bound n _ (run_valid n rest _ (step_valid n clause rest cells))).trans
        (Nat.mul_le_mul_right (cellBound n) ((run_output n rest _).trans tailPeak))
      simp only [run,runBudget,List.length_cons] at *
      nlinarith

theorem run_cells (n : Nat) (formula : Formula) (inside : Within n formula) (cells : Cells) (valid : Valid n cells) :
    (run n formula cells).sourceCells ≤ runBudget n (formulaSize formula) formula.length (run n formula cells).peakCells :=
  run_cells_bound n _ _ formula inside cells valid (Nat.le_refl _) (Nat.le_refl _)

def microRound (n peak : Nat) : Nat := peak*AffineJointCover.Cost.microBudget n peak

theorem microRound_mono (n small large : Nat) (bound : small ≤ large) : microRound n small ≤ microRound n large := by
  unfold microRound AffineJointCover.Cost.microBudget
  gcongr

theorem step_micro (n : Nat) (clause : Clause) (remaining : Formula) (cells : Cells) :
    (step n clause remaining cells).volumeSteps ≤ microRound n (step n clause remaining cells).peakCells := by
  have projected := AffineForget.Cost.cells_length n (AffineClauseProduct.Cost.support remaining).value (clauseAction clause cells).value
  have bounded := projected.trans (Nat.le_max_right cells.length (clauseAction clause cells).value.length)
  exact (AffineGroupCover.compact_machineSteps n _).trans (microRound_mono n _ _ bounded)

theorem step_maxInput (n : Nat) (clause : Clause) (remaining : Formula) (cells : Cells) :
    (step n clause remaining cells).volumeInput ≤ 2*n+2*(step n clause remaining cells).peakCells+5 := by
  have projected := AffineForget.Cost.cells_length n (AffineClauseProduct.Cost.support remaining).value (clauseAction clause cells).value
  have bounded := projected.trans (Nat.le_max_right cells.length (clauseAction clause cells).value.length)
  exact (AffineGroupCover.compact_maxInput n _).trans (by gcongr; exact bounded)

theorem run_micro_bound (n peak : Nat) (formula : Formula) (cells : Cells)
    (measured : (run n formula cells).peakCells ≤ peak) :
    (run n formula cells).volumeSteps ≤ formula.length*microRound n peak ∧
      (run n formula cells).volumeInput ≤ 2*n+2*peak+5 := by
  induction formula generalizing cells with
  | nil => simp [run]
  | cons clause rest ih =>
      have headPeak : (step n clause rest cells).peakCells ≤ peak := (Nat.le_max_left _ _).trans measured
      have tailPeak : (run n rest (step n clause rest cells).value).peakCells ≤ peak := (Nat.le_max_right _ _).trans measured
      have first := (step_micro n clause rest cells).trans (microRound_mono n _ peak headPeak)
      have second := step_maxInput n clause rest cells
      have tail := ih (step n clause rest cells).value tailPeak
      simp only [run,List.length_cons]
      constructor
      · nlinarith
      · exact max_le (second.trans (by gcongr)) tail.2

theorem run_micro (n : Nat) (formula : Formula) (cells : Cells) :
    (run n formula cells).volumeSteps ≤ formula.length*microRound n (run n formula cells).peakCells ∧
      (run n formula cells).volumeInput ≤ 2*n+2*(run n formula cells).peakCells+5 :=
  run_micro_bound n _ formula cells (Nat.le_refl _)

def bodyRun : Formula → Clean
  | [] => ⟨[],1⟩
  | clause::rest =>
      let tail := bodyRun rest
      let kept := match clause with | _::_::_ => true | _ => false
      let output := if kept then clause::tail.value else tail.value
      ⟨output,tail.visits+2*CapacityMatching.RowCost.rowsCells clause+2*formulaSize output+5⟩

theorem bodyRun_value (formula : Formula) : (bodyRun formula).value=Future.body formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      cases clause with
      | nil => simp [bodyRun,Future.body,ih]
      | cons row more => cases more <;> simp [bodyRun,Future.body,ih]

theorem bodyRun_size (formula : Formula) : formulaSize (bodyRun formula).value ≤ formulaSize formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      cases clause with
      | nil => simp [bodyRun,Cost.formulaSize_cons] at *; omega
      | cons row more => cases more <;> simp [bodyRun,Cost.formulaSize_cons] at * <;> omega

theorem bodyRun_length (formula : Formula) : (bodyRun formula).value.length ≤ formula.length := by
  rw [bodyRun_value]
  exact List.length_filter_le _ _

theorem bodyRun_cells_bound (formula : Formula) (size : Nat) (records : formulaSize formula ≤ size) :
    (bodyRun formula).visits ≤ formula.length*(4*size+5)+1 := by
  induction formula with
  | nil => simp [bodyRun]
  | cons clause rest ih =>
      have restSize : formulaSize rest ≤ size := by rw [Cost.formulaSize_cons] at records; omega
      have first : CapacityMatching.RowCost.rowsCells clause ≤ size := by rw [Cost.formulaSize_cons] at records; omega
      have output := (bodyRun_size (clause::rest)).trans records
      have tail := ih restSize
      change (bodyRun rest).visits+2*CapacityMatching.RowCost.rowsCells clause+2*formulaSize (bodyRun (clause::rest)).value+5 ≤ _
      simp only [List.length_cons]
      nlinarith

theorem source_measures (formula : Formula) : formula.length ≤ formulaSize formula ∧
    Cost.rowCount formula ≤ formulaSize formula ∧ Cost.termCount formula ≤ formulaSize formula := by
  rw [Cost.formula_size]
  omega

def generate (n : Nat) (formula : Formula) : Execution :=
  let prepared := cleanRun formula
  let initial := Seed.generate prepared.value
  let live := bodyRun prepared.value
  let packed := AffineCarrier.pack initial.value
  let final := run n live.value packed.value
  ⟨⟨final.value,prepared.visits+initial.cells+live.visits+packed.visits+final.sourceCells+
    2*(formulaSize formula+formulaSize prepared.value+formulaSize live.value+AffineCarrier.resultSize initial.value+
      storage packed.value+storage final.value)+11,final.volumeSteps,final.volumeInput⟩,final.peakCells⟩

theorem generate_value (n : Nat) (formula : Formula) : (generate n formula).value=Future.generate n formula := by
  simp only [generate,Future.generate,run_value,bodyRun_value]

theorem generate_valid (n : Nat) (formula : Formula) (inside : Within n formula) : Valid n (generate n formula).value := by
  rw [generate_value]
  exact Future.generate_valid n formula inside

theorem generate_output (n : Nat) (formula : Formula) : (generate n formula).value.length ≤ (generate n formula).peakCells :=
  run_output n _ _

def generateBudget (n size peak : Nat) : Nat :=
  Cost.cleanBudget n size size size+Seed.generateBudget n size size+size*(4*size+5)+1+2*cellBound n+5+
    runBudget n size size peak+6*size+4*cellBound n+2*peak*cellBound n+13

theorem generateBudget_mono (n small large p q : Nat) (size : small ≤ large) (peak : p ≤ q) :
    generateBudget n small p ≤ generateBudget n large q := by
  have running := runBudget_mono n small large small large p q size size peak
  unfold generateBudget Cost.cleanBudget Seed.generateBudget Seed.extractBudget
  gcongr

theorem generate_cells_bound (n size peak : Nat) (formula : Formula) (inside : Within n formula)
    (records : formulaSize formula ≤ size) (measured : (generate n formula).peakCells ≤ peak) :
    (generate n formula).sourceCells ≤ generateBudget n size peak := by
  let prepared := clean formula
  let live := (bodyRun prepared).value
  have input := source_measures formula
  have cleaned := clean_within n formula inside
  have preSize : formulaSize prepared ≤ size := (Cost.clean_size formula).trans records
  have preMeasures := source_measures prepared
  have initial := Seed.generate_valid n prepared cleaned
  have liveSize := (bodyRun_size prepared).trans preSize
  have liveLength := (bodyRun_length prepared).trans (preMeasures.1.trans preSize)
  have liveInside : Within n live := by
    dsimp only [live]
    rw [bodyRun_value]
    exact Future.body_within n prepared cleaned
  have packed := AffineCarrier.pack_valid n _ initial.1 initial.2
  have first := Cost.cleanRun_visits n formula inside
  have firstBound : (cleanRun formula).visits ≤ Cost.cleanBudget n size size size := by
    apply first.trans
    unfold Cost.cleanBudget
    gcongr <;> omega
  have seed := Seed.generate_cells n prepared cleaned
  have seedBound : (Seed.generate prepared).cells ≤ Seed.generateBudget n size size := by
    apply seed.trans
    unfold Seed.generateBudget Seed.extractBudget
    gcongr <;> omega
  have body := bodyRun_cells_bound prepared size preSize
  have bodyBound : (bodyRun prepared).visits ≤ size*(4*size+5)+1 := by apply body.trans; gcongr; omega
  have packCost := AffineCarrier.Cost.pack_visits n _ initial.1 initial.2
  have packedLength := AffineCarrier.Cost.pack_length (Seed.generate prepared).value
  have packedStorage := (AffineCarrier.Cost.storage_bound n _ packed).trans (Nat.mul_le_mul_right (cellBound n) packedLength)
  have initialSize := AffineCarrier.Cost.result_size n _ initial.1 initial.2
  have runPeak : (run n live (AffineCarrier.pack (Seed.generate prepared).value).value).peakCells ≤ peak := by
    simpa only [generate,cleanRun_value] using measured
  have runCost := run_cells_bound n size peak live liveInside _ packed liveSize runPeak
  have runBound := runCost.trans (runBudget_mono n size size live.length size peak peak (Nat.le_refl _) liveLength (Nat.le_refl _))
  have output := (AffineCarrier.Cost.storage_bound n _ (run_valid n live _ packed)).trans
    (Nat.mul_le_mul_right (cellBound n) ((run_output n live _).trans runPeak))
  simp only [Nat.one_mul] at packedStorage
  simp only [generate,cleanRun_value,generateBudget]
  dsimp only [prepared,live] at *
  nlinarith only [firstBound,seedBound,bodyBound,packCost,runBound,records,preSize,liveSize,initialSize,packedStorage,output]

theorem generate_cells (n : Nat) (formula : Formula) (inside : Within n formula) :
    (generate n formula).sourceCells ≤ generateBudget n (formulaSize formula) (generate n formula).peakCells :=
  generate_cells_bound n _ _ formula inside (Nat.le_refl _) (Nat.le_refl _)

theorem generate_micro_bound (n size peak : Nat) (formula : Formula)
    (records : formulaSize formula ≤ size) (measured : (generate n formula).peakCells ≤ peak) :
    (generate n formula).volumeSteps ≤ size*microRound n peak ∧
      (generate n formula).volumeInput ≤ 2*n+2*peak+5 := by
  have count := (bodyRun_length (clean formula)).trans
    (List.length_filter_le (fun clause => !tautology clause) formula)
  have source := source_measures formula
  have bound := run_micro_bound n peak (bodyRun (clean formula)).value
    (AffineCarrier.pack (Seed.generate (clean formula)).value).value (by simpa only [generate,cleanRun_value] using measured)
  simp only [generate,cleanRun_value]
  exact ⟨bound.1.trans (by gcongr; omega),bound.2⟩

structure Answer where
  value : Bool
  sourceCells : Nat
  volumeSteps : Nat
  volumeInput : Nat
  peakCells : Nat
  deriving Repr

def decide (n : Nat) (formula : Formula) : Answer :=
  let generated := generate n formula
  ⟨!generated.value.isEmpty,generated.sourceCells+2*storage generated.value+3,
    generated.volumeSteps,generated.volumeInput,generated.peakCells⟩

theorem decide_value (n : Nat) (formula : Formula) : (decide n formula).value=Future.decide n formula := by
  simp only [decide,Future.decide,generate_value]

theorem decide_correct (n : Nat) (formula : Formula) (inside : Within n formula) :
    (decide n formula).value=true ↔ AffineClauseProduct.Satisfiable formula := by
  rw [decide_value,Future.decide_correct n formula inside]

def decideBudget (n size peak : Nat) : Nat := generateBudget n size peak+2*peak*cellBound n+3

theorem decide_cells_bound (n size peak : Nat) (formula : Formula) (inside : Within n formula)
    (records : formulaSize formula ≤ size) (measured : (decide n formula).peakCells ≤ peak) :
    (decide n formula).sourceCells ≤ decideBudget n size peak := by
  have first := generate_cells_bound n size peak formula inside records measured
  have output := (AffineCarrier.Cost.storage_bound n _ (generate_valid n formula inside)).trans
    (Nat.mul_le_mul_right (cellBound n) ((generate_output n formula).trans measured))
  simp only [decide,decideBudget]
  nlinarith

structure Components extends Answer where
  grouping : Nat
  copies : Nat
  leafCells : Nat
  leafCount : Nat
  deriving Repr

def components (n : Nat) : Nat → Formula → Components
  | _,[] => ⟨⟨true,1,0,0,0⟩,0,1,0,0⟩
  | 0,formula =>
      let leaf := decide n formula
      let copied := 2*formulaSize formula+3
      ⟨⟨leaf.value,leaf.sourceCells+copied,leaf.volumeSteps,leaf.volumeInput,leaf.peakCells⟩,
        0,copied,leaf.sourceCells,1⟩
  | fuel+1,clause::rest =>
      let split := AffineClauseProduct.Cost.grow rest.length [clause] rest
      let leaf := decide n split.value.1
      let tail := components n fuel split.value.2
      let copied := 2*(formulaSize (clause::rest)+formulaSize split.value.1+formulaSize split.value.2)+7
      ⟨⟨leaf.value && tail.value,split.visits+leaf.sourceCells+tail.sourceCells+copied,
        leaf.volumeSteps+tail.volumeSteps,max leaf.volumeInput tail.volumeInput,max leaf.peakCells tail.peakCells⟩,
        split.visits+tail.grouping,tail.copies+copied,leaf.sourceCells+tail.leafCells,tail.leafCount+1⟩

theorem components_value (n fuel : Nat) (formula : Formula) :
    (components n fuel formula).value=Future.components n fuel formula := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp only [components,Future.components,decide_value]
  | succ fuel ih => cases formula <;> simp only [components,Future.components,decide_value,ih]

theorem components_account (n fuel : Nat) (formula : Formula) :
    (components n fuel formula).sourceCells=(components n fuel formula).grouping+
      (components n fuel formula).copies+(components n fuel formula).leafCells := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [components]; omega
  | succ fuel ih =>
      cases formula with
      | nil => rfl
      | cons clause rest =>
          have tail := ih (AffineClauseProduct.Cost.grow rest.length [clause] rest).value.2
          simp only [components]
          omega

theorem components_grouping_value (n fuel : Nat) (formula : Formula) :
    (components n fuel formula).grouping=(AffineClauseProduct.Cost.factors n fuel formula).grouping := by
  induction fuel generalizing formula with
  | zero => cases formula <;> rfl
  | succ fuel ih => cases formula <;> simp only [components,AffineClauseProduct.Cost.factors,ih]

theorem components_grouping (n fuel : Nat) (formula : Formula) :
    (components n fuel formula).grouping ≤ formula.length*
      AffineClauseProduct.Cost.growBudget formula.length (formulaSize formula+1) := by
  rw [components_grouping_value]
  exact AffineClauseProduct.Cost.factors_grouping n fuel formula formula.length (formulaSize formula) (Nat.le_refl _) (Nat.le_refl _)

theorem components_leafCount (n fuel : Nat) (formula : Formula) :
    (components n fuel formula).leafCount ≤ formula.length := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [components]
  | succ fuel ih =>
      cases formula with
      | nil => simp [components]
      | cons clause rest =>
          have tail := ih (AffineClauseProduct.Cost.grow rest.length [clause] rest).value.2
          have remaining : (AffineClauseProduct.Cost.grow rest.length [clause] rest).value.2.length ≤ rest.length := by
            rw [AffineClauseProduct.Cost.grow_value]
            exact AffineClauseProduct.grow_rest_length _ _ _
          simp only [components,List.length_cons]
          omega

theorem components_copies_bound (n fuel size : Nat) (formula : Formula) (records : formulaSize formula ≤ size) :
    (components n fuel formula).copies ≤ (fuel+1)*(6*size+9)+1 := by
  induction fuel generalizing formula with
  | zero => cases formula <;> simp [components]; omega
  | succ fuel ih =>
      cases formula with
      | nil => simp [components]
      | cons clause rest =>
          have split := AffineClauseProduct.Cost.split_sizes clause rest
          have first := split.1.trans records
          have second := split.2.trans records
          have tail := ih (AffineClauseProduct.Cost.grow rest.length [clause] rest).value.2 second
          simp only [components]
          nlinarith

theorem components_leaf_bound (n fuel size peak : Nat) (formula : Formula) (inside : Within n formula)
    (records : formulaSize formula ≤ size) (measured : (components n fuel formula).peakCells ≤ peak) :
    (components n fuel formula).leafCells ≤ formula.length*decideBudget n size peak := by
  induction fuel generalizing formula with
  | zero =>
      cases formula with
      | nil => simp [components]
      | cons clause rest =>
          have paid := decide_cells_bound n size peak (clause::rest) inside records measured
          change (decide n (clause::rest)).sourceCells ≤ (clause::rest).length*decideBudget n size peak
          apply paid.trans
          simp only [List.length_cons]
          nlinarith
  | succ fuel ih =>
      cases formula with
      | nil => simp [components]
      | cons clause rest =>
          let split := (AffineClauseProduct.Cost.grow rest.length [clause] rest).value
          have bounded := AffineClauseProduct.Cost.split_within n clause rest inside
          have sizes := AffineClauseProduct.Cost.split_sizes clause rest
          have leftPeak : (decide n split.1).peakCells ≤ peak := (Nat.le_max_left _ _).trans measured
          have tailPeak : (components n fuel split.2).peakCells ≤ peak := (Nat.le_max_right _ _).trans measured
          have first := decide_cells_bound n size peak split.1 bounded.1 (sizes.1.trans records) leftPeak
          have tail := ih split.2 bounded.2 (sizes.2.trans records) tailPeak
          have remaining : split.2.length ≤ rest.length := by
            dsimp only [split]
            rw [AffineClauseProduct.Cost.grow_value]
            exact AffineClauseProduct.grow_rest_length _ _ _
          simp only [components,List.length_cons]
          dsimp only [split] at *
          nlinarith

theorem components_micro_bound (n fuel size peak : Nat) (formula : Formula)
    (records : formulaSize formula ≤ size) (measured : (components n fuel formula).peakCells ≤ peak) :
    (components n fuel formula).volumeSteps ≤ formula.length*size*microRound n peak ∧
      (components n fuel formula).volumeInput ≤ 2*n+2*peak+5 := by
  induction fuel generalizing formula with
  | zero =>
      cases formula with
      | nil => simp [components]
      | cons clause rest =>
          have leaf := generate_micro_bound n size peak (clause::rest) records measured
          simp only [components,decide,List.length_cons]
          constructor
          · nlinarith
          · exact leaf.2
  | succ fuel ih =>
      cases formula with
      | nil => simp [components]
      | cons clause rest =>
          let split := (AffineClauseProduct.Cost.grow rest.length [clause] rest).value
          have sizes := AffineClauseProduct.Cost.split_sizes clause rest
          have leftPeak : (decide n split.1).peakCells ≤ peak := (Nat.le_max_left _ _).trans measured
          have tailPeak : (components n fuel split.2).peakCells ≤ peak := (Nat.le_max_right _ _).trans measured
          have first := generate_micro_bound n size peak split.1 (sizes.1.trans records) leftPeak
          have tail := ih split.2 (sizes.2.trans records) tailPeak
          have remaining : split.2.length ≤ rest.length := by
            dsimp only [split]
            rw [AffineClauseProduct.Cost.grow_value]
            exact AffineClauseProduct.grow_rest_length _ _ _
          simp only [components,decide,List.length_cons]
          constructor
          · dsimp only [split] at *
            nlinarith
          · exact max_le first.2 tail.2

theorem components_cells (n fuel : Nat) (formula : Formula) (inside : Within n formula) :
    (components n fuel formula).sourceCells ≤
      formula.length*decideBudget n (formulaSize formula) (components n fuel formula).peakCells+
      formula.length*AffineClauseProduct.Cost.growBudget formula.length (formulaSize formula+1)+
      (fuel+1)*(6*formulaSize formula+9)+1 := by
  have leaves := components_leaf_bound n fuel (formulaSize formula) _ formula inside (Nat.le_refl _) (Nat.le_refl _)
  have grouping := components_grouping n fuel formula
  have copied := components_copies_bound n fuel (formulaSize formula) formula (Nat.le_refl _)
  rw [components_account]
  omega

def decideComponents (n : Nat) (formula : Formula) : Components :=
  let output := components n formula.length formula
  let copied := 2*formulaSize formula+3
  { output with sourceCells := output.sourceCells+copied, copies := output.copies+copied }

theorem decideComponents_value (n : Nat) (formula : Formula) :
    (decideComponents n formula).value=Future.decideComponents n formula := by
  simp only [decideComponents,Future.decideComponents,components_value]

theorem decideComponents_correct (n : Nat) (formula : Formula) (inside : Within n formula) :
    (decideComponents n formula).value=true ↔ AffineClauseProduct.Satisfiable formula := by
  rw [decideComponents_value,Future.decideComponents_correct n formula inside]

def totalBudget (n size count peak : Nat) : Nat :=
  count*decideBudget n size peak+count*AffineClauseProduct.Cost.growBudget count (size+1)+
    (count+1)*(6*size+9)+1+2*size+3

theorem decideComponents_cells (n : Nat) (formula : Formula) (inside : Within n formula) :
    (decideComponents n formula).sourceCells ≤
      totalBudget n (formulaSize formula) formula.length (decideComponents n formula).peakCells := by
  have generated := components_cells n formula.length formula inside
  simp only [decideComponents,totalBudget]
  omega

theorem decideComponents_account (n : Nat) (formula : Formula) :
    (decideComponents n formula).sourceCells=(decideComponents n formula).grouping+
      (decideComponents n formula).copies+(decideComponents n formula).leafCells := by
  have generated := components_account n formula.length formula
  simp only [decideComponents]
  omega

theorem decideComponents_micro (n : Nat) (formula : Formula) :
    (decideComponents n formula).volumeSteps ≤
      formula.length*formulaSize formula*microRound n (decideComponents n formula).peakCells ∧
    (decideComponents n formula).volumeInput ≤ 2*n+2*(decideComponents n formula).peakCells+5 :=
  components_micro_bound n formula.length _ _ formula (Nat.le_refl _) (Nat.le_refl _)

end SaturationMonoid.ComplexityProjection.SATSource.AffineClauses.FutureCost
