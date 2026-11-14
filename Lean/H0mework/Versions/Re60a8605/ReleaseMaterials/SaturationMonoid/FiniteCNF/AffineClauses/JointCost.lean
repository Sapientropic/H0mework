import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Joint

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineClauses.JointCost
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineCarrier (Cells Valid Separated storage)
open AffineCarrier.Cost (cellBound)

/-- Source records and the already lowered volume calls are separate accounts. -/
structure Execution where
  value : Cells
  sourceCells : Nat
  volumeSteps : Nat
  volumeInput : Nat
  deriving Repr

/-- Each generated cut, collected union and binary-word cover is executed once. -/
def step (n : Nat) (clause : Clause) (cells : Cells) : Execution :=
  let cut := clauseAction clause cells
  let shared := AffineCollect.collect n cut.value
  let covered := AffineJointCover.Cost.compact n shared.value
  ⟨covered.value,
    cut.visits+shared.visits+covered.cells+
      2*(storage cells+storage cut.value+storage shared.value+storage covered.value)+11,
    covered.machineSteps,covered.maxInput⟩

theorem step_value (n : Nat) (clause : Clause) (cells : Cells) :
    (step n clause cells).value = Joint.step n clause cells := rfl

theorem compact_length (n : Nat) (cells : Cells) :
    (AffineJointCover.Cost.compact n cells).value.length ≤ cells.length := by
  cases cells with
  | nil => simp [AffineJointCover.Cost.compact,AffineJointCover.Cost.hull]
  | cons basis rest =>
      cases current : (AffineJointCover.Cost.hull n (basis::rest)).value with
      | contradiction => simp [AffineJointCover.Cost.compact,current]
      | basis hull =>
          simp only [AffineJointCover.Cost.compact,current]
          split <;> simp

theorem step_length (n : Nat) (clause : Clause) (inside : RowsWithin n clause)
    (cells : Cells) (valid : Valid n cells) :
    (step n clause cells).value.length ≤ cells.length*(clause.length+1) := by
  have first := Cost.action_length clause cells
  have second := AffineCollect.collect_length n _ (clauseAction_valid n clause inside cells valid)
  exact (compact_length n _).trans (second.trans first)

theorem compactBudget_mono (n small large : Nat) (bound : small ≤ large) :
    AffineJointCover.Cost.compactBudget n small ≤ AffineJointCover.Cost.compactBudget n large := by
  unfold AffineJointCover.Cost.compactBudget AffineJointCover.Cost.hullBudget AffineJointCover.Cost.volumeBudget
  gcongr

def stepBudget (n count length terms : Nat) : Nat :=
  let enlarged := count*(length+1)
  Cost.actionBudget n count length terms+AffineCollect.Cost.collectBudget n enlarged+
    AffineJointCover.Cost.compactBudget n enlarged+2*(count+3*enlarged)*cellBound n+11

theorem step_cells (n : Nat) (clause : Clause) (inside : RowsWithin n clause)
    (cells : Cells) (valid : Valid n cells) :
    (step n clause cells).sourceCells ≤ stepBudget n cells.length clause.length (Gates.rowTerms clause) := by
  have cutValid := clauseAction_valid n clause inside cells valid
  have sharedValid := AffineCollect.collect_valid n _ cutValid
  have outputValid := AffineJointCover.Cost.compact_valid n _ sharedValid
  have first := Cost.action_visits n clause inside cells valid
  have second := AffineCollect.Cost.collect_visits n _ cutValid
  have third := AffineJointCover.Cost.compact_cells n _ sharedValid
  have cutLength := Cost.action_length clause cells
  have sharedLength := AffineCollect.collect_length n _ cutValid
  have outputLength := compact_length n (AffineCollect.collect n (clauseAction clause cells).value).value
  have collected := AffineCollect.Cost.collectBudget_mono n _ _ cutLength
  have covered := compactBudget_mono n _ _ (sharedLength.trans cutLength)
  have inputStorage := AffineCarrier.Cost.storage_bound n cells valid
  have cutStorage := (AffineCarrier.Cost.storage_bound n _ cutValid).trans (Nat.mul_le_mul_right (cellBound n) cutLength)
  have sharedStorage := (AffineCarrier.Cost.storage_bound n _ sharedValid).trans
    (Nat.mul_le_mul_right (cellBound n) (sharedLength.trans cutLength))
  have outputStorage := (AffineCarrier.Cost.storage_bound n _ outputValid).trans
    (Nat.mul_le_mul_right (cellBound n) (outputLength.trans (sharedLength.trans cutLength)))
  simp only [step,stepBudget]
  nlinarith

theorem step_micro (n : Nat) (clause : Clause) (inside : RowsWithin n clause)
    (cells : Cells) (valid : Valid n cells) :
    (step n clause cells).volumeSteps ≤ AffineJointCover.Cost.microBudget n (cells.length*(clause.length+1)) := by
  have first := Cost.action_length clause cells
  have second := AffineCollect.collect_length n _ (clauseAction_valid n clause inside cells valid)
  have generated := AffineJointCover.Cost.compact_machineSteps n (AffineCollect.collect n (clauseAction clause cells).value).value
  apply generated.trans
  unfold AffineJointCover.Cost.microBudget
  gcongr <;> exact second.trans first

theorem step_maxInput (n : Nat) (clause : Clause) (inside : RowsWithin n clause)
    (cells : Cells) (valid : Valid n cells) :
    (step n clause cells).volumeInput ≤ 2*n+2*cells.length*(clause.length+1)+5 := by
  have first := Cost.action_length clause cells
  have second := AffineCollect.collect_length n _ (clauseAction_valid n clause inside cells valid)
  have generated := AffineJointCover.Cost.compact_maxInput n (AffineCollect.collect n (clauseAction clause cells).value).value
  change (AffineJointCover.Cost.compact n (AffineCollect.collect n (clauseAction clause cells).value).value).maxInput ≤ _
  nlinarith

def run (n : Nat) : Formula → Cells → Execution
  | [],cells => ⟨cells,2*storage cells+1,0,0⟩
  | clause::rest,cells =>
      let current := step n clause cells
      let next := run n rest current.value
      ⟨next.value,current.sourceCells+next.sourceCells+2*storage next.value+7,
        current.volumeSteps+next.volumeSteps,max current.volumeInput next.volumeInput⟩

theorem run_value (n : Nat) (formula : Formula) (cells : Cells) :
    (run n formula cells).value = Joint.run n formula cells := by
  induction formula generalizing cells with
  | nil => rfl
  | cons clause rest ih => simp only [run,Joint.run,ih,step_value]

theorem run_length (n : Nat) (formula : Formula) (inside : Within n formula)
    (cells : Cells) (valid : Valid n cells) :
    (run n formula cells).value.length ≤ cells.length*Cost.growth formula := by
  induction formula generalizing cells with
  | nil => simp [run,Cost.growth]
  | cons clause rest ih =>
      have stepValid := Joint.step_valid n clause (inside clause (by simp)) cells valid
      have tail := ih (fun c member => inside c (by simp [member])) (step n clause cells).value stepValid
      have head := step_length n clause (inside clause (by simp)) cells valid
      simpa only [run,Cost.growth,List.map_cons,List.prod_cons,Nat.mul_assoc] using
        tail.trans (Nat.mul_le_mul_right (Cost.growth rest) head)

def runBudget (n : Nat) : Formula → Nat → Nat
  | [],count => 2*count*cellBound n+1
  | clause::rest,count =>
      let enlarged := count*(clause.length+1)
      stepBudget n count clause.length (Gates.rowTerms clause)+runBudget n rest enlarged+
        2*enlarged*Cost.growth rest*cellBound n+7

theorem stepBudget_mono (n length terms small large : Nat) (bound : small ≤ large) :
    stepBudget n small length terms ≤ stepBudget n large length terms := by
  have collected := AffineCollect.Cost.collectBudget_mono n _ _ (Nat.mul_le_mul_right (length+1) bound)
  have covered := compactBudget_mono n _ _ (Nat.mul_le_mul_right (length+1) bound)
  dsimp only [stepBudget,Cost.actionBudget]
  gcongr

theorem runBudget_mono (n : Nat) (formula : Formula) (small large : Nat) (bound : small ≤ large) :
    runBudget n formula small ≤ runBudget n formula large := by
  induction formula generalizing small large with
  | nil => simp only [runBudget]; gcongr
  | cons clause rest ih =>
      have current := stepBudget_mono n clause.length (Gates.rowTerms clause) small large bound
      have tail := ih _ _ (Nat.mul_le_mul_right (clause.length+1) bound)
      simp only [runBudget]
      gcongr

def volumeBudget (n : Nat) : Formula → Nat → Nat
  | [],_ => 0
  | clause::rest,count =>
      AffineJointCover.Cost.microBudget n (count*(clause.length+1))+
        volumeBudget n rest (count*(clause.length+1))

theorem volumeBudget_mono (n : Nat) (formula : Formula) (small large : Nat) (bound : small ≤ large) :
    volumeBudget n formula small ≤ volumeBudget n formula large := by
  induction formula generalizing small large with
  | nil => rfl
  | cons clause rest ih =>
      have tail := ih _ _ (Nat.mul_le_mul_right (clause.length+1) bound)
      simp only [volumeBudget,AffineJointCover.Cost.microBudget]
      gcongr

theorem run_volumeSteps (n : Nat) (formula : Formula) (inside : Within n formula)
    (cells : Cells) (valid : Valid n cells) :
    (run n formula cells).volumeSteps ≤ volumeBudget n formula cells.length := by
  induction formula generalizing cells with
  | nil => rfl
  | cons clause rest ih =>
      have insideHead := inside clause (by simp)
      have insideTail : Within n rest := fun c member => inside c (by simp [member])
      have current := step_micro n clause insideHead cells valid
      have stepValid := Joint.step_valid n clause insideHead cells valid
      have generated := step_length n clause insideHead cells valid
      have tail := ih insideTail (step n clause cells).value stepValid
      have budget := volumeBudget_mono n rest _ _ generated
      simp only [run,volumeBudget]
      omega

theorem run_cells (n : Nat) (formula : Formula) (inside : Within n formula)
    (cells : Cells) (valid : Valid n cells) :
    (run n formula cells).sourceCells ≤ runBudget n formula cells.length := by
  induction formula generalizing cells with
  | nil =>
      have size := AffineCarrier.Cost.storage_bound n cells valid
      simp only [run,runBudget]
      nlinarith
  | cons clause rest ih =>
      have insideHead := inside clause (by simp)
      have insideTail : Within n rest := fun c member => inside c (by simp [member])
      have current := step_cells n clause insideHead cells valid
      have stepValid := Joint.step_valid n clause insideHead cells valid
      have generated := step_length n clause insideHead cells valid
      have tail := ih insideTail (step n clause cells).value stepValid
      have tailBudget := runBudget_mono n rest _ _ generated
      have nextValid : Valid n (run n rest (step n clause cells).value).value := by
        rw [run_value]
        exact Joint.run_valid n rest insideTail _ stepValid
      have output := AffineCarrier.Cost.storage_bound n _ nextValid
      have outputLength := run_length n rest insideTail (step n clause cells).value stepValid
      have outputBound := (Nat.mul_le_mul_right (Cost.growth rest) generated)
      have sizeBound := output.trans (Nat.mul_le_mul_right (cellBound n) (outputLength.trans outputBound))
      simp only [run,runBudget]
      nlinarith

theorem growth_clean (formula : Formula) : Cost.growth (clean formula) ≤ Cost.growth formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      cases truth : tautology clause with
      | false =>
          have shape : clean (clause::rest) = clause::clean rest := by simp [clean,truth]
          rw [shape]
          exact Nat.mul_le_mul_left (clause.length+1) ih
      | true =>
          have shape : clean (clause::rest) = clean rest := by simp [clean,truth]
          rw [shape]
          have bound := Nat.mul_le_mul_right (Cost.growth rest) (show 1 ≤ clause.length+1 by omega)
          exact ih.trans (by simpa only [Nat.one_mul,Cost.growth,List.map_cons,List.prod_cons] using bound)

theorem runBudget_clean (n : Nat) (formula : Formula) (count : Nat) :
    runBudget n (clean formula) count ≤ runBudget n formula count := by
  induction formula generalizing count with
  | nil => rfl
  | cons clause rest ih =>
      cases truth : tautology clause with
      | false =>
          have shape : clean (clause::rest) = clause::clean rest := by simp [clean,truth]
          rw [shape,runBudget,runBudget]
          have tail := ih (count*(clause.length+1))
          have copied := growth_clean rest
          gcongr
      | true =>
          have shape : clean (clause::rest) = clean rest := by simp [clean,truth]
          rw [shape,runBudget]
          have tail := ih count
          have bound := runBudget_mono n rest count (count*(clause.length+1)) (by nlinarith)
          omega

def generate (n : Nat) (formula : Formula) : Execution :=
  let prepared := cleanRun formula
  let initial := Seed.generate prepared.value
  let packed := AffineCarrier.pack initial.value
  let generated := run n prepared.value packed.value
  ⟨generated.value,prepared.visits+initial.cells+packed.visits+generated.sourceCells+
    2*(formulaSize formula+formulaSize prepared.value)+2*storage generated.value+2*storage packed.value+9,
    generated.volumeSteps,generated.volumeInput⟩

theorem generate_value (n : Nat) (formula : Formula) : (generate n formula).value = Joint.generate n formula := by
  simp only [generate,Joint.generate,run_value]

def generateBudget (n : Nat) (formula : Formula) : Nat :=
  Cost.cleanBudget n formula.length (Cost.rowCount formula) (Cost.termCount formula)+runBudget n formula 1+
    Seed.generateBudget n formula.length (formulaSize formula)+4*cellBound n+5+
    4*formulaSize formula+2*Cost.growth formula*cellBound n+9

theorem seedBudget_mono (n smallCount largeCount smallSize largeSize : Nat)
    (count : smallCount ≤ largeCount) (size : smallSize ≤ largeSize) :
    Seed.generateBudget n smallCount smallSize ≤ Seed.generateBudget n largeCount largeSize := by
  unfold Seed.generateBudget Seed.extractBudget
  gcongr

theorem generate_cells (n : Nat) (formula : Formula) (inside : Within n formula) :
    (generate n formula).sourceCells ≤ generateBudget n formula := by
  have prepared := Cost.cleanRun_visits n formula inside
  have cleaned := clean_within n formula inside
  have initial := Seed.generate_valid n (clean formula) cleaned
  have seedCost := Seed.generate_cells n (clean formula) cleaned
  have seedBound := seedBudget_mono n _ _ _ _ (List.length_filter_le (fun clause => !tautology clause) formula) (Cost.clean_size formula)
  have packedValid := AffineCarrier.pack_valid n _ initial.1 initial.2
  have packedCost := AffineCarrier.Cost.pack_visits n _ initial.1 initial.2
  have packedLength := AffineCarrier.Cost.pack_length (Seed.generate (clean formula)).value
  have packedStorage := (AffineCarrier.Cost.storage_bound n _ packedValid).trans (Nat.mul_le_mul_right (cellBound n) packedLength)
  have final := run_cells n (clean formula) cleaned _ packedValid
  have inputBudget := runBudget_mono n (clean formula) _ _ packedLength
  have bounded := runBudget_clean n formula 1
  have size := Cost.clean_size formula
  have length := run_length n (clean formula) cleaned _ packedValid
  have lengthBound := Nat.mul_le_mul_right (Cost.growth (clean formula)) packedLength
  have growth := growth_clean formula
  have outputValid : Valid n (run n (clean formula) (AffineCarrier.pack (Seed.generate (clean formula)).value).value).value := by
    rw [run_value]
    exact Joint.run_valid n _ cleaned _ packedValid
  have stored := AffineCarrier.Cost.storage_bound n _ outputValid
  simp only [Nat.one_mul] at lengthBound packedStorage
  have output := stored.trans (Nat.mul_le_mul_right (cellBound n) ((length.trans lengthBound).trans growth))
  have seedPaid := seedCost.trans seedBound
  have finalPaid := final.trans (inputBudget.trans bounded)
  simp only [generate,generateBudget,cleanRun_value]
  nlinarith only [prepared,seedPaid,packedCost,finalPaid,size,output,packedStorage]

theorem generate_read (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Nat → Bool) :
    AffineCarrier.read (generate n formula).value assignment = formulaRead formula assignment := by
  rw [generate_value,Joint.generate_read n formula inside]

theorem generate_image (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Assignment n) :
    (∃ p : AffineCarrier.Parameters n (generate n formula).value,
      AffineCarrier.lift n (generate n formula).value p=assignment) ↔
      formulaRead formula (extendAssignment assignment) = true := by
  rw [generate_value,Joint.generate_image n formula inside]

end SaturationMonoid.ComplexityProjection.SATSource.AffineClauses.JointCost
