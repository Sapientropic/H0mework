import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationPoleArenaConsumer

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumArenaCollect
open PreparationVacuumPoleCancellation PreparationVacuumDAGCoefficient PreparationVacuumDAGSemantic
open PreparationVacuumClockSymbol PreparationVacuumCanonicalMoyal PreparationVacuumArenaRows
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
open scoped BigOperators

structure Row (k : ℕ) where
  coefficient : NormalizedCoefficient
  word : List (ArenaExpression k)

def rowValue {k : ℕ} (row : Row k) (x : Phase) : ℂ :=
  (coefficientValue row.coefficient x : ℂ)*orderedProduct (row.word.map arenaEvaluate) x

def rowsValue {k : ℕ} (rows : List (Row k)) (x : Phase) : ℂ := (rows.map (fun row=>rowValue row x)).sum

def insertRow {k : ℕ} (row : Row k) (rows : List (Row k)) : List (Row k) := by
  classical
  exact List.rec (motive:=fun _=>Row k→List (Row k)) (fun row=>[row])
    (fun head rest next row=>
      if row.word=head.word then {head with coefficient:=cancelCoefficient (addCoefficient row.coefficient head.coefficient)}::rest
      else head::next row) rows row

-- The recursion preserves the ordered source word. It combines only literally
-- equal words and never changes a Moyal operand or a CAR restriction.
theorem insertRow_value {k : ℕ} (row : Row k) (rows : List (Row k)) (x : Phase) (hx : x∈poleDomain) :
    rowsValue (insertRow row rows) x=rowValue row x+rowsValue rows x := by
  induction rows with
  | nil=>simp [insertRow,rowsValue]
  | cons head tail ih=>
    by_cases same : row.word=head.word
    · simp only [insertRow,if_pos same,rowsValue,List.map_cons,List.sum_cons,rowValue,
        cancelCoefficient_source _ x hx,addCoefficient_source _ _ x hx,Complex.ofReal_add]
      rw [same]
      ring
    · simp only [insertRow,if_neg same,rowsValue,List.map_cons,List.sum_cons]
      change rowValue head x+rowsValue (insertRow row tail) x=_
      rw [ih]
      simp only [rowsValue]
      ring

def collectRows {k : ℕ} (rows : List (Row k)) : List (Row k) := rows.foldr insertRow []

theorem collectRows_value {k : ℕ} (rows : List (Row k)) (x : Phase) (hx : x∈poleDomain) :
    rowsValue (collectRows rows) x=rowsValue rows x := by
  induction rows with
  | nil=>rfl
  | cons head tail ih=>
    change rowsValue (insertRow head (collectRows tail)) x=_
    rw [insertRow_value _ _ x hx,ih]
    rfl

end LowEnergy.PreparationVacuumArenaCollect
