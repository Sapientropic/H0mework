import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationSerializationDualPool

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceSerialization
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumArenaCollect
open PreparationVacuumLiteralAdmission PreparationVacuumLiteralFeed PreparationVacuumNumericSource PreparationVacuumArenaRows
open PreparationVacuumMoyalBudget PreparationVacuumCentralBudget PreparationVacuumArenaBudget PreparationVacuumClockBudget
open PreparationVacuumEngineSource PreparationVacuumEngineSmooth PreparationVacuumCanonicalMoyal
open PreparationVacuumTailSupport PreparationVacuumClockSymbol PreparationVacuumEngineBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators Topology

abbrev ArrayBound := PreparationVacuumCentralBudget.ArrayBound

abbrev ClockBounds (k : ℕ) := Fin (k+1) → Fin 4 → ArrayBound

def tablePrimitives {k : ℕ} (previous : ClockBounds k) : PrimitiveArrays k where
  leaf:=literalLeafArrays
  clock:=previous
  central:=sourceCentralArray


-- Exact Bounds.expression order: start at the central coefficient, multiply
-- each ordered atom, and then sum rows. No triangle estimate is substituted.
def boundsRows {k : ℕ} (input : PrimitiveArrays k) (rows : List (Row k)) : ArrayBound :=
  rows.foldr (fun row out m=>
    (row.word.map (expressionArray input)).foldl productArray (input.central row.coefficient) m+out m)
    (constantArray 0)

theorem boundsRows_readback {k : ℕ} (input : PrimitiveArrays k) (rows : List (Row k)) :
    boundsRows input rows=expressionArray input (rowsExpression rows) := by
  induction rows with
  | nil=>simp only [boundsRows,rowsExpression,List.foldr_nil,expressionArray_literal,abs_zero]
  | cons row rows ih=>
    simp only [boundsRows,rowsExpression,List.foldr_cons,expressionArray_add,expressionArray_row] at ih ⊢
    rw [PreparationVacuumSerializedSource.ordered_bounds_left_fold,ih]

def polynomialTable {k : ℕ} (e : Expression k .symbol) : Fin (runSymbol e).2.polynomials.length → List (Row k) :=
  fun id=>(runSymbol e).2.polynomials[id.val]'id.isLt

theorem generated_target_table {k : ℕ} (e : Expression k .symbol) :
    polynomialTable e (targetHandle e)=targetRows e := rfl

theorem table_target_bounds {k : ℕ} (previous : ClockBounds k) (e : Expression k .symbol) :
    boundsRows (tablePrimitives previous) (polynomialTable e (targetHandle e))=
      expressionArray (tablePrimitives previous) (runSymbol e).1 := by
  rw [generated_target_table,boundsRows_readback,targetRows_readback]

theorem table_reindex_bounds {k n : ℕ} (input : PrimitiveArrays k) (table : Fin n → List (Row k))
    (reindex : Fin n ≃ Fin n) (target : Fin n) :
    boundsRows input ((table∘reindex.symm) (reindex target))=boundsRows input (table target) := by
  simp only [Function.comp_apply,Equiv.symm_apply_apply]

def clockRows (k : ℕ) (a : Fin 4) : List (Row k) := targetRows (referenceClockDefinition k a)
def energyRows (k : ℕ) : List (Row k) := targetRows (referenceEnergy k)

def clockStep {k : ℕ} (previous : ClockBounds k) (a : Fin 4) : ArrayBound :=
  expressionArray (tablePrimitives previous) (rowsExpression (clockRows k a))

def generatedClocks (k : ℕ) : ClockBounds k :=
  Nat.rec (motive:=fun k=>ClockBounds k) literalPrimitiveArrays.clock
    (fun _ previous=>Fin.lastCases (clockStep previous) previous) k


@[simp] theorem generatedClocks_last (k : ℕ) (a : Fin 4) :
    generatedClocks (k+1) (Fin.last (k+1)) a=clockStep (generatedClocks k) a := by
  simp only [generatedClocks,Fin.lastCases_last]

@[simp] theorem generatedClocks_previous (k : ℕ) (l : Fin (k+1)) (a : Fin 4) :
    generatedClocks (k+1) (Fin.castSucc l) a=generatedClocks k l a := by
  simp only [generatedClocks,Fin.lastCases_castSucc]

def generatedEnergy (k : ℕ) : ArrayBound :=
  match k with
  | 0=>literalEnergyArray 0
  | k+1=>expressionArray (tablePrimitives (generatedClocks k)) (rowsExpression (energyRows k))

def generatedFiveBounds (k : ℕ) (i : Fin 5) : ArrayBound :=
  Fin.lastCases (generatedEnergy k) (fun a=>generatedClocks k (Fin.last k) a) i

theorem tablePrimitives_nonnegative {k : ℕ} (previous : ClockBounds k)
    (positive : ∀ l a,Nonnegative (previous l a)) : PrimitiveNonnegative (tablePrimitives previous) where
  leaf:=literal_primitive_nonnegative.leaf
  clock:=positive
  central:=literal_primitive_nonnegative.central

theorem generatedClocks_nonnegative (k : ℕ) : ∀ l a,Nonnegative (generatedClocks k l a) := by
  induction k with
  | zero=>exact literal_primitive_nonnegative.clock
  | succ k ih=>
    intro l a
    induction l using Fin.lastCases with
    | last=>
      rw [generatedClocks_last]
      exact expressionArray_nonnegative _ (tablePrimitives_nonnegative _ ih) _
    | cast l=>simpa only [generatedClocks_previous] using ih l a

theorem generatedFive_nonnegative (k : ℕ) (i : Fin 5) : Nonnegative (generatedFiveBounds k i) := by
  induction i using Fin.lastCases with
  | cast a=>simpa only [generatedFiveBounds,Fin.lastCases_castSucc] using generatedClocks_nonnegative k (Fin.last k) a
  | last=>
    cases k with
    | zero=>exact literal_five_nonnegative 0 (Fin.last 4)
    | succ k=>exact expressionArray_nonnegative _ (tablePrimitives_nonnegative _ (generatedClocks_nonnegative k)) _

private theorem tablePrimitives_bounds {k : ℕ} (previous : ClockBounds k)
    (z u : FlatConfiguration) (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius) (unit : (∑ i : Fin 100,u i^2)=1)
    (N : ℕ) (clockPaid : ∀ l a,FiniteBound (sourceEngine k a l) N (previous l a) (z,WithLp.toLp 2 u)) :
    PrimitiveBounds (tablePrimitives previous) N (z,WithLp.toLp 2 u) := by
  have paid:=literal_primitive_bounds z u zbox ubox unit N
  exact ⟨paid.leaf,clockPaid,paid.central⟩

theorem generatedClocks_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius) (unit : (∑ i : Fin 100,u i^2)=1)
    (k : ℕ) : ∀ N l a,FiniteBound (sourceEngine k a l) N (generatedClocks k l a) (z,WithLp.toLp 2 u) := by
  have hx:=sourceUnit_admitted z u zbox ubox unit
  induction k with
  | zero=>intro N;exact (literal_primitive_bounds z u zbox ubox unit N).clock
  | succ k ih=>
    intro N l a
    induction l using Fin.lastCases with
    | cast l=>
      rw [sourceEngine_preserves,generatedClocks_previous]
      exact ih N l a
    | last=>
      rw [generatedClocks_last]
      let e:=rowsExpression (clockRows k a)
      have bound:=actual_expression_budget (tablePrimitives (generatedClocks k))
        (tablePrimitives_nonnegative _ (generatedClocks_nonnegative k)) (derivativeDemand e N)
        (z,WithLp.toLp 2 u) hx
        (tablePrimitives_bounds _ z u zbox ubox unit _ (ih _)) e N le_rfl
      have germ : arenaEvaluate e=ᶠ[𝓝 (z,WithLp.toLp 2 u)]
          (fun x=>(sourceEngine (k+1) a (Fin.last (k+1)) x : ℂ)) := by
        filter_upwards [poleDomain_open.mem_nhds hx] with x h
        exact (generated_target_native (referenceClockDefinition k a) x h).trans
          (congrArg (fun f : Symbol=>(f x : ℂ)) (referenceClockDefinition_native k a))
      intro m hm w
      have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
      have result:=bound m hm w
      rw [read,realCast_jet _ (sourceEngine_smooth (k+1) a (Fin.last (k+1))) m w _ hx,
        Complex.norm_real,Real.norm_eq_abs] at result
      exact result

theorem generatedEnergy_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius) (unit : (∑ i : Fin 100,u i^2)=1)
    (k N : ℕ) : FiniteBound (sourceEngineEnergy k) N (generatedEnergy k) (z,WithLp.toLp 2 u) := by
  cases k with
  | zero=>exact actual_literal_energy_budget z u zbox ubox unit 0 N
  | succ k=>
    have hx:=sourceUnit_admitted z u zbox ubox unit
    let e:=rowsExpression (energyRows k)
    have bound:=actual_expression_budget (tablePrimitives (generatedClocks k))
      (tablePrimitives_nonnegative _ (generatedClocks_nonnegative k)) (derivativeDemand e N)
      (z,WithLp.toLp 2 u) hx
      (tablePrimitives_bounds _ z u zbox ubox unit _ (generatedClocks_budget z u zbox ubox unit k _)) e N le_rfl
    have germ : arenaEvaluate e=ᶠ[𝓝 (z,WithLp.toLp 2 u)] (fun x=>(sourceEngineEnergy (k+1) x : ℂ)) := by
      filter_upwards [poleDomain_open.mem_nhds hx] with x h
      exact (generated_target_native (referenceEnergy k) x h).trans
        (congrArg (fun f : Symbol=>(f x : ℂ)) (referenceEnergy_native k))
    intro m hm w
    have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
    have result:=bound m hm w
    rw [read,realCast_jet _ (sourceEngineEnergy_smooth (k+1)) m w _ hx,
      Complex.norm_real,Real.norm_eq_abs] at result
    exact result

theorem generatedFive_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius) (unit : (∑ i : Fin 100,u i^2)=1)
    (k N : ℕ) (i : Fin 5) : FiniteBound (actualFiveSymbols k i) N (generatedFiveBounds k i) (z,WithLp.toLp 2 u) := by
  induction i using Fin.lastCases with
  | last=>exact generatedEnergy_budget z u zbox ubox unit k N
  | cast a=>simpa only [actualFiveSymbols,generatedFiveBounds,Fin.lastCases_castSucc] using
      generatedClocks_budget z u zbox ubox unit k N (Fin.last k) a


theorem generated_clock_table_fold (k : ℕ) (a : Fin 4) :
    generatedClocks (k+1) (Fin.last (k+1)) a=
      boundsRows (tablePrimitives (generatedClocks k))
        (polynomialTable (referenceClockDefinition k a) (targetHandle (referenceClockDefinition k a))) := by
  rw [generatedClocks_last,generated_target_table,boundsRows_readback]
  rfl

theorem generated_energy_table_fold (k : ℕ) :
    generatedEnergy (k+1)=boundsRows (tablePrimitives (generatedClocks k))
      (polynomialTable (referenceEnergy k) (targetHandle (referenceEnergy k))) := by
  rw [generated_target_table,boundsRows_readback]
  rfl

theorem generated_clock_atom_fold (k : ℕ) (l : Fin (k+1)) (a : Fin 4) :
    expressionArray (tablePrimitives (generatedClocks k)) (.clock l a)=generatedClocks k l a := rfl

theorem generated_moyal_fold (k r : ℕ) (left right : ArenaExpression k) (m : ℕ) :
    expressionArray (tablePrimitives (generatedClocks k)) (.moyal r left right) m=
      ((100 : ℝ)^r/(r.factorial : ℝ))*productArray
        (fun n=>expressionArray (tablePrimitives (generatedClocks k)) left (n+r))
        (fun n=>expressionArray (tablePrimitives (generatedClocks k)) right (n+r)) m := by
  simp only [expressionArray_moyal,moyalScale,convolution,productArray,Nat.add_comm]

theorem generated_unit_inputs (N : ℕ) : UnitEnergyInputs generatedFiveBounds N where
  coefficients:=by
    intro z zbox u ubox unit k _
    exact generatedEnergy_budget z u zbox ubox unit k N

theorem generated_unit_102 : UnitEnergyInputs generatedFiveBounds 102 := generated_unit_inputs 102

end LowEnergy.PreparationVacuumSourceSerialization
