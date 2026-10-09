import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationKernelOperators

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumRawTableBounds
open PreparationVacuumSharedPool PreparationVacuumExecutionGraph PreparationVacuumKernelValues
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumLiteralFeed
open PreparationVacuumNumericSource PreparationVacuumSourceSerialization PreparationVacuumArenaRows PreparationVacuumLiteralAdmission
open PreparationVacuumCentralBudget PreparationVacuumArenaBudget PreparationVacuumMoyalBudget
open PreparationVacuumClockBudget PreparationVacuumCanonicalMoyal PreparationVacuumClockSymbol
open PreparationVacuumEngineSource PreparationVacuumEngineSmooth PreparationVacuumEngineBudget
open scoped BigOperators Topology
abbrev ArrayBound := PreparationVacuumCentralBudget.ArrayBound
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

-- This fold reads the actual node and polynomial pools. Clock references remain
-- lookups in the supplied earlier-stage array environment.
def rawNodeBounds {K : ℕ} (clock : ClockBounds K) (previous : ℕ → ArrayBound) : RawKind → ArrayBound
  | .source d j=>literalLeafArrays d.castSucc j
  | .clock level axis=>if h : level < K then clock (Fin.succ ⟨level,h⟩) axis else constantArray 0
  | .moyal r left right=>fun m=>((100 : ℝ)^r/(r.factorial : ℝ))*
      productArray (fun n=>previous left (n+r)) (fun n=>previous right (n+r)) m

def rawBoundsStep {K : ℕ} (clock : ClockBounds K) (state : RawArena) (previous : ℕ → ArrayBound) (id : ℕ) : ArrayBound :=
  (rawRows state id).foldr (fun row out m=>
    (row.word.map (fun node=>rawNodeBounds clock previous (rawNode state node).kind)).foldl productArray
      (sourceCentralArray row.coefficient) m+out m) (constantArray 0)

def rawBoundsFuel {K : ℕ} (clock : ClockBounds K) (fuel : ℕ) (state : RawArena) : ℕ → ArrayBound :=
  Nat.rec (fun _=>constantArray 0) (fun _ previous=>rawBoundsStep clock state previous) fuel

def rawTableBounds {K : ℕ} (clock : ClockBounds K) (state : RawArena) (id : ℕ) : ArrayBound :=
  rawBoundsFuel clock state.polynomials.length state id

theorem rawNodeBounds_expression {K : ℕ} (clock : ClockBounds K) (previous : ℕ → ArenaExpression K) (kind : RawKind) :
    rawNodeBounds clock (fun id=>expressionArray (tablePrimitives clock) (previous id)) kind=
      expressionArray (tablePrimitives clock) (rawNodeExpression K previous kind) := by
  cases kind with
  | source d j=>rfl
  | clock level axis=>
    simp only [rawNodeBounds,rawNodeExpression]
    split_ifs
    · rfl
    · change constantArray 0=constantArray |(0 : ℝ)|
      rw [abs_zero]
  | moyal r left right=>
    funext m
    simp only [rawNodeBounds,rawNodeExpression,expressionArray_moyal,moyalScale,convolution,productArray,Nat.add_comm]

theorem rawBoundsStep_expression {K : ℕ} (clock : ClockBounds K) (state : RawArena) (previous : ℕ → ArenaExpression K) (id : ℕ) :
    rawBoundsStep clock state (fun id=>expressionArray (tablePrimitives clock) (previous id)) id=
      expressionArray (tablePrimitives clock) (rawExpandStep K state previous id) := by
  unfold rawBoundsStep rawExpandStep
  generalize rawRows state id=rows
  induction rows with
  | nil=>simp only [List.foldr_nil,expressionArray_literal,abs_zero]
  | cons row rows ih=>
    simp only [List.foldr_cons,expressionArray_add,expressionArray_row] at ih ⊢
    rw [PreparationVacuumSerializedSource.ordered_bounds_left_fold]
    funext m
    congr 1
    · have nodes : row.word.map (fun node=>rawNodeBounds clock (fun id=>expressionArray (tablePrimitives clock) (previous id)) (rawNode state node).kind)=
        (row.word.map (fun node=>rawNodeExpression K previous (rawNode state node).kind)).map (expressionArray (tablePrimitives clock)) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro node member
        exact rawNodeBounds_expression clock previous (rawNode state node).kind
      rw [nodes]
      rfl
    · exact congrFun ih m

theorem rawBoundsFuel_expression {K : ℕ} (clock : ClockBounds K) (fuel : ℕ) (state : RawArena) :
    rawBoundsFuel clock fuel state=fun id=>expressionArray (tablePrimitives clock) (rawExpand K fuel state id) := by
  induction fuel with
  | zero=>
    funext id
    change constantArray 0=constantArray |(0 : ℝ)|
    rw [abs_zero]
  | succ fuel ih=>
    change rawBoundsStep clock state (rawBoundsFuel clock fuel state)=_
    rw [ih]
    funext id
    exact rawBoundsStep_expression clock state (rawExpand K fuel state) id

theorem rawTableBounds_expression {K : ℕ} (clock : ClockBounds K) (state : RawArena) (id : ℕ) :
    rawTableBounds clock state id=expressionArray (tablePrimitives clock) (expanded K state id) := by
  exact congrFun (rawBoundsFuel_expression clock state.polynomials.length state) id

theorem rawTableBounds_equation {K : ℕ} (clock : ClockBounds K) (state : RawArena) (closed : RawMoyalClosed state)
    (id : ℕ) (valid : Handle state id) :
    rawTableBounds clock state id=rawBoundsStep clock state (rawTableBounds clock state) id := by
  rw [rawTableBounds_expression]
  have values : rawTableBounds clock state=fun id=>expressionArray (tablePrimitives clock) (expanded K state id) := by
    funext id;exact rawTableBounds_expression clock state id
  rw [values,rawBoundsStep_expression]
  exact congrArg (expressionArray (tablePrimitives clock)) (rawExpand_equation K state closed id valid)

theorem rawTableBounds_prefix {K : ℕ} (clock : ClockBounds K) {old next : RawArena} (growth : RawExtends old next)
    (closed : RawMoyalClosed old) (id : ℕ) (valid : Handle old id) :
    rawTableBounds clock next id=rawTableBounds clock old id := by
  rw [rawTableBounds_expression,rawTableBounds_expression,expanded_prefix K growth closed id valid]

theorem rawTableBounds_nonnegative {K : ℕ} (clock : ClockBounds K) (positive : ∀ l a,Nonnegative (clock l a))
    (state : RawArena) (id : ℕ) : Nonnegative (rawTableBounds clock state id) := by
  rw [rawTableBounds_expression]
  exact expressionArray_nonnegative _ (tablePrimitives_nonnegative clock positive) _

theorem rawTableBounds_budget {K : ℕ} (clock : ClockBounds K) (positive : ∀ l a,Nonnegative (clock l a))
    (state : RawArena) (id : ℕ) (x : Phase) (hx : x∈poleDomain) (N : ℕ)
    (primitives : PrimitiveBounds (tablePrimitives clock) (derivativeDemand (expanded K state id) N) x) :
    ComplexJetBound (nativePolynomial K state id) N (rawTableBounds clock state id) x := by
  rw [rawTableBounds_expression]
  exact actual_expression_budget _ (tablePrimitives_nonnegative clock positive) _ x hx primitives _ N le_rfl

def ClockAgreement {K L : ℕ} (state : RawArena) (left : ClockBounds K) (right : ClockBounds L) : Prop :=
  ∀ node,node∈state.nodes → ∀ level axis,node.kind=.clock level axis →
    rawNodeBounds left (fun _=>constantArray 0) (.clock level axis)=rawNodeBounds right (fun _=>constantArray 0) (.clock level axis)

theorem rawNodeBounds_congr {K L : ℕ} (leftClock : ClockBounds K) (rightClock : ClockBounds L)
    (left right : ℕ → ArrayBound) (kind : RawKind)
    (clocks : ∀ level axis,kind=.clock level axis →
      rawNodeBounds leftClock (fun _=>constantArray 0) kind=rawNodeBounds rightClock (fun _=>constantArray 0) kind)
    (children : ∀ dep,dep∈kind.dependencies → left dep=right dep) :
    rawNodeBounds leftClock left kind=rawNodeBounds rightClock right kind := by
  cases kind with
  | source d j=>rfl
  | clock level axis=>exact clocks level axis rfl
  | moyal r a b=>simp only [rawNodeBounds,children a (by simp [RawKind.dependencies]),children b (by simp [RawKind.dependencies])]

theorem rawBoundsStep_congr {K L : ℕ} (leftClock : ClockBounds K) (rightClock : ClockBounds L) (state : RawArena)
    (left right : ℕ → ArrayBound) (id : ℕ)
    (same : ∀ row,row∈rawRows state id → ∀ node,node∈row.word →
      rawNodeBounds leftClock left (rawNode state node).kind=rawNodeBounds rightClock right (rawNode state node).kind) :
    rawBoundsStep leftClock state left id=rawBoundsStep rightClock state right id := by
  unfold rawBoundsStep
  generalize rawRows state id=rows at same ⊢
  induction rows with
  | nil=>rfl
  | cons row rows ih=>
    simp only [List.foldr_cons]
    have head : row.word.map (fun node=>rawNodeBounds leftClock left (rawNode state node).kind)=
        row.word.map (fun node=>rawNodeBounds rightClock right (rawNode state node).kind) := by
      apply List.map_congr_left
      intro node member
      exact same row (by simp) node member
    rw [head,ih (fun row member=>same row (List.mem_cons_of_mem _ member))]

theorem rawBoundsFuel_clock_agree {K L : ℕ} (left : ClockBounds K) (right : ClockBounds L) (state : RawArena)
    (closed : RawMoyalClosed state) (clocks : ClockAgreement state left right) (fuel : ℕ) :
    rawBoundsFuel left fuel state=rawBoundsFuel right fuel state := by
  induction fuel with
  | zero=>rfl
  | succ fuel ih=>
    funext id
    change rawBoundsStep left state (rawBoundsFuel left fuel state) id=rawBoundsStep right state (rawBoundsFuel right fuel state) id
    apply rawBoundsStep_congr
    intro row member node inWord
    have valid:=rawRows_words state closed id row member node inWord
    apply rawNodeBounds_congr
    · intro level axis kind
      simpa only [kind] using clocks (rawNode state node) (rawNode_member state node valid) level axis kind
    · intro dep _;exact congrFun ih dep

theorem rawTableBounds_clock_agree {K L : ℕ} (left : ClockBounds K) (right : ClockBounds L) (state : RawArena)
    (closed : RawMoyalClosed state) (clocks : ClockAgreement state left right) (id : ℕ) :
    rawTableBounds left state id=rawTableBounds right state id :=
  congrFun (rawBoundsFuel_clock_agree left right state closed clocks state.polynomials.length) id

theorem rawTableBounds_supported_agree {K L : ℕ} (left : ClockBounds K) (right : ClockBounds L) (base current : RawArena)
    (growth : RawExtends base current) (baseClosed : RawMoyalClosed base) (closed : RawMoyalClosed current)
    (clocks : ClockAgreement base left right) (id : ℕ) (support : Supported base current id) :
    rawTableBounds left current id=rawTableBounds right current id := by
  rw [rawTableBounds_equation left current closed id support.1,rawTableBounds_equation right current closed id support.1]
  apply rawBoundsStep_congr
  intro row member node inWord
  have nodeValid:=support.2 row member node inWord
  rw [rawNode_preserved growth node nodeValid]
  apply rawNodeBounds_congr
  · intro level axis kind
    simpa only [kind] using clocks (rawNode base node) (rawNode_member base node nodeValid) level axis kind
  · intro dep member
    have valid:=baseClosed.nodes (rawNode base node) (rawNode_member base node nodeValid) dep member
    rw [rawTableBounds_prefix left growth baseClosed dep valid,rawTableBounds_prefix right growth baseClosed dep valid]
    exact rawTableBounds_clock_agree left right base baseClosed clocks dep

theorem actual_stage_table_equation (k : ℕ) (clock : ClockBounds (k+1)) (i : Fin 5) :
    rawTableBounds clock (originalEngine (k+1)).runtime.arena (originalFiveId k i)=
      rawBoundsStep clock (originalEngine (k+1)).runtime.arena
        (rawTableBounds clock (originalEngine (k+1)).runtime.arena) (originalFiveId k i) :=
  rawTableBounds_equation clock _ (originalEngine_graph_closed (k+1)) _ (originalFive_handle k i)

end LowEnergy.PreparationVacuumRawTableBounds
