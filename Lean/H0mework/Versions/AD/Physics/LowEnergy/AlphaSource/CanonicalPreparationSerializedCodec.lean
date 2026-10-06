import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLiteralStages

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSerializedSource
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient
open PreparationVacuumLiteralFeed PreparationVacuumArenaRows PreparationVacuumCentralBudget
open scoped BigOperators

inductive NodeKind (expressions : ℕ) where
  | source (degree : Fin 2) (slot : Fin 14)
  | clock (order : Fin 4) (axis : Fin 4) (definition : Fin expressions)
  | moyal (order : ℕ) (left right : Fin expressions)
  deriving DecidableEq

structure Node (expressions : ℕ) where
  central : Bool
  kind : NodeKind expressions
  deriving DecidableEq

structure RawRow (nodes coefficients : ℕ) where
  word : List (Fin nodes)
  coefficient : Fin coefficients
  deriving DecidableEq

structure SourceTable (expressions nodes coefficients : ℕ) where
  node : Fin nodes → Node expressions
  rows : Fin expressions → List (RawRow nodes coefficients)
  coefficient : Fin coefficients → NormalizedCoefficient
  height : Fin expressions → ℕ

def NodeKind.dependencies {p : ℕ} : NodeKind p → List (Fin p)
  | .source _ _=>[]
  | .clock _ _ e=>[e]
  | .moyal _ a b=>[a,b]

def NodeKind.expression {p : ℕ} (previous : Fin p → ArenaExpression 0) : NodeKind p → ArenaExpression 0
  | .source d j=>.source (Fin.castSucc d) j
  | .clock _ _ e=>previous e
  | .moyal r a b=>.moyal r (previous a) (previous b)

def sourceStep {p n c : ℕ} (source : SourceTable p n c) (previous : Fin p → ArenaExpression 0)
    (e : Fin p) : ArenaExpression 0 :=
  (source.rows e).foldr (fun row out=>.add
    (.row (source.coefficient row.coefficient)
      (row.word.map (fun i=>(source.node i).kind.expression previous))) out) (.literal 0)

def decode {p n c : ℕ} (source : SourceTable p n c) (fuel : ℕ) : Fin p → ArenaExpression 0 :=
  Nat.rec (fun _=>.literal 0) (fun _ previous=>sourceStep source previous) fuel

structure SourceClosed {p n c : ℕ} (source : SourceTable p n c) : Prop where
  positive : ∀ e,0<source.height e
  decreases : ∀ e row,row∈source.rows e → ∀ i,i∈row.word →
    ∀ dep,dep∈(source.node i).kind.dependencies → source.height dep<source.height e

theorem node_expression_congr {p : ℕ} (node : NodeKind p) (left right : Fin p → ArenaExpression 0)
    (same : ∀ e,e∈node.dependencies → left e=right e) : node.expression left=node.expression right := by
  cases node with
  | source d j=>rfl
  | clock k a e=>exact same e (by simp [NodeKind.dependencies])
  | moyal r a b=>simp only [NodeKind.expression,same a (by simp [NodeKind.dependencies]),
      same b (by simp [NodeKind.dependencies])]

theorem sourceStep_congr {p n c : ℕ} (source : SourceTable p n c) (e : Fin p)
    (left right : Fin p → ArenaExpression 0)
    (same : ∀ row,row∈source.rows e → ∀ i,i∈row.word →
      ∀ dep,dep∈(source.node i).kind.dependencies → left dep=right dep) :
    sourceStep source left e=sourceStep source right e := by
  unfold sourceStep
  have rows : ∀ (rs : List (RawRow n c)),
      (∀ row,row∈rs → ∀ i,i∈row.word → ∀ dep,dep∈(source.node i).kind.dependencies → left dep=right dep) →
      rs.foldr (fun row out=>ArenaExpression.add
        (.row (source.coefficient row.coefficient) (row.word.map (fun i=>(source.node i).kind.expression left))) out) (.literal 0)=
      rs.foldr (fun row out=>ArenaExpression.add
        (.row (source.coefficient row.coefficient) (row.word.map (fun i=>(source.node i).kind.expression right))) out) (.literal 0) := by
    intro rs
    induction rs with
    | nil=>intro _;rfl
    | cons row rs ih=>
      intro h
      simp only [List.foldr_cons]
      apply congrArg₂ ArenaExpression.add
      · apply congrArg (ArenaExpression.row (source.coefficient row.coefficient))
        apply List.map_congr_left
        intro i hi
        exact node_expression_congr _ _ _ (h row (by simp) i hi)
      · exact ih (fun r hr=>h r (by simp [hr]))
  exact rows _ same

theorem decode_stable {p n c : ℕ} (source : SourceTable p n c) (closed : SourceClosed source)
    (fuel : ℕ) (e : Fin p) (paid : source.height e≤fuel) : decode source (fuel+1) e=decode source fuel e := by
  induction fuel generalizing e with
  | zero=>have h:=closed.positive e;omega
  | succ fuel ih=>
    change sourceStep source (decode source (fuel+1)) e=sourceStep source (decode source fuel) e
    apply sourceStep_congr
    intro row hrow i hi dep hd
    exact ih dep (by have h:=closed.decreases e row hrow i hi dep hd;omega)

theorem decode_exact_equation {p n c : ℕ} (source : SourceTable p n c) (closed : SourceClosed source)
    (fuel : ℕ) (paid : ∀ e,source.height e≤fuel) (e : Fin p) :
    decode source fuel e=sourceStep source (decode source fuel) e :=
  (decode_stable source closed fuel e (paid e)).symm

def rowsValid {p n c : ℕ} (source : SourceTable p n c) (e : Fin p) : Bool :=
  decide (0<source.height e) && (source.rows e).all (fun row=>row.word.all (fun i=>
    (source.node i).kind.dependencies.all (fun dep=>decide (source.height dep<source.height e))))

theorem sourceClosed_of_rowsValid {p n c : ℕ} (source : SourceTable p n c)
    (valid : ∀ e,rowsValid source e=true) : SourceClosed source := by
  constructor
  · intro e
    have h:=(Bool.and_eq_true_iff.mp (valid e)).1
    simpa only [decide_eq_true_eq] using h
  · intro e row hr i hi dep hd
    have h:=(Bool.and_eq_true_iff.mp (valid e)).2
    have rowH:=List.all_eq_true.mp h row hr
    have nodeH:=List.all_eq_true.mp rowH i hi
    have depH:=List.all_eq_true.mp nodeH dep hd
    exact of_decide_eq_true depH

end LowEnergy.PreparationVacuumSerializedSource
