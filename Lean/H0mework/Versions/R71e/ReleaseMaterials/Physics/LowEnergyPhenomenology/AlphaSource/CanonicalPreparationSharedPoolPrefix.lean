import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSerializationTableBounds

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSharedPool
open PreparationVacuumSourceSerialization PreparationVacuumDAGSemantic
open PreparationVacuumEngineSource PreparationVacuumEnginePaidDepth PreparationVacuumCanonicalMoyal
open PreparationVacuumClockSymbol PreparationVacuumArenaCollect
open scoped BigOperators
variable {K : ℕ}

structure Extends (old next : ArenaStore K) : Prop where
  nodes : old.nodes.IsPrefix next.nodes
  polynomials : old.polynomials.IsPrefix next.polynomials

theorem Extends.refl (state : ArenaStore K) : Extends state state := ⟨List.prefix_refl _,List.prefix_refl _⟩

theorem Extends.trans {a b c : ArenaStore K} (left : Extends a b) (right : Extends b c) : Extends a c :=
  ⟨left.nodes.trans right.nodes,left.polynomials.trans right.polynomials⟩

theorem intern_prefix {α : Type} (x : α) (pool : List α) : pool.IsPrefix (intern x pool) := by
  classical
  unfold intern
  split_ifs
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

theorem intern_list_prefix (items : List (ArenaExpression K)) (pool : List (ArenaExpression K)) :
    pool.IsPrefix (items.foldl (fun out e=>intern e out) pool) := by
  induction items generalizing pool with
  | nil=>exact List.prefix_refl _
  | cons e items ih=>exact (intern_prefix e pool).trans (ih (intern e pool))

theorem registerRows_extends (rows : List (Row K)) (state : ArenaStore K) : Extends state (registerRows rows state) :=
  ⟨intern_list_prefix _ _,intern_prefix _ _⟩

def Grows (action : Action K) : Prop := ∀ state,Extends state (action state).2

theorem normalize_grows (e : ArenaExpression K) : Grows (normalize e) := fun _=>registerRows_extends _ _

theorem unary_grows (op : ArenaExpression K → ArenaExpression K) (input : Action K)
    (h : Grows input) : Grows (unary op input) := by
  intro state
  exact (h state).trans (normalize_grows _ _)

theorem binary_grows (op : ArenaExpression K → ArenaExpression K → ArenaExpression K)
    (left right : Action K) (hl : Grows left) (hr : Grows right) : Grows (binary op left right) := by
  intro state
  exact ((hl state).trans (hr (left state).2)).trans (normalize_grows _ _)

theorem listSum_grows {ι : Type} (items : List ι) (actions : ι → Action K)
    (h : ∀ i,Grows (actions i)) : Grows (listSum items actions) := by
  induction items with
  | nil=>exact normalize_grows _
  | cons i items ih=>exact binary_grows _ _ _ (h i) ih

theorem finiteSum_grows {ι : Type} (items : Finset ι) (actions : ι → Action K)
    (h : ∀ i,Grows (actions i)) : Grows (finiteSum items actions) := listSum_grows _ _ h

theorem rowPair_grows (r : ℕ) (left right : Row K) : Grows (rowPair r left right) := by
  intro state
  exact ((registerRows_extends _ state).trans (registerRows_extends _ _)).trans (normalize_grows _ _)

theorem moyalAction_grows (r : ℕ) (left right : Action K) (hl : Grows left) (hr : Grows right) :
    Grows (moyalAction r left right) := by
  intro state
  unfold moyalAction
  split_ifs
  · exact ((hl state).trans (hr _)).trans (normalize_grows _ _)
  · exact ((hl state).trans (hr _)).trans
      (listSum_grows _ _ (fun row=>listSum_grows _ _ (rowPair_grows r row)) _)

theorem jordanAction_grows (r : ℕ) (left right : Action K) (hl : Grows left) (hr : Grows right) :
    Grows (jordanAction r left right) :=
  unary_grows _ _ (binary_grows _ _ _ (moyalAction_grows r left right hl hr) (moyalAction_grows r right left hr hl))

def CompiledGrows {K : ℕ} : (s : PreparationVacuumSourceSerialization.ExprSort) → CompiledAction K s → Prop
  | .symbol,action=>Grows action
  | .polynomial,action=>∀ u,Grows (action u)

theorem compileAction_grows {s : PreparationVacuumSourceSerialization.ExprSort}
    (e : PreparationVacuumSourceSerialization.Expression K s) : CompiledGrows s (compileAction e) := by
  induction e with
  | primitive p=>exact normalize_grows _
  | addS e f he hf=>exact binary_grows _ _ _ he hf
  | negS e he=>exact unary_grows _ _ he
  | mulS e f he hf=>exact binary_grows _ _ _ he hf
  | sumS terms ih=>exact finiteSum_grows _ _ ih
  | coefficient u e he=>exact he u
  | average e he=>exact finiteSum_grows _ _ (fun u=>binary_grows _ _ _ (normalize_grows _) (he u))
  | zeroP=>intro u;exact normalize_grows _
  | monomial u e he=>
    intro v
    change Grows (if u=v then compileAction e else returnExpression (.literal 0))
    split_ifs
    · exact he
    · exact normalize_grows _
  | addP e f he hf=>intro u;exact binary_grows _ _ _ (he u) (hf u)
  | negP e he=>intro u;exact unary_grows _ _ (he u)
  | mulP e f he hf=>
    intro u
    apply finiteSum_grows
    intro a
    apply finiteSum_grows
    intro b
    split_ifs
    · exact binary_grows _ _ _ (he a) (hf b)
    · exact normalize_grows _
  | sumP terms ih=>intro u;exact finiteSum_grows _ _ (fun i=>ih i u)
  | weighted r e f he hf=>
    intro u
    apply finiteSum_grows
    intro a
    apply finiteSum_grows
    intro b
    split_ifs
    · exact jordanAction_grows r _ _ (he a) (hf b)
    · exact normalize_grows _



theorem node_id_preserved {old next : ArenaStore K} (extension : Extends old next)
    (node : ArenaExpression K) (present : node∈old.nodes) :
    (nodeLabels next node).1=(nodeLabels old node).1 := by
  classical
  exact (extension.nodes.idxOf_eq_of_mem present).symm

def polynomialSerial (state : ArenaStore K) (rows : List (Row K)) : ℕ := by
  classical
  exact state.polynomials.idxOf rows

theorem polynomial_id_preserved {old next : ArenaStore K} (extension : Extends old next)
    (rows : List (Row K)) (present : rows∈old.polynomials) :
    polynomialSerial next rows=polynomialSerial old rows := by
  classical
  exact (extension.polynomials.idxOf_eq_of_mem present).symm

abbrev SourceExpression := PreparationVacuumSourceSerialization.Expression
abbrev SourcePrimitive := PreparationVacuumSourceSerialization.Primitive
abbrev SourceSort := PreparationVacuumSourceSerialization.ExprSort

def liftPrimitive {small big : ℕ} (paid : small≤big) : SourcePrimitive small → SourcePrimitive big
  | .base p=>.base p
  | .clockReference level axis=>.clockReference ⟨level.val,level.isLt.trans_le paid⟩ axis

theorem source_clock_lift {small big : ℕ} (paid : small≤big) (a : Fin 4) (level : Fin small) :
    sourceEngine big a (Fin.succ ⟨level.val,level.isLt.trans_le paid⟩)=sourceEngine small a (Fin.succ level) := by
  have source:=sourceEngine_preserves_paid small big paid a (level.val+1) (by omega)
  have hs : level.val+1<small+1:=by omega
  have hb : level.val+1<big+1:=by omega
  change (if h : level.val+1<big+1 then sourceEngine big a ⟨level.val+1,h⟩ else 0)=
    (if h : level.val+1<small+1 then sourceEngine small a ⟨level.val+1,h⟩ else 0) at source
  simp only [dif_pos hb,dif_pos hs] at source
  have left : Fin.succ (⟨level.val,level.isLt.trans_le paid⟩ : Fin big)=⟨level.val+1,hb⟩ := rfl
  have right : Fin.succ level=⟨level.val+1,hs⟩ := rfl
  rw [left,right]
  exact source

theorem liftPrimitive_value {small big : ℕ} (paid : small≤big) (p : SourcePrimitive small) :
    PreparationVacuumSourceSerialization.primitiveValue (liftPrimitive paid p)=
      PreparationVacuumSourceSerialization.primitiveValue p := by
  cases p with
  | base p=>rfl
  | clockReference level axis=>exact source_clock_lift paid axis level

def liftExpression {small big : ℕ} (paid : small≤big) {s : SourceSort} (e : SourceExpression small s) :
    SourceExpression big s :=
  PreparationVacuumSourceSerialization.Expression.rec (motive:=fun s _=>SourceExpression big s)
    (fun p=>.primitive (liftPrimitive paid p))
    (fun _ _ left right=>.addS left right) (fun _ e=>.negS e) (fun _ _ left right=>.mulS left right)
    (fun _ terms=>.sumS terms) (fun u _ e=>.coefficient u e) (fun _ e=>.average e)
    .zeroP (fun u _ e=>.monomial u e) (fun _ _ left right=>.addP left right) (fun _ e=>.negP e)
    (fun _ _ left right=>.mulP left right) (fun _ terms=>.sumP terms)
    (fun r _ _ left right=>.weighted r left right) e

theorem liftExpression_value {small big : ℕ} (paid : small≤big) {s : SourceSort} (e : SourceExpression small s) :
    PreparationVacuumSourceSerialization.evaluate (liftExpression paid e)=PreparationVacuumSourceSerialization.evaluate e := by
  induction e <;> simp_all [liftExpression,PreparationVacuumSourceSerialization.evaluate,liftPrimitive_value]


def readPolynomial (state : ArenaStore K) (id : ℕ) : ArenaExpression K :=
  (state.polynomials.map rowsExpression).getD id (.literal 0)

def emitReference (e : SourceExpression K .symbol) (state : ArenaStore K) : ℕ × ArenaStore K := by
  classical
  let result:=compileAction e state
  exact ((result.2.polynomials.map rowsExpression).idxOf result.1,result.2)

theorem emitReference_bound (e : SourceExpression K .symbol) (state : ArenaStore K) :
    (emitReference e state).1<(emitReference e state).2.polynomials.length := by
  classical
  have member:=compileAction_allocated e state
  simpa only [emitReference,List.length_map] using List.idxOf_lt_length_of_mem member

theorem emitReference_readback (e : SourceExpression K .symbol) (state : ArenaStore K) :
    readPolynomial (emitReference e state).2 (emitReference e state).1=(compileAction e state).1 := by
  classical
  have member:=compileAction_allocated e state
  exact (List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem member)).trans (List.getElem_idxOf _)

theorem readPolynomial_preserved {old next : ArenaStore K} (extension : Extends old next)
    (id : ℕ) (bound : id<old.polynomials.length) : readPolynomial next id=readPolynomial old id := by
  have oldBound : id<(old.polynomials.map rowsExpression).length:=by simpa using bound
  have nextBound : id<(next.polynomials.map rowsExpression).length:=by
    simpa using lt_of_lt_of_le bound extension.polynomials.length_le
  rw [readPolynomial,List.getD_eq_getElem _ _ nextBound,readPolynomial,List.getD_eq_getElem _ _ oldBound]
  exact ((extension.polynomials.map rowsExpression).getElem oldBound).symm

def executeExpressions (expressions : List (SourceExpression K .symbol)) :
    ArenaStore K → List ℕ × ArenaStore K :=
  List.rec (motive:=fun _=>ArenaStore K → List ℕ × ArenaStore K)
    (fun state=>([],state))
    (fun expression _ rest state=>
      let one:=emitReference expression state
      let next:=rest one.2
      (one.1::next.1,next.2)) expressions

theorem executeExpressions_extends (expressions : List (SourceExpression K .symbol)) (state : ArenaStore K) :
    Extends state (executeExpressions expressions state).2 := by
  induction expressions generalizing state with
  | nil=>exact Extends.refl _
  | cons e expressions ih=>exact (compileAction_grows e state).trans (ih (emitReference e state).2)


theorem executeExpressions_length (expressions : List (SourceExpression K .symbol)) (state : ArenaStore K) :
    (executeExpressions expressions state).1.length=expressions.length := by
  induction expressions generalizing state with
  | nil=>rfl
  | cons e expressions ih=>
    change ((emitReference e state).1::(executeExpressions expressions (emitReference e state).2).1).length = _
    simp only [List.length_cons,ih]

theorem executeExpressions_bounds (expressions : List (SourceExpression K .symbol)) (state : ArenaStore K) :
    ∀ id,id∈(executeExpressions expressions state).1 → id<(executeExpressions expressions state).2.polynomials.length := by
  induction expressions generalizing state with
  | nil=>simp only [executeExpressions,List.not_mem_nil,false_implies,implies_true]
  | cons e expressions ih=>
    intro id member
    change id∈(emitReference e state).1::(executeExpressions expressions (emitReference e state).2).1 at member
    rcases List.mem_cons.mp member with head|tail
    · subst id
      exact lt_of_lt_of_le (emitReference_bound e state)
        (executeExpressions_extends expressions (emitReference e state).2).polynomials.length_le
    · exact ih (emitReference e state).2 id tail

theorem executeExpressions_native (expressions : List (SourceExpression K .symbol)) (state : ArenaStore K)
    (x : PreparationVacuumCanonicalMoyal.Phase) (hx : x∈poleDomain) :
    List.Forall₂ (fun id (e : SourceExpression K .symbol)=>arenaEvaluate (readPolynomial (executeExpressions expressions state).2 id) x=
      (PreparationVacuumSourceSerialization.evaluate e x : ℂ)) (executeExpressions expressions state).1 expressions := by
  induction expressions generalizing state with
  | nil=>exact .nil
  | cons e expressions ih=>
    apply List.Forall₂.cons
    · change arenaEvaluate (readPolynomial (executeExpressions expressions (emitReference e state).2).2
        (emitReference e state).1) x=_
      rw [readPolynomial_preserved (executeExpressions_extends expressions (emitReference e state).2) _
        (emitReference_bound e state),emitReference_readback]
      exact compileAction_source e state x hx
    · exact ih (emitReference e state).2

end LowEnergy.PreparationVacuumSharedPool
