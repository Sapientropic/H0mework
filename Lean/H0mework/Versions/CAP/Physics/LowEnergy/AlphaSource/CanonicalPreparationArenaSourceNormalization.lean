import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationArenaCollectProducts

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumArenaCollect
open PreparationVacuumPoleCancellation PreparationVacuumDAGCoefficient PreparationVacuumDAGSemantic
open PreparationVacuumClockSymbol PreparationVacuumCanonicalMoyal PreparationVacuumArenaRows
open PreparationVacuumCentralBudget PreparationVacuumEngineBudget PreparationVacuumEngineSource
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators Topology


def rowsExpression {k : ℕ} (rows : List (Row k)) : ArenaExpression k :=
  rows.foldr (fun row out=>.add (.row row.coefficient row.word) out) (.literal 0)

theorem rowsExpression_value {k : ℕ} (rows : List (Row k)) (x : Phase) :
    arenaEvaluate (rowsExpression rows) x=rowsValue rows x := by
  induction rows with
  | nil=>simp [rowsExpression,rowsValue,arenaEvaluate_literal]
  | cons row rest ih=>
    simp only [rowsExpression,List.foldr_cons,arenaEvaluate_add,arenaEvaluate_row]
    simp only [rowsExpression] at ih
    rw [ih]
    simp only [rowsValue,List.map_cons,List.sum_cons,rowValue,orderedProduct,List.foldr_map]

def atomRow {k : ℕ} (e : ArenaExpression k) : Row k := ⟨polynomialCoefficient 1,[e]⟩

theorem atomRow_value {k : ℕ} (e : ArenaExpression k) (x : Phase) : rowValue (atomRow e) x=arenaEvaluate e x := by
  simp [rowValue,atomRow,polynomialCoefficient_source,polynomialSymbol,orderedProduct]

def sourceRows {k : ℕ} (e : ArenaExpression k) : List (Row k) :=
  ArenaExpression.rec (motive_1:=fun _=>List (Row k)) (motive_2:=fun _=>List (List (Row k)))
    (fun c=>[atomRow (.literal c)])
    (fun d j=>[atomRow (.source d j)])
    (fun l a=>[atomRow (.clock l a)])
    (fun r _ _ left right=>[atomRow (.moyal r (rowsExpression left) (rowsExpression right))])
    (fun c _ word=>collectRows (multiplyRows [⟨c,[]⟩] (productRows word)))
    (fun _ _ left right=>collectRows (left++right))
    [] (fun _ _ head tail=>head::tail) e

@[simp] theorem sourceRows_literal {k : ℕ} (c : ℝ) : sourceRows (.literal c:ArenaExpression k)=[atomRow (.literal c)] := rfl
@[simp] theorem sourceRows_source {k : ℕ} (d : Fin 3) (j : Fin 14) : sourceRows (.source d j:ArenaExpression k)=[atomRow (.source d j)] := rfl
@[simp] theorem sourceRows_clock {k : ℕ} (l : Fin (k+1)) (a : Fin 4) : sourceRows (.clock l a:ArenaExpression k)=[atomRow (.clock l a)] := rfl
@[simp] theorem sourceRows_moyal {k : ℕ} (r : ℕ) (e f : ArenaExpression k) :
    sourceRows (.moyal r e f)=[atomRow (.moyal r (rowsExpression (sourceRows e)) (rowsExpression (sourceRows f)))] := rfl
@[simp] theorem sourceRows_add {k : ℕ} (e f : ArenaExpression k) : sourceRows (.add e f)=collectRows (sourceRows e++sourceRows f) := rfl

theorem sourceRows_row {k : ℕ} (c : NormalizedCoefficient) (word : List (ArenaExpression k)) :
    sourceRows (.row c word)=collectRows (multiplyRows [⟨c,[]⟩] (productRows (word.map sourceRows))) := by
  suffices same : ArenaExpression.rec_1
      (motive_1:=fun _=>List (Row k)) (motive_2:=fun _=>List (List (Row k)))
      (fun c=>[atomRow (.literal c)]) (fun d j=>[atomRow (.source d j)]) (fun l a=>[atomRow (.clock l a)])
      (fun r _ _ left right=>[atomRow (.moyal r (rowsExpression left) (rowsExpression right))])
      (fun c _ word=>collectRows (multiplyRows [⟨c,[]⟩] (productRows word)))
      (fun _ _ left right=>collectRows (left++right)) [] (fun _ _ head tail=>head::tail) word=word.map sourceRows by
    exact congrArg (fun word=>collectRows (multiplyRows [⟨c,[]⟩] (productRows word))) same
  induction word with
  | nil=>rfl
  | cons e rest ih=>change sourceRows e::_=sourceRows e::rest.map sourceRows;rw [ih]

private theorem coefficient_germ (r : ℕ) (f f' g g' : PreparationVacuumCanonicalMoyal.Symbol)
    (x : Phase) (left : f=ᶠ[𝓝 x]f') (right : g=ᶠ[𝓝 x]g') : coefficient r f g x=coefficient r f' g' x := by
  have fj : ∀ w : Word r,jet r f w x=jet r f' w x := fun w=>
    congrArg (fun D=>D (slotDirection∘w)) ((left.iteratedFDeriv ℝ r).eq_of_nhds)
  have gj : ∀ w : Word r,jet r g w x=jet r g' w x := fun w=>
    congrArg (fun D=>D (slotDirection∘w)) ((right.iteratedFDeriv ℝ r).eq_of_nhds)
  simp only [coefficient,contraction,fj,gj]

private theorem complexMoyal_germ (r : ℕ) (f f' g g' : Phase→ℂ)
    (x : Phase) (left : f=ᶠ[𝓝 x]f') (right : g=ᶠ[𝓝 x]g') : complexMoyal r f g x=complexMoyal r f' g' x := by
  have fre : (fun y=>(f y).re)=ᶠ[𝓝 x](fun y=>(f' y).re) := left.fun_comp Complex.re
  have fim : (fun y=>(f y).im)=ᶠ[𝓝 x](fun y=>(f' y).im) := left.fun_comp Complex.im
  have gre : (fun y=>(g y).re)=ᶠ[𝓝 x](fun y=>(g' y).re) := right.fun_comp Complex.re
  have gim : (fun y=>(g y).im)=ᶠ[𝓝 x](fun y=>(g' y).im) := right.fun_comp Complex.im
  simp only [complexMoyal,coefficient_germ r _ _ _ _ x fre gre,coefficient_germ r _ _ _ _ x fim gim,
    coefficient_germ r _ _ _ _ x fre gim,coefficient_germ r _ _ _ _ x fim gre]

theorem sourceRows_value {k : ℕ} (e : ArenaExpression k) :
    ∀ x∈poleDomain,rowsValue (sourceRows e) x=arenaEvaluate e x := by
  refine ArenaExpression.rec
    (motive_1:=fun e=>∀ x∈poleDomain,rowsValue (sourceRows e) x=arenaEvaluate e x)
    (motive_2:=fun word=>∀ x∈poleDomain,
      ((word.map sourceRows).map (fun rows=>rowsValue rows x)).prod=orderedProduct (word.map arenaEvaluate) x)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro c x _;simp only [sourceRows_literal,rowsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,atomRow_value,add_zero]
  · intro d j x _;simp only [sourceRows_source,rowsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,atomRow_value,add_zero]
  · intro l a x _;simp only [sourceRows_clock,rowsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,atomRow_value,add_zero]
  · intro r e f he hf x hx
    simp only [sourceRows_moyal,rowsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,atomRow_value,add_zero,arenaEvaluate_moyal]
    apply complexMoyal_germ
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      rw [rowsExpression_value,he y hy]
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      rw [rowsExpression_value,hf y hy]
  · intro c word ih x hx
    rw [sourceRows_row,collectRows_value _ x hx,multiplyRows_value _ _ x hx,productRows_value _ x hx,ih x hx]
    simp only [rowsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,rowValue,orderedProduct,
      List.map_nil,List.foldr_nil,mul_one,add_zero,arenaEvaluate_row,List.foldr_map]
  · intro e f he hf x hx
    rw [sourceRows_add,collectRows_value _ x hx]
    simp only [rowsValue,List.map_append,List.sum_append] at he hf ⊢
    rw [he x hx,hf x hx,arenaEvaluate_add]
  · intro x _;rfl
  · intro e word he ih x hx
    simp only [List.map_cons,List.prod_cons,orderedProduct,List.foldr_cons]
    rw [he x hx,ih x hx]
    rfl

def normalizedExpression {k : ℕ} (e : ArenaExpression k) : ArenaExpression k := rowsExpression (sourceRows e)

theorem normalizedExpression_source {k : ℕ} (e : ArenaExpression k) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (normalizedExpression e) x=arenaEvaluate e x := by
  rw [normalizedExpression,rowsExpression_value,sourceRows_value e x hx]

def normalizedEnergyExpression (k : ℕ) : ArenaExpression 0 := normalizedExpression (arena_energy_expr k)

theorem normalizedEnergy_source (k : ℕ) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (normalizedEnergyExpression k) x=(sourceEngineEnergy k x : ℂ) :=
  (normalizedExpression_source _ x hx).trans (arena_energy_readback k x hx)

def normalizedEnergyArray {x : Phase} {N : ℕ} (central : PrimitiveInputs x N)
    (leaf : Fin 3 → Fin 14 → PreparationVacuumCentralBudget.ArrayBound) (k : ℕ) : PreparationVacuumCentralBudget.ArrayBound :=
  expressionArray (canceledSourceArrays central leaf) (normalizedEnergyExpression k)

theorem actual_normalized_energy_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ)
    (central : PrimitiveInputs (z,WithLp.toLp 2 u) N)
    (leaf : Fin 3 → Fin 14 → PreparationVacuumCentralBudget.ArrayBound) (positive : ∀ d j m,0 ≤ leaf d j m)
    (bounds : ∀ d j,FiniteBound (PreparationVacuumCanonicalMoyal.originalLeaf d j) N (leaf d j) (z,WithLp.toLp 2 u))
    (k M : ℕ) (paid : derivativeDemand (normalizedEnergyExpression k) M≤N) :
    FiniteBound (sourceEngineEnergy k) M (normalizedEnergyArray central leaf k) (z,WithLp.toLp 2 u) := by
  have hx:=PreparationVacuumClockBudget.sourceUnit_admitted z u zbox ubox unit
  have actual:=actual_expression_budget (canceledSourceArrays central leaf)
    (canceledSourceArrays_nonnegative central leaf positive) N _ hx
    (canceledSourceArrays_bounds z u zbox ubox unit N central leaf bounds) (normalizedEnergyExpression k) M paid
  have germ : arenaEvaluate (normalizedEnergyExpression k)=ᶠ[𝓝 (z,WithLp.toLp 2 u)]
      (fun x=>(sourceEngineEnergy k x : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with x h
    exact normalizedEnergy_source k x h
  intro m hm w
  have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  have result:=actual m hm w
  rw [read,realCast_jet _ (PreparationVacuumEngineSmooth.sourceEngineEnergy_smooth k) m w _ hx,
    Complex.norm_real,Real.norm_eq_abs] at result
  exact result

end LowEnergy.PreparationVacuumArenaCollect
