import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationLiteralRowsScalar

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLiteralRows
open PreparationVacuumDAGCoefficient PreparationVacuumDAGSemantic PreparationVacuumArenaCollect
open PreparationVacuumClockSymbol PreparationVacuumArenaRows PreparationVacuumSourceCacheRules
open PreparationVacuumMoyalNormalization
open scoped BigOperators Topology

def rationalRows {k : ℕ} (labels : CacheLabels k) (e : ArenaExpression k) : List (Row k) :=
  ArenaExpression.rec (motive_1:=fun _=>List (Row k)) (motive_2:=fun _=>List (List (Row k)))
    (fun c=>sourceCacheRows labels [scalarRow k c])
    (fun d j=>[atomRow (.source d j)])
    (fun l a=>[atomRow (.clock l a)])
    (fun r _ _ left right=>[atomRow (.moyal r (rowsExpression left) (rowsExpression right))])
    (fun c _ word=>sourceCacheRows labels (multiplyRows [⟨c,[]⟩] (productRows word)))
    (fun _ _ left right=>sourceCacheRows labels (left++right))
    [] (fun _ _ head tail=>head::tail) e

@[simp] theorem rationalRows_literal {k : ℕ} (labels : CacheLabels k) (c : ℝ) :
    rationalRows labels (.literal c:ArenaExpression k)=sourceCacheRows labels [scalarRow k c] := rfl
@[simp] theorem rationalRows_moyal {k : ℕ} (labels : CacheLabels k) (r : ℕ) (e f : ArenaExpression k) :
    rationalRows labels (.moyal r e f)=
      [atomRow (.moyal r (rowsExpression (rationalRows labels e)) (rowsExpression (rationalRows labels f)))] := rfl
@[simp] theorem rationalRows_add {k : ℕ} (labels : CacheLabels k) (e f : ArenaExpression k) :
    rationalRows labels (.add e f)=sourceCacheRows labels (rationalRows labels e++rationalRows labels f) := rfl

theorem rationalRows_row {k : ℕ} (labels : CacheLabels k) (c : NormalizedCoefficient)
    (word : List (ArenaExpression k)) : rationalRows labels (.row c word)=
      sourceCacheRows labels (multiplyRows [⟨c,[]⟩] (productRows (word.map (rationalRows labels)))) := by
  suffices same : ArenaExpression.rec_1
      (motive_1:=fun _=>List (Row k)) (motive_2:=fun _=>List (List (Row k)))
      (fun c=>sourceCacheRows labels [scalarRow k c])
      (fun d j=>[atomRow (.source d j)]) (fun l a=>[atomRow (.clock l a)])
      (fun r _ _ left right=>[atomRow (.moyal r (rowsExpression left) (rowsExpression right))])
      (fun c _ word=>sourceCacheRows labels (multiplyRows [⟨c,[]⟩] (productRows word)))
      (fun _ _ left right=>sourceCacheRows labels (left++right))
      [] (fun _ _ head tail=>head::tail) word=word.map (rationalRows labels) by
    exact congrArg (fun word=>sourceCacheRows labels (multiplyRows [⟨c,[]⟩] (productRows word))) same
  induction word with
  | nil=>rfl
  | cons e rest ih=>change rationalRows labels e::_=rationalRows labels e::rest.map (rationalRows labels);rw [ih]

theorem rationalRows_source {k : ℕ} (labels : CacheLabels k) (e : ArenaExpression k) :
    ∀ x∈poleDomain,rowsValue (rationalRows labels e) x=arenaEvaluate e x := by
  refine ArenaExpression.rec
    (motive_1:=fun e=>∀ x∈poleDomain,rowsValue (rationalRows labels e) x=arenaEvaluate e x)
    (motive_2:=fun word=>∀ x∈poleDomain,
      ((word.map (rationalRows labels)).map (fun rows=>rowsValue rows x)).prod=orderedProduct (word.map arenaEvaluate) x)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro c x hx
    rw [rationalRows_literal,sourceCacheRows_source _ _ x hx]
    simp only [rowsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,scalarRow_value,add_zero,arenaEvaluate_literal]
  · intro d j x _
    change rowsValue [atomRow (.source d j)] x=_
    simp only [rowsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,atomRow_value,add_zero]
  · intro l a x _
    change rowsValue [atomRow (.clock l a)] x=_
    simp only [rowsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,atomRow_value,add_zero]
  · intro r e f he hf x hx
    simp only [rationalRows_moyal,rowsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      atomRow_value,add_zero,arenaEvaluate_moyal]
    apply moyal_germ
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      rw [rowsExpression_value,he y hy]
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      rw [rowsExpression_value,hf y hy]
  · intro c word ih x hx
    rw [rationalRows_row,sourceCacheRows_source _ _ x hx,multiplyRows_value _ _ x hx,
      productRows_value _ x hx,ih x hx]
    simp only [rowsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,rowValue,orderedProduct,
      List.map_nil,List.foldr_nil,mul_one,add_zero,arenaEvaluate_row,List.foldr_map]
  · intro e f he hf x hx
    rw [rationalRows_add,sourceCacheRows_source _ _ x hx]
    simp only [rowsValue,List.map_append,List.sum_append] at he hf ⊢
    rw [he x hx,hf x hx,arenaEvaluate_add]
  · intro x _;rfl
  · intro e word he ih x hx
    simp only [List.map_cons,List.prod_cons,orderedProduct,List.foldr_cons]
    rw [he x hx,ih x hx]
    rfl

theorem rationalRows_rational_literal {k : ℕ} (labels : CacheLabels k) (q : ℚ) :
    rationalRows labels (.literal (q : ℝ):ArenaExpression k)=
      sourceCacheRows labels [⟨polynomialCoefficient (MvPolynomial.C q),[]⟩] := by
  rw [rationalRows_literal,scalarRow_rational]

def rationalExpression {k : ℕ} (labels : CacheLabels k) (e : ArenaExpression k) : ArenaExpression k :=
  rowsExpression (rationalRows labels e)

theorem rationalExpression_source {k : ℕ} (labels : CacheLabels k) (e : ArenaExpression k)
    (x : Phase) (hx : x∈poleDomain) : arenaEvaluate (rationalExpression labels e) x=arenaEvaluate e x := by
  rw [rationalExpression,rowsExpression_value,rationalRows_source _ _ x hx]

end LowEnergy.PreparationVacuumLiteralRows
