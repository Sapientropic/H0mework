import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalNormalizationBilinear

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMoyalNormalization
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumArenaBudget
open PreparationVacuumArenaRows PreparationVacuumArenaCollect PreparationVacuumClockSymbol
open PreparationVacuumCanonicalMoyal
open scoped BigOperators ContDiff Topology

def numericCoefficient (c : NormalizedCoefficient) : Prop :=
  c.poles=0 ∧ c.numerator=MvPolynomial.C (MvPolynomial.constantCoeff c.numerator)

def rowExpression {k : ℕ} (row : Row k) : ArenaExpression k := .row row.coefficient row.word

def wordExpression {k : ℕ} (word : List (ArenaExpression k)) : ArenaExpression k :=
  if word.isEmpty then .literal 1 else .row (polynomialCoefficient 1) word

def rowNumber {k : ℕ} (row : Row k) : ℝ := by
  classical
  exact if numericCoefficient row.coefficient then ((MvPolynomial.constantCoeff row.coefficient.numerator : ℚ) : ℝ) else 1

def rowOperand {k : ℕ} (row : Row k) : ArenaExpression k := by
  classical
  exact if numericCoefficient row.coefficient then wordExpression row.word else rowExpression row

theorem wordExpression_value {k : ℕ} (word : List (ArenaExpression k)) (x : Phase) :
    arenaEvaluate (wordExpression word) x=orderedProduct (word.map arenaEvaluate) x := by
  cases word with
  | nil=>simp [wordExpression,arenaEvaluate_literal,orderedProduct]
  | cons e word=>simp [wordExpression,arenaEvaluate_row,polynomialCoefficient_source,
      polynomialSymbol,orderedProduct,List.foldr_map]

theorem rowExpression_value {k : ℕ} (row : Row k) (x : Phase) :
    arenaEvaluate (rowExpression row) x=rowValue row x := by
  simp only [rowExpression,arenaEvaluate_row,rowValue,orderedProduct,List.foldr_map]

theorem numericCoefficient_value (c : NormalizedCoefficient) (h : numericCoefficient c) (x : Phase) :
    coefficientValue c x=((MvPolynomial.constantCoeff c.numerator : ℚ) : ℝ) := by
  unfold coefficientValue
  rw [h.1,h.2]
  simp [sourceDenominator,evalAt]

theorem row_split {k : ℕ} (row : Row k) :
    arenaEvaluate (rowExpression row)=(fun x=>(rowNumber row : ℂ)*arenaEvaluate (rowOperand row) x) := by
  classical
  funext x
  by_cases h : numericCoefficient row.coefficient
  · rw [rowExpression_value]
    simp only [rowNumber,rowOperand,if_pos h,wordExpression_value,rowValue,numericCoefficient_value _ h]
  · simp only [rowNumber,rowOperand,if_neg h,Complex.ofReal_one,one_mul]

-- No ID order is invented here: the source cache's orientation can consume the
-- signed scalar-N0 swap law independently of the actual row splitting below.
def pairCore {k : ℕ} (r : ℕ) (left right : ArenaExpression k) : ArenaExpression k := by
  classical
  exact if r=0 then arenaProduct left right else
    if left=.literal 1 ∨ right=.literal 1 then .literal 0 else
    if Odd r ∧ left=right then .literal 0 else .moyal r left right

theorem pairCore_source {k : ℕ} (r : ℕ) (left right : ArenaExpression k) (x : Phase) :
    arenaEvaluate (pairCore r left right) x=arenaEvaluate (.moyal r left right) x := by
  classical
  unfold pairCore
  split_ifs with zero identity diagonal
  · subst r;exact (arena_moyal_zero left right x).symm
  · obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero zero
    rcases identity with h|h
    · subst left;exact (arena_moyal_constant_left n 1 right x).symm
    · subst right;exact (arena_moyal_constant_right n 1 left x).symm
  · rcases diagonal with ⟨⟨n,hn⟩,same⟩
    subst right
    have hr : r=2*n+1 := by omega
    rw [hr]
    exact (arena_moyal_odd_self n left x).symm
  · rfl

def rowPair {k : ℕ} (r : ℕ) (left right : Row k) : ArenaExpression k :=
  arenaProduct (.literal (rowNumber left*rowNumber right))
    (pairCore r (rowOperand left) (rowOperand right))

theorem rowPair_source {k : ℕ} (r : ℕ) (left right : Row k)
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (rowPair r left right) x=
      complexMoyal r (arenaEvaluate (rowExpression left)) (arenaEvaluate (rowExpression right)) x := by
  rw [row_split left,row_split right,
    moyal_scale_left r _ _ _ (arena_smooth (rowOperand left))
      (contDiffOn_const.mul (arena_smooth (rowOperand right))) x hx,
    moyal_scale_right r _ _ _ (arena_smooth (rowOperand left)) (arena_smooth (rowOperand right)) x hx]
  rw [rowPair,arenaProduct_evaluate,pairCore_source]
  simp only [arenaEvaluate_literal,arenaEvaluate_moyal,Complex.ofReal_mul,mul_assoc]

theorem rowPair_swap {k : ℕ} (r : ℕ) (left right : Row k)
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (rowPair r right left) x=(-1:ℂ)^r*arenaEvaluate (rowPair r left right) x := by
  rw [rowPair_source r right left x hx,rowPair_source r left right x hx]
  exact complexMoyal_swap r _ _ x

theorem rowOperand_keeps_fields {k : ℕ} (row : Row k)
    (nonconstant : ¬numericCoefficient row.coefficient) : rowOperand row=rowExpression row := by
  classical
  simp only [rowOperand,if_neg nonconstant]

def rightExpansion {k : ℕ} (r : ℕ) (left : Row k) (right : List (Row k)) : ArenaExpression k :=
  right.foldr (fun row out=>.add (rowPair r left row) out) (.literal 0)

def pairExpansion {k : ℕ} (r : ℕ) (left right : List (Row k)) : ArenaExpression k :=
  left.foldr (fun row out=>.add (rightExpansion r row right) out) (.literal 0)

theorem rightExpansion_source {k : ℕ} (r : ℕ) (left : Row k) (right : List (Row k))
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (rightExpansion r left right) x=
      complexMoyal r (arenaEvaluate (rowExpression left)) (arenaEvaluate (rowsExpression right)) x := by
  induction right with
  | nil=>simp only [rightExpansion,rowsExpression,List.foldr_nil,arenaEvaluate_literal,Complex.ofReal_zero,moyal_zero_right]
  | cons row rest ih=>
    simp only [rightExpansion,rowsExpression,List.foldr_cons,arenaEvaluate_add]
    change arenaEvaluate (rowPair r left row) x+arenaEvaluate (rightExpansion r left rest) x=_
    rw [rowPair_source r left row x hx,ih]
    exact (moyal_add_right r _ _ _ (arena_smooth _) (arena_smooth _) (arena_smooth _) x hx).symm

theorem pairExpansion_source {k : ℕ} (r : ℕ) (left right : List (Row k))
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (pairExpansion r left right) x=
      complexMoyal r (arenaEvaluate (rowsExpression left)) (arenaEvaluate (rowsExpression right)) x := by
  induction left with
  | nil=>simp only [pairExpansion,rowsExpression,List.foldr_nil,arenaEvaluate_literal,Complex.ofReal_zero,moyal_zero_left]
  | cons row rest ih=>
    simp only [pairExpansion,rowsExpression,List.foldr_cons,arenaEvaluate_add]
    change arenaEvaluate (rightExpansion r row right) x+arenaEvaluate (pairExpansion r rest right) x=_
    rw [rightExpansion_source r row right x hx,ih]
    exact (moyal_add_left r _ _ _ (arena_smooth _) (arena_smooth _) (arena_smooth _) x hx).symm

def moyalRows {k : ℕ} (r : ℕ) (left right : List (Row k)) : ArenaExpression k :=
  if r=0 then rowsExpression (multiplyRows left right) else pairExpansion r left right

theorem moyalRows_source {k : ℕ} (r : ℕ) (left right : List (Row k))
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (moyalRows r left right) x=
      complexMoyal r (arenaEvaluate (rowsExpression left)) (arenaEvaluate (rowsExpression right)) x := by
  unfold moyalRows
  split_ifs with h
  · subst r
    rw [complexMoyal_zero,rowsExpression_value,multiplyRows_value _ _ x hx,
      rowsExpression_value,rowsExpression_value]
  · exact pairExpansion_source r left right x hx

theorem moyal_germ (r : ℕ) (f f' g g' : Phase→ℂ) (x : Phase)
    (left : f=ᶠ[𝓝 x]f') (right : g=ᶠ[𝓝 x]g') :
    complexMoyal r f g x=complexMoyal r f' g' x := by
  have fre : (fun y=>(f y).re)=ᶠ[𝓝 x](fun y=>(f' y).re) := left.fun_comp Complex.re
  have fim : (fun y=>(f y).im)=ᶠ[𝓝 x](fun y=>(f' y).im) := left.fun_comp Complex.im
  have gre : (fun y=>(g y).re)=ᶠ[𝓝 x](fun y=>(g' y).re) := right.fun_comp Complex.re
  have gim : (fun y=>(g y).im)=ᶠ[𝓝 x](fun y=>(g' y).im) := right.fun_comp Complex.im
  have coeff (a a' b b' : Phase→ℝ) (ha : a=ᶠ[𝓝 x]a') (hb : b=ᶠ[𝓝 x]b') :
      coefficient r a b x=coefficient r a' b' x := by
    unfold coefficient contraction jet
    rw [(ha.iteratedFDeriv ℝ r).eq_of_nhds,(hb.iteratedFDeriv ℝ r).eq_of_nhds]
  simp only [complexMoyal,coeff _ _ _ _ fre gre,coeff _ _ _ _ fim gim,
    coeff _ _ _ _ fre gim,coeff _ _ _ _ fim gre]

def sourceMoyal {k : ℕ} (r : ℕ) (left right : ArenaExpression k) : ArenaExpression k :=
  moyalRows r (sourceRows left) (sourceRows right)

theorem sourceMoyal_source {k : ℕ} (r : ℕ) (left right : ArenaExpression k)
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (sourceMoyal r left right) x=arenaEvaluate (.moyal r left right) x := by
  rw [sourceMoyal,moyalRows_source r _ _ x hx,arenaEvaluate_moyal]
  apply moyal_germ
  · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact normalizedExpression_source left y hy
  · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact normalizedExpression_source right y hy


def normalizeMoyal {k : ℕ} (e : ArenaExpression k) : ArenaExpression k :=
  ArenaExpression.rec (motive_1:=fun _=>ArenaExpression k) (motive_2:=fun _=>List (ArenaExpression k))
    .literal .source .clock (fun r _ _ left right=>sourceMoyal r left right)
    (fun c _ word=>.row c word) (fun _ _ left right=>.add left right)
    [] (fun _ _ head tail=>head::tail) e

@[simp] theorem normalize_literal {k : ℕ} (c : ℝ) : normalizeMoyal (.literal c:ArenaExpression k)=.literal c := rfl
@[simp] theorem normalize_source {k : ℕ} (d : Fin 3) (j : Fin 14) : normalizeMoyal (.source d j:ArenaExpression k)=.source d j := rfl
@[simp] theorem normalize_clock {k : ℕ} (l : Fin (k+1)) (a : Fin 4) : normalizeMoyal (.clock l a:ArenaExpression k)=.clock l a := rfl
@[simp] theorem normalize_moyal {k : ℕ} (r : ℕ) (e f : ArenaExpression k) :
    normalizeMoyal (.moyal r e f)=sourceMoyal r (normalizeMoyal e) (normalizeMoyal f) := rfl
@[simp] theorem normalize_add {k : ℕ} (e f : ArenaExpression k) :
    normalizeMoyal (.add e f)=.add (normalizeMoyal e) (normalizeMoyal f) := rfl

theorem normalize_row {k : ℕ} (c : NormalizedCoefficient) (word : List (ArenaExpression k)) :
    normalizeMoyal (.row c word)=.row c (word.map normalizeMoyal) := by
  suffices same : ArenaExpression.rec_1
      (motive_1:=fun _=>ArenaExpression k) (motive_2:=fun _=>List (ArenaExpression k))
      .literal .source .clock (fun r _ _ left right=>sourceMoyal r left right)
      (fun c _ word=>.row c word) (fun _ _ left right=>.add left right)
      [] (fun _ _ head tail=>head::tail) word=word.map normalizeMoyal by
    exact congrArg (ArenaExpression.row c) same
  induction word with
  | nil=>rfl
  | cons e rest ih=>change normalizeMoyal e::_=normalizeMoyal e::rest.map normalizeMoyal;rw [ih]

theorem normalizeMoyal_source {k : ℕ} (e : ArenaExpression k) :
    ∀ x∈poleDomain,arenaEvaluate (normalizeMoyal e) x=arenaEvaluate e x := by
  refine ArenaExpression.rec
    (motive_1:=fun e=>∀ x∈poleDomain,arenaEvaluate (normalizeMoyal e) x=arenaEvaluate e x)
    (motive_2:=fun word=>∀ x∈poleDomain,
      orderedProduct ((word.map normalizeMoyal).map arenaEvaluate) x=orderedProduct (word.map arenaEvaluate) x)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro c x _;rfl
  · intro d j x _;rfl
  · intro l a x _;rfl
  · intro r e f he hf x hx
    rw [normalize_moyal,sourceMoyal_source r _ _ x hx]
    simp only [arenaEvaluate_moyal]
    apply moyal_germ
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      exact he y hy
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      exact hf y hy
  · intro c word ih x hx
    rw [normalize_row,arenaEvaluate_row,arenaEvaluate_row]
    have same:=ih x hx
    simp only [orderedProduct,List.foldr_map] at same
    simp only [List.foldr_map]
    rw [same]
  · intro e f he hf x hx
    simp only [normalize_add,arenaEvaluate_add,he x hx,hf x hx]
  · intro x _;rfl
  · intro e word he ih x hx
    simp only [List.map_cons,orderedProduct,List.foldr_cons]
    have same:=ih x hx
    simp only [orderedProduct] at same
    rw [he x hx,same]

def moyalNormalizedEnergy (k : ℕ) : ArenaExpression 0 :=
  normalizedExpression (normalizeMoyal (arena_energy_expr k))

theorem moyalNormalizedEnergy_source (k : ℕ) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (moyalNormalizedEnergy k) x=(PreparationVacuumEngineSource.sourceEngineEnergy k x:ℂ) := by
  rw [moyalNormalizedEnergy,normalizedExpression_source _ x hx,normalizeMoyal_source _ x hx]
  exact arena_energy_readback k x hx

theorem moyalNormalizedEnergy_jets (k m : ℕ) (x : Phase) (hx : x∈poleDomain) :
    iteratedFDeriv ℝ m (arenaEvaluate (moyalNormalizedEnergy k)) x=
      iteratedFDeriv ℝ m (fun y=>(PreparationVacuumEngineSource.sourceEngineEnergy k y:ℂ)) x := by
  have germ : arenaEvaluate (moyalNormalizedEnergy k)=ᶠ[𝓝 x]
      (fun y=>(PreparationVacuumEngineSource.sourceEngineEnergy k y:ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact moyalNormalizedEnergy_source k y hy
  exact (germ.iteratedFDeriv ℝ m).eq_of_nhds

end LowEnergy.PreparationVacuumMoyalNormalization
