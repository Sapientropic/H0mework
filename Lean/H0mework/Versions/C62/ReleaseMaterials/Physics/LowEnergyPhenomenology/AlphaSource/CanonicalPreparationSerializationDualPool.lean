import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSerializationClockProgram

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceSerialization
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumArenaCollect
open PreparationVacuumLiteralRows PreparationVacuumSourceCacheRules PreparationVacuumSourceCacheProgram
open PreparationVacuumArenaRows PreparationVacuumCanonicalMoyal PreparationVacuumClockSymbol
open PreparationVacuumEngineSource PreparationVacuumMoyalNormalization
open scoped BigOperators Topology Pointwise
variable {K : ℕ}

-- Python has distinct node and polynomial intern pools. Their ranks serve
-- different sorting operations and therefore are never conflated here.
structure ArenaStore (K : ℕ) where
  nodes : List (ArenaExpression K) := []
  polynomials : List (List (Row K)) := []

def intern {α : Type} (a : α) (pool : List α) : List α := by
  classical
  exact if a∈pool then pool else pool++[a]

theorem intern_member {α : Type} (a : α) (pool : List α) : a∈intern a pool := by
  classical
  simp only [intern]
  split_ifs with h
  · exact h
  · exact List.mem_append_right _ (List.mem_singleton_self _)

theorem intern_preserves {α : Type} (a b : α) (pool : List α) (h : a∈pool) : a∈intern b pool := by
  classical
  simp only [intern]
  split_ifs
  · exact h
  · exact List.mem_append_left _ h

def central (e : ArenaExpression K) : Bool :=
  ArenaExpression.rec (motive_1:=fun _=>Bool) (motive_2:=fun _=>Bool)
    (fun _=>true) (fun _ _=>false) (fun _ _=>false)
    (fun _ _ _ left right=>left && right) (fun _ _ word=>word)
    (fun _ _ left right=>left && right) true (fun _ _ head tail=>head && tail) e

def nodeLabels (state : ArenaStore K) : CacheLabels K := by
  classical
  exact fun e=>(state.nodes.idxOf e,central e)

def polynomialLabels (state : ArenaStore K) : CacheLabels K := by
  classical
  exact fun e=>(state.polynomials.idxOf (rationalRows (nodeLabels state) e),central e)

def registerRows (rows : List (Row K)) (state : ArenaStore K) : ArenaStore K :=
  { nodes := (rows.flatMap Row.word).foldl (fun pool e=>intern e pool) state.nodes
    polynomials := intern rows state.polynomials }

abbrev Action (K : ℕ) := ArenaStore K → ArenaExpression K × ArenaStore K

def normalize (e : ArenaExpression K) : Action K := fun state=>
  let rows:=rationalRows (nodeLabels state) e
  (rowsExpression rows,registerRows rows state)

theorem normalize_source (e : ArenaExpression K) (state : ArenaStore K)
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (normalize e state).1 x=arenaEvaluate e x := by
  exact rationalExpression_source (nodeLabels state) e x hx

theorem normalize_allocated (e : ArenaExpression K) (state : ArenaStore K) :
    rationalRows (nodeLabels state) e∈(normalize e state).2.polynomials :=
  intern_member _ _

def returnExpression (e : ArenaExpression K) : Action K := normalize e

def unary (op : ArenaExpression K → ArenaExpression K) (input : Action K) : Action K := fun state=>
  let (e,next):=input state
  normalize (op e) next

def binary (op : ArenaExpression K → ArenaExpression K → ArenaExpression K)
    (left right : Action K) : Action K := fun state=>
  let (a,one):=left state
  let (b,two):=right one
  normalize (op a b) two

def addAction (left right : Action K) : Action K := binary ArenaExpression.add left right

def listSum {ι : Type} (items : List ι) (action : ι → Action K) : Action K :=
  items.foldr (fun i result=>addAction (action i) result) (returnExpression (.literal 0))

def finiteSum {ι : Type} (items : Finset ι) (action : ι → Action K) : Action K :=
  listSum items.toList action

-- One original row pair first interns the possibly constant-stripped operands,
-- then uses polynomial ranks for the Moyal orientation decision.
def rowPair (r : ℕ) (left right : Row K) : Action K := fun state=>
  let one:=registerRows (rationalRows (nodeLabels state) (rowOperand left)) state
  let two:=registerRows (rationalRows (nodeLabels one) (rowOperand right)) one
  normalize (originalRowPair (polynomialLabels two) r left right) two

theorem rowPair_source (r : ℕ) (left right : Row K) (state : ArenaStore K)
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (rowPair r left right state).1 x=
      complexMoyal r (arenaEvaluate (rowExpression left)) (arenaEvaluate (rowExpression right)) x := by
  unfold rowPair
  rw [normalize_source _ _ x hx,originalRowPair_source _ _ _ _ x hx]

-- The r=0 branch is multiply; positive orders split all row pairs and preserve
-- every variable central factor inside its operand before differentiation.
def moyalAction (r : ℕ) (left right : Action K) : Action K := fun state=>
  let (a,one):=left state
  let (b,two):=right one
  if r=0 then normalize (arenaProduct a b) two else
    listSum (rationalRows (nodeLabels two) a) (fun row=>
      listSum (rationalRows (nodeLabels two) b) (rowPair r row)) two

def jordanAction (r : ℕ) (left right : Action K) : Action K :=
  unary (arenaProduct (.literal (1/2)))
    (addAction (moyalAction r left right) (moyalAction r right left))


def RunsTo (action : Action K) (value : Phase → ℂ) : Prop :=
  ∀ state x,x∈poleDomain → arenaEvaluate (action state).1 x=value x

theorem returnExpression_source (e : ArenaExpression K) : RunsTo (returnExpression e) (arenaEvaluate e) :=
  normalize_source e

theorem addAction_source (left right : Action K) (f g : Phase → ℂ)
    (hl : RunsTo left f) (hr : RunsTo right g) : RunsTo (addAction left right) (fun x=>f x+g x) := by
  intro state x hx
  change arenaEvaluate (normalize (.add (left state).1 (right (left state).2).1)
    (right (left state).2).2).1 x=_
  rw [normalize_source _ _ x hx,arenaEvaluate_add]
  dsimp only
  rw [hl _ x hx,hr _ x hx]

theorem unary_source (op : ArenaExpression K → ArenaExpression K) (input : Action K)
    (target : Phase → ℂ)
    (read : ∀ state x,x∈poleDomain → arenaEvaluate (op (input state).1) x=target x) :
    RunsTo (unary op input) target := by
  intro state x hx
  rw [unary,normalize_source _ _ x hx]
  exact read state x hx

theorem listSum_source {ι : Type} (items : List ι) (actions : ι → Action K) (values : ι → Phase → ℂ)
    (read : ∀ i,RunsTo (actions i) (values i)) :
    RunsTo (listSum items actions) (fun x=>(items.map (fun i=>values i x)).sum) := by
  induction items with
  | nil=>
    intro state x hx
    exact normalize_source (.literal 0) state x hx
  | cons i items ih=>
    exact addAction_source (actions i) (listSum items actions) (values i)
      (fun x=>(items.map (fun j=>values j x)).sum) (read i) ih

theorem finiteSum_source {ι : Type} (items : Finset ι) (actions : ι → Action K) (values : ι → Phase → ℂ)
    (read : ∀ i,RunsTo (actions i) (values i)) :
    RunsTo (finiteSum items actions) (fun x=>∑ i∈items,values i x) := by
  intro state x hx
  rw [finiteSum,listSum_source items.toList actions values read state x hx]
  exact Finset.sum_map_toList _ _

private theorem originalRightExpansion_sum (labels : CacheLabels K) (r : ℕ) (left : Row K)
    (right : List (Row K)) (x : Phase) :
    arenaEvaluate (originalRightExpansion labels r left right) x=
      (right.map (fun row=>arenaEvaluate (originalRowPair labels r left row) x)).sum := by
  induction right with
  | nil=>rfl
  | cons row right ih=>
    change arenaEvaluate (originalRowPair labels r left row) x+
      arenaEvaluate (originalRightExpansion labels r left right) x=_
    rw [ih];rfl

private theorem originalPairExpansion_sum (labels : CacheLabels K) (r : ℕ)
    (left right : List (Row K)) (x : Phase) :
    arenaEvaluate (originalPairExpansion labels r left right) x=
      (left.map (fun row=>arenaEvaluate (originalRightExpansion labels r row right) x)).sum := by
  induction left with
  | nil=>rfl
  | cons row left ih=>
    change arenaEvaluate (originalRightExpansion labels r row right) x+
      arenaEvaluate (originalPairExpansion labels r left right) x=_
    rw [ih];rfl

theorem pairExpansion_source (r : ℕ) (left right : List (Row K)) :
    RunsTo (listSum left (fun row=>listSum right (rowPair r row)))
      (complexMoyal r (arenaEvaluate (rowsExpression left)) (arenaEvaluate (rowsExpression right))) := by
  let labels : CacheLabels K:=fun e=>(0,central e)
  have each (row : Row K) : RunsTo (listSum right (rowPair r row))
      (arenaEvaluate (originalRightExpansion labels r row right)) := by
    intro state x hx
    rw [listSum_source right (rowPair r row)
      (fun other=>complexMoyal r (arenaEvaluate (rowExpression row)) (arenaEvaluate (rowExpression other)))
      (fun other=>rowPair_source r row other) state x hx,originalRightExpansion_sum]
    dsimp only
    congr 1
    apply List.map_congr_left
    intro other _
    exact (originalRowPair_source labels r row other x hx).symm
  intro state x hx
  rw [listSum_source left _ _ each state x hx]
  dsimp only
  rw [←originalPairExpansion_sum,originalPairExpansion_source _ _ _ _ x hx]

theorem moyalAction_source (r : ℕ) (left right : Action K) (f g : Phase → ℂ)
    (hl : RunsTo left f) (hr : RunsTo right g) :
    RunsTo (moyalAction r left right) (complexMoyal r f g) := by
  intro state x hx
  unfold moyalAction
  split_ifs with zero
  · subst r
    rw [normalize_source _ _ x hx,arenaProduct_evaluate,complexMoyal_zero,hl _ x hx,hr _ x hx]
  · rw [pairExpansion_source _ _ _ _ x hx]
    apply PreparationVacuumMoyalNormalization.moyal_germ
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      rw [rowsExpression_value,rationalRows_source _ _ y hy,hl _ y hy]
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      rw [rowsExpression_value,rationalRows_source _ _ y hy,hr _ y hy]


theorem productAction_source (left right : Action K) (f g : Phase → ℂ)
    (hl : RunsTo left f) (hr : RunsTo right g) :
    RunsTo (binary arenaProduct left right) (fun x=>f x*g x) := by
  intro state x hx
  change arenaEvaluate (normalize (arenaProduct (left state).1 (right (left state).2).1)
    (right (left state).2).2).1 x=_
  rw [normalize_source _ _ x hx,arenaProduct_evaluate,hl _ x hx,hr _ x hx]

theorem negateAction_source (input : Action K) (f : Phase → ℂ) (h : RunsTo input f) :
    RunsTo (unary arenaNegate input) (fun x=>-f x) := by
  intro state x hx
  rw [unary,normalize_source _ _ x hx,arenaNegate_evaluate,h _ x hx]

theorem jordanAction_source (r : ℕ) (left right : Action K) (f g : Symbol)
    (hl : RunsTo left (fun x=>(f x : ℂ))) (hr : RunsTo right (fun x=>(g x : ℂ))) :
    RunsTo (jordanAction r left right) (fun x=>(scalarJordan r f g x : ℂ)) := by
  have sumRead:=addAction_source _ _ _ _ (moyalAction_source r left right _ _ hl hr)
    (moyalAction_source r right left _ _ hr hl)
  intro state x hx
  rw [jordanAction,unary,normalize_source _ _ x hx,arenaProduct_evaluate,arenaEvaluate_literal,sumRead _ x hx]
  dsimp only
  rw [complexMoyal_real,complexMoyal_real,scalarJordan_native]
  simp only [PreparationVacuumCanonicalMoyal.jordan,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

def primitiveExpression (p : Primitive K) : ArenaExpression K :=
  match p with
  | .base (.literal c)=>.literal c
  | .base (.principal j)=>.row (principalCoefficient j) []
  | .base (.leaf d j)=>.source d j
  | .base .clock=>.row (polynomialCoefficient (MvPolynomial.X 0)) []
  | .base .inverseClock=>.row (inversePoleCoefficient 0) []
  | .base (.inverseJacobian a b)=>.row (inverseCoefficient a b) []
  | .clockReference level axis=>.clock (Fin.succ level) axis

theorem primitiveExpression_source (p : Primitive K) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (primitiveExpression p) x=(primitiveValue p x : ℂ) := by
  cases p with
  | clockReference level axis=>exact arena_clock_readback K (Fin.succ level) axis x
  | base p=>
    cases p with
    | literal c=>rfl
    | principal j=>exact arena_row_principal K j x
    | leaf d j=>rfl
    | clock=>
      rw [primitiveExpression,arena_row_empty,polynomialCoefficient_source]
      simp [polynomialSymbol,evalAt,sourceVariables,primitiveValue,
        PreparationVacuumDAGSemantic.primitiveValue,PreparationVacuumClockJacobian.actualC,sourceClock]
    | inverseClock=>rw [primitiveExpression,arena_row_empty,inverseClockCoefficient_native];rfl
    | inverseJacobian a b=>exact arena_row_inverse K a b x hx

def angularSupport {s : ExprSort} (e : Expression K s) : Finset AngularExponent :=
  Expression.rec (motive:=fun _ _=>Finset AngularExponent)
    (fun _=>∅) (fun _ _ _ _=>∅) (fun _ _=>∅) (fun _ _ _ _=>∅)
    (fun _ _=>∅) (fun _ _ _=>∅) (fun _ _=>∅)
    ∅ (fun u _ _=>{u}) (fun _ _ a b=>a∪b) (fun _ a=>a)
    (fun _ _ a b=>a+b) (fun _ values=>Finset.univ.biUnion values)
    (fun _ _ _ a b=>a+b) e

def Covered {K : ℕ} : (s : ExprSort) → Expression K s → Prop
  | .symbol,_=>True
  | .polynomial,e=>(evaluate e).support⊆angularSupport e

theorem angularSupport_covers {s : ExprSort} (e : Expression K s) : Covered s e := by
  induction e with
  | primitive _=>trivial
  | addS _ _ _ _=>trivial
  | negS _ _=>trivial
  | mulS _ _ _ _=>trivial
  | sumS _ _=>trivial
  | coefficient _ _ _=>trivial
  | average _ _=>trivial
  | zeroP=>exact Finset.empty_subset _
  | monomial _ _ _=>exact MvPolynomial.support_monomial_subset
  | addP e f he hf=>
    exact (MvPolynomial.support_add).trans (Finset.union_subset_union he hf)
  | negP e he=>simpa only [Covered,evaluate,angularSupport,MvPolynomial.support_neg] using he
  | mulP e f he hf=>
    intro u hu
    obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (MvPolynomial.support_mul (evaluate e) (evaluate f) hu)
    exact Finset.mem_add.mpr ⟨a,he ha,b,hf hb,rfl⟩
  | sumP terms ih=>
    intro u hu
    obtain ⟨i,hi,h⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hu)
    exact Finset.mem_biUnion.mpr ⟨i,hi,ih i h⟩
  | weighted r e f he hf=>
    intro u hu
    obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (PreparationVacuumOriginalEmitter.weighted_support_subset r (evaluate e) (evaluate f) hu)
    exact Finset.mem_add.mpr ⟨a,he ha,b,hf hb,rfl⟩



def CompiledAction (K : ℕ) : ExprSort → Type
  | .symbol=>Action K
  | .polynomial=>AngularExponent → Action K

def compileAction {s : ExprSort} (e : Expression K s) : CompiledAction K s :=
  Expression.rec (motive:=fun s _=>CompiledAction K s)
    (fun p=>returnExpression (primitiveExpression p))
    (fun _ _ left right=>addAction left right)
    (fun _ input=>unary arenaNegate input)
    (fun _ _ left right=>binary arenaProduct left right)
    (fun _ terms=>finiteSum Finset.univ terms)
    (fun u _ terms=>terms u)
    (fun e terms=>finiteSum (angularSupport e) (fun u=>binary arenaProduct
      (returnExpression (.literal (angularMoment u))) (terms u)))
    (fun _=>returnExpression (.literal 0))
    (fun u _ term v=>if u=v then term else returnExpression (.literal 0))
    (fun _ _ left right u=>addAction (left u) (right u))
    (fun _ input u=>unary arenaNegate (input u))
    (fun e f left right u=>finiteSum (angularSupport e) (fun a=>
      finiteSum (angularSupport f) (fun b=>if a+b=u then binary arenaProduct (left a) (right b)
        else returnExpression (.literal 0))))
    (fun _ terms u=>finiteSum Finset.univ (fun i=>terms i u))
    (fun r e f left right u=>finiteSum (angularSupport e) (fun a=>
      finiteSum (angularSupport f) (fun b=>if a+b=u then jordanAction r (left a) (right b)
        else returnExpression (.literal 0)))) e

def Compiles {K : ℕ} : (s : ExprSort) → CompiledAction K s → Value s → Prop
  | .symbol,action,f=>RunsTo action (fun x=>(f x : ℂ))
  | .polynomial,action,P=>∀ u,RunsTo (action u) (fun x=>(MvPolynomial.coeff u P x : ℂ))



theorem constantAction_source (c : ℝ) :
    RunsTo (returnExpression (.literal c : ArenaExpression K)) (fun _=>(c : ℂ)) :=
  returnExpression_source _

theorem addAction_real (left right : Action K) (f g : Symbol)
    (hl : RunsTo left (fun x=>(f x : ℂ))) (hr : RunsTo right (fun x=>(g x : ℂ))) :
    RunsTo (addAction left right) (fun x=>((f+g) x : ℂ)) := by
  simpa only [Pi.add_apply,Complex.ofReal_add] using addAction_source left right _ _ hl hr

theorem productAction_real (left right : Action K) (f g : Symbol)
    (hl : RunsTo left (fun x=>(f x : ℂ))) (hr : RunsTo right (fun x=>(g x : ℂ))) :
    RunsTo (binary arenaProduct left right) (fun x=>((f*g) x : ℂ)) := by
  simpa only [Pi.mul_apply,Complex.ofReal_mul] using productAction_source left right _ _ hl hr

theorem negateAction_real (input : Action K) (f : Symbol) (h : RunsTo input (fun x=>(f x : ℂ))) :
    RunsTo (unary arenaNegate input) (fun x=>((-f) x : ℂ)) := by
  simpa only [Pi.neg_apply,Complex.ofReal_neg] using negateAction_source input _ h

theorem finiteSum_real {ι : Type} (items : Finset ι) (actions : ι → Action K) (values : ι → Symbol)
    (read : ∀ i,RunsTo (actions i) (fun x=>(values i x : ℂ))) :
    RunsTo (finiteSum items actions) (fun x=>((∑ i∈items,values i) x : ℂ)) := by
  simpa only [Finset.sum_apply,Complex.ofReal_sum] using finiteSum_source items actions _ read

theorem compileAction_source {s : ExprSort} (e : Expression K s) : Compiles s (compileAction e) (evaluate e) := by
  induction e with
  | primitive p=>
    intro state x hx
    rw [show compileAction (.primitive p)=returnExpression (primitiveExpression p) from rfl]
    exact (normalize_source _ state x hx).trans (primitiveExpression_source p x hx)
  | addS e f he hf=>exact addAction_real _ _ _ _ he hf
  | negS e he=>exact negateAction_real _ _ he
  | mulS e f he hf=>exact productAction_real _ _ _ _ he hf
  | sumS terms ih=>
    simpa only [Compiles,compileAction,evaluate] using finiteSum_real (Finset.univ) _ (fun i=>evaluate (terms i)) ih
  | coefficient u e he=>exact he u
  | average e he=>
    have read:=finiteSum_real (angularSupport e)
      (fun u=>binary arenaProduct (returnExpression (.literal (angularMoment u))) (compileAction e u))
      (fun u=> (fun _=>angularMoment u)*MvPolynomial.coeff u (evaluate e))
      (fun u=>productAction_real _ _ _ _ (constantAction_source _) (he u))
    intro state x hx
    rw [show compileAction (.average e)=finiteSum (angularSupport e)
      (fun u=>binary arenaProduct (returnExpression (.literal (angularMoment u))) (compileAction e u)) from rfl]
    rw [read state x hx]
    change _=(average (evaluate e) x : ℂ)
    rw [PreparationVacuumOriginalEmitter.average_over_cover _ _ (angularSupport_covers e)]
    rfl
  | zeroP=>intro u;exact constantAction_source 0
  | monomial u e he=>
    intro v
    by_cases same : u=v
    · subst v
      simpa only [Compiles,compileAction,ite_true,evaluate,MvPolynomial.coeff_monomial] using he
    · simpa only [Compiles,compileAction,same,ite_false,evaluate,MvPolynomial.coeff_monomial,Pi.zero_apply]
        using (constantAction_source (K:=K) 0)
  | addP e f he hf=>
    intro u
    simpa only [compileAction,evaluate,MvPolynomial.coeff_add] using addAction_real _ _ _ _ (he u) (hf u)
  | negP e he=>
    intro u
    simpa only [compileAction,evaluate,MvPolynomial.coeff_neg] using negateAction_real _ _ (he u)
  | mulP e f he hf=>
    intro u
    have pair (a b : AngularExponent) : RunsTo
        (if a+b=u then binary arenaProduct (compileAction e a) (compileAction f b) else returnExpression (.literal 0))
        (fun x=>((if a+b=u then MvPolynomial.coeff a (evaluate e)*MvPolynomial.coeff b (evaluate f) else 0) x : ℂ)) := by
      split_ifs
      · exact productAction_real _ _ _ _ (he a) (hf b)
      · exact constantAction_source 0
    have read:=finiteSum_real (angularSupport e) _ _ (fun a=>finiteSum_real (angularSupport f) _ _ (pair a))
    intro state x hx
    rw [show compileAction (.mulP e f) u=finiteSum (angularSupport e) (fun a=>
      finiteSum (angularSupport f) (fun b=>if a+b=u then binary arenaProduct (compileAction e a) (compileAction f b)
        else returnExpression (.literal 0))) from rfl]
    rw [read state x hx]
    change _=(MvPolynomial.coeff u (evaluate e*evaluate f) x : ℂ)
    rw [PreparationVacuumOriginalEmitter.coefficient_product_cover _ _ _ _ (angularSupport_covers e) (angularSupport_covers f)]
  | sumP terms ih=>
    intro u
    simpa only [compileAction,evaluate,MvPolynomial.coeff_sum] using
      finiteSum_real Finset.univ (fun i=>compileAction (terms i) u) (fun i=>MvPolynomial.coeff u (evaluate (terms i))) (fun i=>ih i u)
  | weighted r e f he hf=>
    intro u
    have pair (a b : AngularExponent) : RunsTo
        (if a+b=u then jordanAction r (compileAction e a) (compileAction f b) else returnExpression (.literal 0))
        (fun x=>((if a+b=u then scalarJordan r (MvPolynomial.coeff a (evaluate e)) (MvPolynomial.coeff b (evaluate f)) else 0) x : ℂ)) := by
      split_ifs
      · exact jordanAction_source r _ _ _ _ (he a) (hf b)
      · exact constantAction_source 0
    have read:=finiteSum_real (angularSupport e) _ _ (fun a=>finiteSum_real (angularSupport f) _ _ (pair a))
    intro state x hx
    rw [show compileAction (.weighted r e f) u=finiteSum (angularSupport e) (fun a=>
      finiteSum (angularSupport f) (fun b=>if a+b=u then jordanAction r (compileAction e a) (compileAction f b)
        else returnExpression (.literal 0))) from rfl]
    rw [read state x hx]
    change _=(MvPolynomial.coeff u (weighted r (evaluate e) (evaluate f)) x : ℂ)
    rw [PreparationVacuumOriginalEmitter.coefficient_weighted_cover _ _ _ _ _ (angularSupport_covers e) (angularSupport_covers f)]


def Allocated (action : Action K) : Prop :=
  ∀ state,(action state).1∈(action state).2.polynomials.map rowsExpression

theorem normalize_allocated_expression (e : ArenaExpression K) : Allocated (normalize e) := by
  intro state
  exact List.mem_map.mpr ⟨_,normalize_allocated e state,rfl⟩

theorem unary_allocated (op : ArenaExpression K → ArenaExpression K) (input : Action K) :
    Allocated (unary op input) := by
  intro state
  exact normalize_allocated_expression _ _

theorem binary_allocated (op : ArenaExpression K → ArenaExpression K → ArenaExpression K)
    (left right : Action K) : Allocated (binary op left right) := by
  intro state
  exact normalize_allocated_expression _ _

theorem listSum_allocated {ι : Type} (items : List ι) (action : ι → Action K) : Allocated (listSum items action) := by
  cases items with
  | nil=>exact normalize_allocated_expression _
  | cons i items=>exact binary_allocated _ _ _

theorem finiteSum_allocated {ι : Type} (items : Finset ι) (action : ι → Action K) : Allocated (finiteSum items action) :=
  listSum_allocated _ _

def CompiledAllocated {K : ℕ} : (s : ExprSort) → CompiledAction K s → Prop
  | .symbol,action=>Allocated action
  | .polynomial,action=>∀ u,Allocated (action u)

theorem compileAction_allocated {s : ExprSort} (e : Expression K s) : CompiledAllocated s (compileAction e) := by
  induction e with
  | primitive p=>exact normalize_allocated_expression _
  | addS e f he hf=>exact binary_allocated _ _ _
  | negS e he=>exact unary_allocated _ _
  | mulS e f he hf=>exact binary_allocated _ _ _
  | sumS terms ih=>exact finiteSum_allocated _ _
  | coefficient u e he=>exact he u
  | average e he=>exact finiteSum_allocated _ _
  | zeroP=>intro u;exact normalize_allocated_expression _
  | monomial u e he=>
    intro v
    change Allocated (if u=v then compileAction e else returnExpression (.literal 0))
    split_ifs
    · exact he
    · exact normalize_allocated_expression _
  | addP e f he hf=>intro u;exact binary_allocated _ _ _
  | negP e he=>intro u;exact unary_allocated _ _
  | mulP e f he hf=>intro u;exact finiteSum_allocated _ _
  | sumP terms ih=>intro u;exact finiteSum_allocated _ _
  | weighted r e f he hf=>intro u;exact finiteSum_allocated _ _

-- The two mandatory initial polynomial IDs are Arena.zero and Arena.one.
def initialStore (K : ℕ) : ArenaStore K :=
  ⟨[],[[],[⟨polynomialCoefficient 1,[]⟩]]⟩

def runSymbol (e : Expression K .symbol) : ArenaExpression K × ArenaStore K :=
  compileAction e (initialStore K)

def targetHandle (e : Expression K .symbol) : Fin (runSymbol e).2.polynomials.length := by
  classical
  let pool:=(runSymbol e).2.polynomials.map rowsExpression
  have member : (runSymbol e).1∈pool:=compileAction_allocated e (initialStore K)
  exact ⟨pool.idxOf (runSymbol e).1,by simpa only [pool,List.length_map] using List.idxOf_lt_length_of_mem member⟩

def targetRows (e : Expression K .symbol) : List (Row K) :=
  (runSymbol e).2.polynomials[(targetHandle e).val]'(targetHandle e).isLt

theorem targetRows_readback (e : Expression K .symbol) : rowsExpression (targetRows e)=(runSymbol e).1 := by
  classical
  have member:=compileAction_allocated e (initialStore K)
  have read:=List.getElem_idxOf (List.idxOf_lt_length_of_mem member)
  simpa only [runSymbol,targetRows,targetHandle,List.getElem_map] using read

theorem generated_target_native (e : Expression K .symbol) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (rowsExpression (targetRows e)) x=(evaluate e x : ℂ) := by
  rw [targetRows_readback]
  exact compileAction_source e (initialStore K) x hx

end LowEnergy.PreparationVacuumSourceSerialization
