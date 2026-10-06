import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEmitterAngularSupport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumOriginalEmitter
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumEngineSource
open PreparationVacuumCanonicalMoyal PreparationVacuumClockSymbol PreparationVacuumLiteralRows
open PreparationVacuumSourceCacheRules
open scoped BigOperators Topology

def cachedJordan (labels : CacheLabels 0) (r : ℕ) (e f : ArenaExpression 0) : ArenaExpression 0 :=
  rationalExpression labels (arenaProduct (.literal (1/2))
    (.add (rationalSourceMoyal labels r e f) (rationalSourceMoyal labels r f e)))

theorem cachedJordan_evaluate (labels : CacheLabels 0) (r : ℕ) (e f : ArenaExpression 0)
    (a b : PreparationVacuumCanonicalMoyal.Symbol) (he : Set.EqOn (arenaEvaluate e) (fun x=>(a x : ℂ)) poleDomain)
    (hf : Set.EqOn (arenaEvaluate f) (fun x=>(b x : ℂ)) poleDomain) (x : PreparationVacuumCanonicalMoyal.Phase) (hx : x∈poleDomain) :
    arenaEvaluate (cachedJordan labels r e f) x=(scalarJordan r a b x : ℂ) := by
  rw [cachedJordan,rationalExpression_source _ _ x hx,arenaProduct_evaluate]
  simp only [arenaEvaluate_add,rationalSourceMoyal_source labels r e f x hx,
    rationalSourceMoyal_source labels r f e x hx,arenaEvaluate_literal]
  rw [←arenaJordan_evaluate r e f a b he hf x hx]
  simp only [arenaJordan,arenaProduct_evaluate,arenaEvaluate_literal,arenaEvaluate_add,arenaEvaluate_moyal]

-- Every scalar operation executes the original row/cache normalization before
-- its result is consumed. Angular keys come solely from angularSupport.
def emit (labels : CacheLabels 0) {s : ExprSort} (e : Expression s) : Compiled s :=
  Expression.rec (motive:=fun s _=>Compiled s)
    (fun p=>rationalExpression labels (compilePrimitive p))
    (fun _ _ e f=>rationalExpression labels (.add e f))
    (fun _ e=>rationalExpression labels (arenaNegate e))
    (fun _ _ e f=>rationalExpression labels (arenaProduct e f))
    (fun _ terms=>rationalExpression labels (arenaSum Finset.univ terms))
    (fun u _ p=>p u)
    (fun e compiled=>rationalExpression labels (arenaSum (angularSupport e)
      (fun u=>rationalExpression labels (arenaProduct (.literal (angularMoment u)) (compiled u)))))
    (fun _=>.literal 0)
    (fun u _ e v=>if u=v then e else .literal 0)
    (fun _ _ e f u=>rationalExpression labels (.add (e u) (f u)))
    (fun _ e u=>rationalExpression labels (arenaNegate (e u)))
    (fun e f ce cf u=>rationalExpression labels (arenaSum (angularSupport e) (fun a=>
      rationalExpression labels (arenaSum (angularSupport f) (fun b=>
        if a+b=u then rationalExpression labels (arenaProduct (ce a) (cf b)) else .literal 0)))))
    (fun _ terms u=>rationalExpression labels (arenaSum Finset.univ (fun i=>terms i u)))
    (fun r e f ce cf u=>rationalExpression labels (arenaSum (angularSupport e) (fun a=>
      rationalExpression labels (arenaSum (angularSupport f) (fun b=>
        if a+b=u then cachedJordan labels r (ce a) (cf b) else .literal 0))))) e

private theorem evaluate_primitive (p : Primitive) : evaluate (.primitive p)=(primitiveValue p) := rfl
private theorem evaluate_addS (e f : Expression .symbol) : evaluate (.addS e f)=(evaluate e+evaluate f) := rfl
private theorem evaluate_negS (e : Expression .symbol) : evaluate (.negS e)=(-evaluate e) := rfl
private theorem evaluate_mulS (e f : Expression .symbol) : evaluate (.mulS e f)=(evaluate e*evaluate f) := rfl
private theorem evaluate_sumS {n : ℕ} (terms : Fin n → Expression .symbol) : evaluate (.sumS terms)=(∑ i,evaluate (terms i)) := rfl
private theorem evaluate_coefficient (u : AngularExponent) (e : Expression .polynomial) : evaluate (.coefficient u e)=(MvPolynomial.coeff u (evaluate e)) := rfl
private theorem evaluate_average (e : Expression .polynomial) : evaluate (.average e)=(average (evaluate e)) := rfl
private theorem evaluate_zeroP  : evaluate Expression.zeroP=(0) := rfl
private theorem evaluate_monomial (u : AngularExponent) (e : Expression .symbol) : evaluate (.monomial u e)=(MvPolynomial.monomial u (evaluate e)) := rfl
private theorem evaluate_addP (e f : Expression .polynomial) : evaluate (.addP e f)=(evaluate e+evaluate f) := rfl
private theorem evaluate_negP (e : Expression .polynomial) : evaluate (.negP e)=(-evaluate e) := rfl
private theorem evaluate_mulP (e f : Expression .polynomial) : evaluate (.mulP e f)=(evaluate e*evaluate f) := rfl
private theorem evaluate_sumP {n : ℕ} (terms : Fin n → Expression .polynomial) : evaluate (.sumP terms)=(∑ i,evaluate (terms i)) := rfl
private theorem evaluate_weighted (r : ℕ) (e f : Expression .polynomial) : evaluate (.weighted r e f)=(weighted r (evaluate e) (evaluate f)) := rfl

private theorem emit_primitive (labels : CacheLabels 0) (p : Primitive) : emit labels (.primitive p)=rationalExpression labels (compilePrimitive p) := rfl
private theorem emit_addS (labels : CacheLabels 0) (e f : Expression .symbol) : emit labels (.addS e f)=rationalExpression labels (.add (emit labels e) (emit labels f)) := rfl
private theorem emit_negS (labels : CacheLabels 0) (e : Expression .symbol) : emit labels (.negS e)=rationalExpression labels (arenaNegate (emit labels e)) := rfl
private theorem emit_mulS (labels : CacheLabels 0) (e f : Expression .symbol) : emit labels (.mulS e f)=rationalExpression labels (arenaProduct (emit labels e) (emit labels f)) := rfl
private theorem emit_sumS (labels : CacheLabels 0) {n : ℕ} (terms : Fin n → Expression .symbol) : emit labels (.sumS terms)=rationalExpression labels (arenaSum Finset.univ (fun i=>emit labels (terms i))) := rfl
private theorem emit_coefficient (labels : CacheLabels 0) (u : AngularExponent) (e : Expression .polynomial) : emit labels (.coefficient u e)=emit labels e u := rfl
private theorem emit_average (labels : CacheLabels 0) (e : Expression .polynomial) : emit labels (.average e)=rationalExpression labels (arenaSum (angularSupport e) (fun u=>rationalExpression labels (arenaProduct (.literal (angularMoment u)) (emit labels e u)))) := rfl
private theorem emit_zeroP (labels : CacheLabels 0)  : emit labels Expression.zeroP=(fun _=>.literal 0) := rfl
private theorem emit_monomial (labels : CacheLabels 0) (u : AngularExponent) (e : Expression .symbol) : emit labels (.monomial u e)=(fun v=>if u=v then emit labels e else .literal 0) := rfl
private theorem emit_addP (labels : CacheLabels 0) (e f : Expression .polynomial) : emit labels (.addP e f)=(fun u=>rationalExpression labels (.add (emit labels e u) (emit labels f u))) := rfl
private theorem emit_negP (labels : CacheLabels 0) (e : Expression .polynomial) : emit labels (.negP e)=(fun u=>rationalExpression labels (arenaNegate (emit labels e u))) := rfl
private theorem emit_mulP (labels : CacheLabels 0) (e f : Expression .polynomial) : emit labels (.mulP e f)=(fun u=>rationalExpression labels (arenaSum (angularSupport e) (fun a=>rationalExpression labels (arenaSum (angularSupport f) (fun b=>if a+b=u then rationalExpression labels (arenaProduct (emit labels e a) (emit labels f b)) else .literal 0))))) := rfl
private theorem emit_sumP (labels : CacheLabels 0) {n : ℕ} (terms : Fin n → Expression .polynomial) : emit labels (.sumP terms)=(fun u=>rationalExpression labels (arenaSum Finset.univ (fun i=>emit labels (terms i) u))) := rfl
private theorem emit_weighted (labels : CacheLabels 0) (r : ℕ) (e f : Expression .polynomial) : emit labels (.weighted r e f)=(fun u=>rationalExpression labels (arenaSum (angularSupport e) (fun a=>rationalExpression labels (arenaSum (angularSupport f) (fun b=>if a+b=u then cachedJordan labels r (emit labels e a) (emit labels f b) else .literal 0))))) := rfl
theorem emit_evaluate (labels : CacheLabels 0) {s : ExprSort} (e : Expression s) : CompilesTo s (emit labels e) (evaluate e) := by
  induction e with
  | primitive p =>
    intro x hx
    rw [emit_primitive,rationalExpression_source _ _ x hx]
    exact compilePrimitive_evaluate p x hx
  | addS e f he hf =>
    intro x hx
    simp only [emit_primitive,emit_addS,emit_negS,emit_mulS,emit_sumS,emit_coefficient,emit_average,emit_zeroP,emit_monomial,emit_addP,emit_negP,emit_mulP,emit_sumP,emit_weighted,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,Pi.add_apply,Complex.ofReal_add,rationalExpression_source _ _ x hx]
    rw [he x hx,hf x hx]
  | negS e he =>
    intro x hx
    simp only [emit_primitive,emit_addS,emit_negS,emit_mulS,emit_sumS,emit_coefficient,emit_average,emit_zeroP,emit_monomial,emit_addP,emit_negP,emit_mulP,emit_sumP,emit_weighted,rationalExpression_source _ _ x hx]
    rw [arenaNegate_evaluate,he x hx]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,Pi.neg_apply,Complex.ofReal_neg,rationalExpression_source _ _ x hx]
  | mulS e f he hf =>
    intro x hx
    simp only [emit_primitive,emit_addS,emit_negS,emit_mulS,emit_sumS,emit_coefficient,emit_average,emit_zeroP,emit_monomial,emit_addP,emit_negP,emit_mulP,emit_sumP,emit_weighted,rationalExpression_source _ _ x hx]
    rw [arenaProduct_evaluate,he x hx,hf x hx]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,Pi.mul_apply,Complex.ofReal_mul,rationalExpression_source _ _ x hx]
  | sumS terms ih =>
    intro x hx
    simp only [emit_primitive,emit_addS,emit_negS,emit_mulS,emit_sumS,emit_coefficient,emit_average,emit_zeroP,emit_monomial,emit_addP,emit_negP,emit_mulP,emit_sumP,emit_weighted,rationalExpression_source _ _ x hx]
    rw [arenaSum_evaluate]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,Finset.sum_apply,Complex.ofReal_sum,rationalExpression_source _ _ x hx]
    apply Finset.sum_congr rfl
    intro i _
    exact ih i x hx
  | coefficient u e he => exact he u
  | average e he =>
    intro x hx
    simp only [emit_primitive,emit_addS,emit_negS,emit_mulS,emit_sumS,emit_coefficient,emit_average,emit_zeroP,emit_monomial,emit_addP,emit_negP,emit_mulP,emit_sumP,emit_weighted,rationalExpression_source _ _ x hx]
    rw [arenaSum_evaluate]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted, (average_over_cover (evaluate e) (angularSupport e) (angularSupport_covers e)),Finset.sum_apply,Complex.ofReal_sum,Complex.ofReal_mul,arenaProduct_evaluate,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,rationalExpression_source _ _ x hx]
    apply Finset.sum_congr rfl
    intro u _
    rw [he u x hx]
  | zeroP => intro u x hx; simp [emit_primitive,emit_addS,emit_negS,emit_mulS,emit_sumS,emit_coefficient,emit_average,emit_zeroP,emit_monomial,emit_addP,emit_negP,emit_mulP,emit_sumP,emit_weighted,evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,rationalExpression_source _ _ x hx]
  | monomial u e he =>
    intro v x hx
    by_cases h : u=v
    · subst v
      simpa only [emit_primitive,emit_addS,emit_negS,emit_mulS,emit_sumS,emit_coefficient,emit_average,emit_zeroP,emit_monomial,emit_addP,emit_negP,emit_mulP,emit_sumP,emit_weighted,ite_true,evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,MvPolynomial.coeff_monomial,rationalExpression_source _ _ x hx] using he x hx
    · simp only [emit_primitive,emit_addS,emit_negS,emit_mulS,emit_sumS,emit_coefficient,emit_average,emit_zeroP,emit_monomial,emit_addP,emit_negP,emit_mulP,emit_sumP,emit_weighted,h,ite_false,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,MvPolynomial.coeff_monomial,Pi.zero_apply,Complex.ofReal_zero,rationalExpression_source _ _ x hx]
  | addP e f he hf =>
    intro u x hx
    simp only [emit_primitive,emit_addS,emit_negS,emit_mulS,emit_sumS,emit_coefficient,emit_average,emit_zeroP,emit_monomial,emit_addP,emit_negP,emit_mulP,emit_sumP,emit_weighted,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,MvPolynomial.coeff_add,Pi.add_apply,Complex.ofReal_add,rationalExpression_source _ _ x hx]
    rw [he u x hx,hf u x hx]
  | negP e he =>
    intro u x hx
    simp only [emit_primitive,emit_addS,emit_negS,emit_mulS,emit_sumS,emit_coefficient,emit_average,emit_zeroP,emit_monomial,emit_addP,emit_negP,emit_mulP,emit_sumP,emit_weighted,rationalExpression_source _ _ x hx]
    rw [arenaNegate_evaluate,he u x hx]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,MvPolynomial.coeff_neg,Pi.neg_apply,Complex.ofReal_neg,rationalExpression_source _ _ x hx]
  | mulP e f he hf =>
    intro u x hx
    simp only [emit_primitive,emit_addS,emit_negS,emit_mulS,emit_sumS,emit_coefficient,emit_average,emit_zeroP,emit_monomial,emit_addP,emit_negP,emit_mulP,emit_sumP,emit_weighted,rationalExpression_source _ _ x hx]
    rw [arenaSum_evaluate]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,(coefficient_product_cover (evaluate e) (evaluate f) (angularSupport e) (angularSupport f) (angularSupport_covers e) (angularSupport_covers f)),Finset.sum_apply,Complex.ofReal_sum,rationalExpression_source _ _ x hx]
    apply Finset.sum_congr rfl
    intro a _
    rw [arenaSum_evaluate]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : a+b=u
    · simp only [h,ite_true,arenaProduct_evaluate,Pi.mul_apply,Complex.ofReal_mul,rationalExpression_source _ _ x hx]
      rw [he a x hx,hf b x hx]
    · simp only [h,ite_false,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,Pi.zero_apply,Complex.ofReal_zero,rationalExpression_source _ _ x hx]
  | sumP terms ih =>
    intro u x hx
    simp only [emit_primitive,emit_addS,emit_negS,emit_mulS,emit_sumS,emit_coefficient,emit_average,emit_zeroP,emit_monomial,emit_addP,emit_negP,emit_mulP,emit_sumP,emit_weighted,rationalExpression_source _ _ x hx]
    rw [arenaSum_evaluate]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,MvPolynomial.coeff_sum,Finset.sum_apply,Complex.ofReal_sum,rationalExpression_source _ _ x hx]
    apply Finset.sum_congr rfl
    intro i _
    exact ih i u x hx
  | weighted r e f he hf =>
    intro u x hx
    simp only [emit_primitive,emit_addS,emit_negS,emit_mulS,emit_sumS,emit_coefficient,emit_average,emit_zeroP,emit_monomial,emit_addP,emit_negP,emit_mulP,emit_sumP,emit_weighted,rationalExpression_source _ _ x hx]
    rw [arenaSum_evaluate]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,(coefficient_weighted_cover r (evaluate e) (evaluate f) (angularSupport e) (angularSupport f) (angularSupport_covers e) (angularSupport_covers f)),Finset.sum_apply,Complex.ofReal_sum,rationalExpression_source _ _ x hx]
    apply Finset.sum_congr rfl
    intro a _
    rw [arenaSum_evaluate]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : a+b=u
    · simp only [h,ite_true,rationalExpression_source _ _ x hx]
      exact cachedJordan_evaluate labels r _ _ _ _ (fun y hy => he a y hy) (fun y hy => hf b y hy) x hx
    · simp only [h,ite_false,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,Pi.zero_apply,Complex.ofReal_zero,rationalExpression_source _ _ x hx]

end LowEnergy.PreparationVacuumOriginalEmitter
