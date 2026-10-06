import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationArenaDerivativeDemand

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumArenaRows
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumArenaBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalBudget PreparationVacuumCentralBudget
open PreparationVacuumClockSymbol PreparationVacuumEngineSource PreparationVacuumEngineSmooth
open SourceQuantumConfigurationHilbert CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open PreparationPhaseSource PreparationScalarCoordinates PreparationActualFactor PreparationVacuumClockPole
open scoped BigOperators ContDiff Topology

abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol

theorem realCast_smooth (f : Symbol) (smooth : SmoothSymbol f) :
    SmoothComplex (fun x=>(f x : ℂ)) :=
  fun x hx=>Complex.ofRealCLM.contDiff.contDiffAt.comp_contDiffWithinAt x (smooth x hx)

theorem realCast_jet (f : Symbol) (smooth : SmoothSymbol f) (m : ℕ)
    (w : Word m) (x : Phase) (hx : x∈poleDomain) :
    iteratedFDeriv ℝ m (fun y=>(f y : ℂ)) x (slotDirection∘w)=(jet m f w x : ℂ) := by
  have read:=Complex.ofRealCLM.iteratedFDeriv_comp_left
    ((smooth x hx).contDiffAt (poleDomain_open.mem_nhds hx))
    (show (m : ℕ∞ω)≤∞ by exact_mod_cast (ENat.natCast_lt_top m).le)
  exact congrArg (fun D=>D (slotDirection∘w)) read

theorem realCast_budget (f : Symbol) (smooth : SmoothSymbol f) (B : ArrayBound)
    (N : ℕ) (x : Phase) (hx : x∈poleDomain) (bound : FiniteBound f N B x) :
    ComplexJetBound (fun y=>(f y : ℂ)) N B x := by
  intro m hm w
  rw [realCast_jet f smooth m w x hx,Complex.norm_real,Real.norm_eq_abs]
  exact bound m hm w

theorem coefficientValue_smooth (c : NormalizedCoefficient) : SmoothSymbol (coefficientValue c) := by
  rw [coefficientValue_fold]
  exact foldValue_smooth _ (fun i=>(inversePole_smooth i).pow (c.poles i)) _ _
    (polynomialSymbol_smooth c.numerator)

theorem complexMoyal_smooth (r : ℕ) (f g : ComplexSymbol)
    (hf : SmoothComplex f) (hg : SmoothComplex g) :
    SmoothComplex (PreparationVacuumDAGSemantic.complexMoyal r f g) := by
  have fc : SmoothComplex (complexCoefficient r f g):=
    contDiffOn_const.mul (complexContraction_smooth poleDomain_open r f g hf hg)
  intro x hx
  have germ : complexCoefficient r f g=ᶠ[𝓝 x] PreparationVacuumDAGSemantic.complexMoyal r f g := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact complexCoefficient_arena poleDomain_open r f g hf hg y hy
  exact ((fc x hx).contDiffAt (poleDomain_open.mem_nhds hx)).congr_of_eventuallyEq
    germ.symm |>.contDiffWithinAt

theorem arena_smooth {k : ℕ} (e : ArenaExpression k) : SmoothComplex (arenaEvaluate e) := by
  refine ArenaExpression.rec
    (motive_1:=fun e=>SmoothComplex (arenaEvaluate e))
    (motive_2:=fun word=>SmoothComplex (orderedProduct (word.map arenaEvaluate)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro c;exact contDiffOn_const
  · intro d j;exact realCast_smooth _ (originalLeaf_pole_smooth d j)
  · intro l a
    have same : arenaEvaluate (.clock l a : ArenaExpression k)=
        (fun x=>(sourceEngine k a l x : ℂ)) := funext (arena_clock_readback k l a)
    rw [same]
    exact realCast_smooth _ (sourceEngine_smooth k a l)
  · intro r e f he hf;exact complexMoyal_smooth r _ _ he hf
  · intro c word ih
    have same : arenaEvaluate (.row c word)=
        (fun x=>(coefficientValue c x : ℂ)*orderedProduct (word.map arenaEvaluate) x) := by
      funext x
      rw [arenaEvaluate_row]
      simp only [orderedProduct,List.foldr_map]
    rw [same]
    exact (realCast_smooth _ (coefficientValue_smooth c)).mul ih
  · intro e f he hf;exact he.add hf
  · exact contDiffOn_const
  · intro e word he ih;exact he.mul ih

structure PrimitiveBounds {k : ℕ} (input : PrimitiveArrays k) (N : ℕ) (x : Phase) : Prop where
  leaf : ∀ d j,FiniteBound (originalLeaf d j) N (input.leaf d j) x
  clock : ∀ l a,FiniteBound (sourceEngine k a l) N (input.clock l a) x
  central : ∀ c,FiniteBound (coefficientValue c) N (input.central c) x

theorem complex_finite_add (f g : ComplexSymbol) (hf : SmoothComplex f) (hg : SmoothComplex g)
    (B D : ArrayBound) (N : ℕ) (x : Phase) (hx : x∈poleDomain)
    (left : ComplexJetBound f N B x) (right : ComplexJetBound g N D x) :
    ComplexJetBound (fun y=>f y+g y) N (fun m=>B m+D m) x := by
  intro m hm w
  have read:=complexListJet_add poleDomain_open f g hf hg (List.ofFn (slotDirection∘w)) hx
  dsimp only at read
  rw [complexListJet_ofFn poleDomain_open (hf.add hg) m (slotDirection∘w) x hx,
    complexListJet_ofFn poleDomain_open hf m (slotDirection∘w) x hx,
    complexListJet_ofFn poleDomain_open hg m (slotDirection∘w) x hx] at read
  rw [read]
  exact (norm_add_le _ _).trans (add_le_add (left m hm w) (right m hm w))

theorem complex_bound_restrict (f : ComplexSymbol) (B : ArrayBound) (N M : ℕ) (x : Phase)
    (bound : ComplexJetBound f N B x) (lower : M≤N) : ComplexJetBound f M B x :=
  fun m hm w=>bound m (hm.trans lower) w

theorem derivativeExtra_word_mem {k : ℕ} (word : List (ArenaExpression k))
    (e : ArenaExpression k) (mem : e∈word) :
    derivativeExtra e≤word.foldr (fun a n=>max (derivativeExtra a) n) 0 := by
  induction word with
  | nil=>simp at mem
  | cons a word ih=>
    rcases List.mem_cons.mp mem with same|tail
    · subst e;exact le_max_left _ _
    · exact (ih tail).trans (le_max_right _ _)

theorem actual_expression_budget {k : ℕ} (input : PrimitiveArrays k)
    (positive : PrimitiveNonnegative input) (N : ℕ) (x : Phase) (hx : x∈poleDomain)
    (primitives : PrimitiveBounds input N x) (e : ArenaExpression k) :
    ∀ M,derivativeDemand e M≤N → ComplexJetBound (arenaEvaluate e) M (expressionArray input e) x := by
  refine ArenaExpression.rec
    (motive_1:=fun e=>∀ M,derivativeDemand e M≤N →
      ComplexJetBound (arenaEvaluate e) M (expressionArray input e) x)
    (motive_2:=fun word=>∀ M,M+word.foldr (fun a n=>max (derivativeExtra a) n) 0≤N →
      ComplexJetBound (orderedProduct (word.map arenaEvaluate)) M
        (orderedArray (word.map (expressionArray input))) x)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro c M _
    simpa only [arenaEvaluate_literal,expressionArray_literal,Complex.norm_real,Real.norm_eq_abs]
      using complex_finite_constant (c : ℂ) M x
  · intro d j M paid
    simp only [derivativeDemand,derivativeExtra_source,Nat.add_zero] at paid
    exact complex_bound_restrict _ _ N M x
      (realCast_budget _ (originalLeaf_pole_smooth d j) _ N x hx (primitives.leaf d j)) paid
  · intro l a M paid
    simp only [derivativeDemand,derivativeExtra_clock,Nat.add_zero] at paid
    rw [show arenaEvaluate (.clock l a : ArenaExpression k)=
      (fun y=>(sourceEngine k a l y : ℂ)) from funext (arena_clock_readback k l a)]
    exact complex_bound_restrict _ _ N M x
      (realCast_budget _ (sourceEngine_smooth k a l) _ N x hx (primitives.clock l a)) paid
  · intro r e f he hf M paid
    have epaid : derivativeDemand e (r+M)≤N := by
      unfold derivativeDemand at paid ⊢
      rw [derivativeExtra_moyal] at paid
      omega
    have fpaid : derivativeDemand f (r+M)≤N := by
      unfold derivativeDemand at paid ⊢
      rw [derivativeExtra_moyal] at paid
      omega
    intro m hm w
    have ev:=complex_bound_restrict _ _ (r+M) (r+m) x (he (r+M) epaid) (by omega)
    have fv:=complex_bound_restrict _ _ (r+M) (r+m) x (hf (r+M) fpaid) (by omega)
    have read:=actual_arena_moyal_list_budget poleDomain_open r (arenaEvaluate e) (arenaEvaluate f)
      (arena_smooth e) (arena_smooth f) (List.ofFn (slotDirection∘w)) (canonical_ofFn w)
      x hx (expressionArray input e) (expressionArray input f)
      (expressionArray_nonnegative input positive e) (expressionArray_nonnegative input positive f)
      (by simpa only [List.length_ofFn] using ev) (by simpa only [List.length_ofFn] using fv)
    rw [complexListJet_ofFn poleDomain_open (complexMoyal_smooth r _ _ (arena_smooth e) (arena_smooth f))
      m (slotDirection∘w) x hx] at read
    simpa only [List.length_ofFn,arenaEvaluate_moyal,expressionArray_moyal] using read
  · intro c word ih M paid
    have order : M≤N := by unfold derivativeDemand at paid;omega
    have wordPaid : M+word.foldr (fun a n=>max (derivativeExtra a) n) 0≤N := by
      simpa only [derivativeDemand,derivativeExtra_row] using paid
    rw [expressionArray_row]
    have same : arenaEvaluate (.row c word)=
        (fun y=>(coefficientValue c y : ℂ)*orderedProduct (word.map arenaEvaluate) y) := by
      funext y;rw [arenaEvaluate_row];simp only [orderedProduct,List.foldr_map]
    rw [same]
    apply complex_finite_product _ _ (realCast_smooth _ (coefficientValue_smooth c))
      (orderedProduct_smooth _ (by intro f hf;obtain ⟨a,_,rfl⟩:=List.mem_map.mp hf;exact arena_smooth a))
      _ _ (positive.central c) M x hx
      (complex_bound_restrict _ _ N M x
        (realCast_budget _ (coefficientValue_smooth c) _ N x hx (primitives.central c)) order)
      (ih M wordPaid)
  · intro e f he hf M paid
    have ep : derivativeDemand e M≤N := by
      unfold derivativeDemand at paid ⊢;rw [derivativeExtra_add] at paid;omega
    have fp : derivativeDemand f M≤N := by
      unfold derivativeDemand at paid ⊢;rw [derivativeExtra_add] at paid;omega
    exact complex_finite_add _ _ (arena_smooth e) (arena_smooth f) _ _ M x hx (he M ep) (hf M fp)
  · intro M _
    change ComplexJetBound (fun _=>1) M (constantArray 1) x
    simpa only [norm_one] using complex_finite_constant 1 M x
  · intro e word he ih M paid
    have ep : derivativeDemand e M≤N := by
      change M+max (derivativeExtra e) _≤N at paid
      unfold derivativeDemand;omega
    have wp : M+word.foldr (fun a n=>max (derivativeExtra a) n) 0≤N := by
      change M+max (derivativeExtra e) _≤N at paid
      omega
    exact complex_finite_product _ _ (arena_smooth e)
      (orderedProduct_smooth _ (by intro f hf;obtain ⟨a,_,rfl⟩:=List.mem_map.mp hf;exact arena_smooth a))
      _ _ (expressionArray_nonnegative input positive e) M x hx (he M ep) (ih M wp)


-- Only primitive leaf arrays and the already generated central-field responsibility
-- enter the expanded graph. All clock definitions are expanded by sourceEngineTerm.
def sourceArrays {x : Phase} {N : ℕ} (central : PrimitiveInputs x N)
    (leaf : Fin 3 → Fin 14 → ArrayBound) : PrimitiveArrays 0 where
  leaf:=leaf
  clock _ a:=if a=0 then central.clock else (fun _=>0)
  central:=sourceCoefficientArray central

theorem sourceArrays_nonnegative {x : Phase} {N : ℕ} (central : PrimitiveInputs x N)
    (leaf : Fin 3 → Fin 14 → ArrayBound) (positive : ∀ d j m,0 ≤ leaf d j m) :
    PrimitiveNonnegative (sourceArrays central leaf) where
  leaf:=positive
  clock:=by intro _ a m;dsimp [sourceArrays];split_ifs;exact central.clock_nonnegative m;exact le_refl 0
  central:=by
    intro c m
    exact foldArray_nonnegative _
      (fun i=>powerArray_nonnegative _ (inverseArrays_nonnegative central i) (c.poles i))
      _ _ (numeratorArray_nonnegative _ (fieldArrays_nonnegative central) c.numerator) m

theorem sourceArrays_bounds (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ)
    (central : PrimitiveInputs (z,WithLp.toLp 2 u) N)
    (leaf : Fin 3 → Fin 14 → ArrayBound)
    (bounds : ∀ d j,FiniteBound (originalLeaf d j) N (leaf d j) (z,WithLp.toLp 2 u)) :
    PrimitiveBounds (sourceArrays central leaf) N (z,WithLp.toLp 2 u) where
  leaf:=bounds
  central:=actual_coefficient_budget z u zbox ubox unit N central
  clock:=by
    intro l a
    have first : l=(0 : Fin 1) := by apply Fin.ext;have:=l.isLt;omega
    rw [first,sourceEngine_initial]
    dsimp [sourceArrays]
    split_ifs with axis
    · have cb:=central.fields 0
      change FiniteBound sourceClock N central.clock (z,WithLp.toLp 2 u) at cb
      exact cb
    · intro m _ w
      change |jet m (fun _ : Phase=>(0 : ℝ)) w (z,WithLp.toLp 2 u)|≤0
      cases m with
      | zero=>simp [jet]
      | succ m=>simp [jet]

def generatedEnergyArray {x : Phase} {N : ℕ} (central : PrimitiveInputs x N)
    (leaf : Fin 3 → Fin 14 → ArrayBound) (k : ℕ) : ArrayBound :=
  expressionArray (sourceArrays central leaf) (arena_energy_expr k)

def generatedClockArray {x : Phase} {N : ℕ} (central : PrimitiveInputs x N)
    (leaf : Fin 3 → Fin 14 → ArrayBound) (k : ℕ) (a : Fin 4) : ArrayBound :=
  expressionArray (sourceArrays central leaf) (arena_clock_definition_exprs k a)

theorem actual_generated_energy_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ)
    (central : PrimitiveInputs (z,WithLp.toLp 2 u) N)
    (leaf : Fin 3 → Fin 14 → ArrayBound) (positive : ∀ d j m,0 ≤ leaf d j m)
    (bounds : ∀ d j,FiniteBound (originalLeaf d j) N (leaf d j) (z,WithLp.toLp 2 u))
    (k M : ℕ) (paid : derivativeDemand (arena_energy_expr k) M≤N) :
    FiniteBound (sourceEngineEnergy k) M (generatedEnergyArray central leaf k) (z,WithLp.toLp 2 u) := by
  let x : Phase:=(z,WithLp.toLp 2 u)
  have hx : x∈poleDomain:=by
    refine ⟨actual_closed_phase_cone z u zbox ubox unit,?_⟩
    have guard:=PreparationVacuumClockGuard.actual_clockMatrix_det_j15 z u zbox ubox
    have positiveDet : 0 < (clockMatrix (fullCoordinates.symm z)
      (nativeCovector (WithLp.toLp 2 u))).det:=by linarith
    exact positiveDet.ne'
  have all:=actual_expression_budget (sourceArrays central leaf)
    (sourceArrays_nonnegative central leaf positive) N x hx
    (sourceArrays_bounds z u zbox ubox unit N central leaf bounds) (arena_energy_expr k) M paid
  have germ : arenaEvaluate (arena_energy_expr k)=ᶠ[𝓝 x]
      (fun y=>(sourceEngineEnergy k y : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact arena_energy_readback k y hy
  intro m hm w
  have read:=congrArg (fun D=>D (slotDirection∘w))
    ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  have result:=all m hm w
  rw [read,realCast_jet _ (sourceEngineEnergy_smooth k) m w x hx,
    Complex.norm_real,Real.norm_eq_abs] at result
  exact result

theorem actual_generated_clock_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ)
    (central : PrimitiveInputs (z,WithLp.toLp 2 u) N)
    (leaf : Fin 3 → Fin 14 → ArrayBound) (positive : ∀ d j m,0 ≤ leaf d j m)
    (bounds : ∀ d j,FiniteBound (originalLeaf d j) N (leaf d j) (z,WithLp.toLp 2 u))
    (k M : ℕ) (a : Fin 4) (paid : derivativeDemand (arena_clock_definition_exprs k a) M≤N) :
    FiniteBound (sourceEngine (k+1) a (Fin.last (k+1))) M
      (generatedClockArray central leaf k a) (z,WithLp.toLp 2 u) := by
  let x : Phase:=(z,WithLp.toLp 2 u)
  have hx : x∈poleDomain:=by
    refine ⟨actual_closed_phase_cone z u zbox ubox unit,?_⟩
    have guard:=PreparationVacuumClockGuard.actual_clockMatrix_det_j15 z u zbox ubox
    have positiveDet : 0 < (clockMatrix (fullCoordinates.symm z)
      (nativeCovector (WithLp.toLp 2 u))).det:=by linarith
    exact positiveDet.ne'
  have all:=actual_expression_budget (sourceArrays central leaf)
    (sourceArrays_nonnegative central leaf positive) N x hx
    (sourceArrays_bounds z u zbox ubox unit N central leaf bounds) (arena_clock_definition_exprs k a) M paid
  have germ : arenaEvaluate (arena_clock_definition_exprs k a)=ᶠ[𝓝 x]
      (fun y=>(sourceEngine (k+1) a (Fin.last (k+1)) y : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact arena_clock_definition_readback k a y hy
  intro m hm w
  have read:=congrArg (fun D=>D (slotDirection∘w))
    ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  have result:=all m hm w
  rw [read,realCast_jet _ (sourceEngine_smooth (k+1) a (Fin.last (k+1))) m w x hx,
    Complex.norm_real,Real.norm_eq_abs] at result
  exact result

end LowEnergy.PreparationVacuumArenaRows
