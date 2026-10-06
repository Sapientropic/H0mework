import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEmitterCached
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSerializedConsumer

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumOriginalEmitter
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumEngineSource
open PreparationVacuumCanonicalMoyal PreparationVacuumClockSymbol PreparationVacuumLiteralRows
open PreparationVacuumSourceCacheRules PreparationVacuumSerializedSource PreparationVacuumLiteralFeed
open PreparationVacuumEnginePaidDepth PreparationVacuumEngineIdentities PreparationVacuumEngineResponse
open scoped BigOperators Topology
abbrev SourcePhase := PreparationVacuumCanonicalMoyal.Phase

def emittedEnergy (labels : CacheLabels 0) (k : ℕ) : ArenaExpression 0 := emit labels (energy_expr k)
def emittedClock (labels : CacheLabels 0) (k : ℕ) (a : Fin 4) : ArenaExpression 0 :=
  emit labels (clock_definition_exprs k a)
def emittedResidual (labels : CacheLabels 0) (k : ℕ) (a : Fin 4) : ArenaExpression 0 :=
  emit labels (residual_exprs k a)

theorem emittedEnergy_native (labels : CacheLabels 0) (k : ℕ) (x : SourcePhase) (hx : x∈poleDomain) :
    arenaEvaluate (emittedEnergy labels k) x=(sourceEngineEnergy k x : ℂ) := by
  rw [←energy_expr_readback k]
  exact emit_evaluate labels (energy_expr k) x hx

theorem emittedClock_native (labels : CacheLabels 0) (k : ℕ) (a : Fin 4) (x : SourcePhase) (hx : x∈poleDomain) :
    arenaEvaluate (emittedClock labels k a) x=(sourceEngine (k+1) a (Fin.last (k+1)) x : ℂ) := by
  rw [←clock_definition_exprs_readback k a]
  exact emit_evaluate labels (clock_definition_exprs k a) x hx

theorem emittedResidual_native (labels : CacheLabels 0) (k : ℕ) (a : Fin 4) (x : SourcePhase) (hx : x∈poleDomain) :
    arenaEvaluate (emittedResidual labels k a) x=
      (forceOrEnergy (k+1) (sourceEngine k) (some a) (Fin.last (k+1)) x : ℂ) := by
  rw [←residual_exprs_readback k a]
  exact emit_evaluate labels (residual_exprs k a) x hx

theorem emittedClock_update (labels : CacheLabels 0) (k : ℕ) (a : Fin 4) (x : SourcePhase) (hx : x∈poleDomain) :
    arenaEvaluate (emittedClock labels k a) x=
      ∑ b : Fin 4,(coefficientValue (correctionCoefficient a b) x : ℂ)*
        arenaEvaluate (emittedResidual labels k b) x := by
  rw [emittedClock_native labels k a x hx,sourceEngine_generated_normalized k a x hx]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,emittedResidual_native labels k _ x hx]

private theorem source_first_time_zero (x : SourcePhase) : originalLeaf 1 0 x=0 := rfl
private theorem source_first_four_zero (x : SourcePhase) : originalLeaf 1 4 x=0 := rfl
private theorem source_first_five_zero (x : SourcePhase) : originalLeaf 1 5 x=0 := rfl
private theorem source_first_six_zero (x : SourcePhase) : originalLeaf 1 6 x=0 := rfl

def firstEnergyRows : ArenaExpression 0 :=
  .add (.row coefficient0 [.source 1 0])
    (.add (.row coefficient63 [.source 1 4])
      (.add (.row coefficient63 [.source 1 5]) (.add (.row coefficient63 [.source 1 6]) (.literal 0))))

theorem fixed_first_energy_rows : fixedExpression 138=firstEnergyRows := rfl

theorem fixed_first_energy_native (x : SourcePhase) :
    arenaEvaluate (fixedExpression 138) x=(sourceEngineEnergy 1 x : ℂ) := by
  rw [fixed_first_energy_rows,sourceEngineEnergy_one]
  simp only [firstEnergyRows,arenaEvaluate_add,arenaEvaluate_row,arenaEvaluate_source,
    List.foldr_cons,List.foldr_nil,arenaEvaluate_literal,source_first_time_zero,
    source_first_four_zero,source_first_five_zero,source_first_six_zero,Complex.ofReal_zero,
    zero_mul,mul_zero,add_zero,Pi.zero_apply]

private abbrev originalR := engine_const% "resolvent"
private abbrev originalJ := engine_const% "js"
private abbrev originalAct := engine_const% "act"
private theorem weighted_one (P Q : AngularPolynomial) : weighted 1 P Q=0 := by
  unfold weighted
  simp only [show ∀ f g,scalarJordan 1 f g=0 from scalarJordan_odd 0,map_zero,Finset.sum_const_zero]

private theorem R_one (X : List AngularPolynomial) :
    originalR 1 ((fun a _ => if a=0 then sourceClock else 0) : ClockAt 0) X=
      [MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)*X.getD 0 0,
        MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)*X.getD 1 0] := by
  change (engine_const% "resolvent") 1 ((fun a _ => if a=0 then sourceClock else 0) : ClockAt 0) X=_
  unfold_engine_helpers
  simp [List.range_succ,Finset.sum_range_succ,weighted_one,weighted_zero]

private theorem J_one (a : Fin 4) (X : List AngularPolynomial) :
    originalJ 1 ((fun a _ => if a=0 then sourceClock else 0) : ClockAt 0) a X=
      [MvPolynomial.C (if a=0 then sourceClock else 0)*X.getD 0 0,
        MvPolynomial.C (if a=0 then sourceClock else 0)*X.getD 1 0] := by
  change (engine_const% "js") 1 ((fun a _ => if a=0 then sourceClock else 0) : ClockAt 0) a X=_
  unfold_engine_helpers
  simp [Finset.sum_range_succ,weighted_one,weighted_zero]

private theorem act_inverse_one (X : List AngularPolynomial) :
    originalAct 1 ((fun a _ => if a=0 then sourceClock else 0) : ClockAt 0) Token.inverse X=
      [MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)*X.getD 0 0,
        MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)*X.getD 1 0] := R_one X
private theorem act_jordan_one (a : Fin 4) (X : List AngularPolynomial) :
    originalAct 1 ((fun a _ => if a=0 then sourceClock else 0) : ClockAt 0) (Token.jordan a) X=
      [MvPolynomial.C (if a=0 then sourceClock else 0)*X.getD 0 0,
        MvPolynomial.C (if a=0 then sourceClock else 0)*X.getD 1 0] := J_one a X

private theorem C_zero_function : MvPolynomial.C (fun _ : SourcePhase=>(0 : ℝ))=(0 : AngularPolynomial) := by
  exact map_zero MvPolynomial.C
private theorem average_zero : average (0 : AngularPolynomial)=(0 : PreparationVacuumCanonicalMoyal.Symbol) := by
  funext x
  simp [average]

open Lean Elab Tactic in
elab "reduce_first_force" : tactic => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgram 0) "LowEnergy") "PreparationVacuumEngineSource"
  let ids := #["affine","applyT","table","energyTable","differentiateTerm","derivativeExponent",
    "word","scale","sourceSeries","traceSeries","crossFirst","crossSecond","crossSlot"].map
    (fun suffix=>mkIdent (Name.str ns suffix))
  evalTactic (← `(tactic| simp [$[$ids:ident],*,act_inverse_one,act_jordan_one,
    engineTrace_first,engineSource,originalLeaf_first,PreparationVacuumLowerLeaves.originalFirstLeaves,
    average_constant,average_monomial,angularMoment_zero,←MvPolynomial.C_mul,←MvPolynomial.C_add,Fin.sum_univ_succ,
    Pi.mul_def,Pi.add_def,Pi.neg_def,C_zero_function,average_zero,-map_mul,-map_add]))

theorem first_residual_native (a : Fin 4) (x : SourcePhase) (hx : x∈poleDomain) :
    forceOrEnergy 1 (sourceEngine 0) (some a) (Fin.last 1) x=
      -originalLeaf 1 (Fin.castAdd 10 a) x+(sourceClock x)⁻¹^2*
        originalLeaf 1 ⟨9+a.val,by omega⟩ x := by
  change forceOrEnergy 1 ((fun a _=>if a=0 then sourceClock else 0) : ClockAt 0) (some a) (Fin.last 1) x=_
  fin_cases a <;> unfold forceOrEnergy
  all_goals reduce_first_force
  all_goals
    have hc:=poleFunction_nonzero x hx 0
    change sourceClock x≠0 at hc
    field_simp [hc]
    ring

private theorem eval_monomial_add (x : SourcePhase) (e f : Fin 7 →₀ ℕ) (q : ℚ) :
    evalAt x (MvPolynomial.monomial (e+f) q)=
      evalAt x (MvPolynomial.monomial e q)*evalAt x (MvPolynomial.monomial f 1) := by
  rw [←map_mul,MvPolynomial.monomial_mul,mul_one]

private theorem eval_monomial_single (x : SourcePhase) (i : Fin 7) (n : ℕ) (q : ℚ) :
    evalAt x (MvPolynomial.monomial (Finsupp.single i n) q)=(q : ℝ)*(evalAt x (MvPolynomial.X i))^n := by
  simp [evalAt,MvPolynomial.eval₂_monomial]

def firstSpatialCoefficients : Fin 3 → Fin 6 → NormalizedCoefficient :=
  ![![coefficient23,coefficient24,coefficient25,coefficient26,coefficient27,coefficient28],
    ![coefficient24,coefficient29,coefficient30,coefficient27,coefficient31,coefficient32],
    ![coefficient25,coefficient30,coefficient33,coefficient28,coefficient32,coefficient34]]

def firstSpatialAST (i : Fin 3) : ArenaExpression 0 :=
  .add (.row (firstSpatialCoefficients i 0) [.source 1 10])
    (.add (.row (firstSpatialCoefficients i 1) [.source 1 11])
      (.add (.row (firstSpatialCoefficients i 2) [.source 1 12])
        (.add (.row (firstSpatialCoefficients i 3) [.source 1 1])
          (.add (.row (firstSpatialCoefficients i 4) [.source 1 2])
            (.add (.row (firstSpatialCoefficients i 5) [.source 1 3]) (.literal 0))))))

theorem fixed_first_spatial_rows (i : Fin 3) :
    fixedExpression (fixedClockIds 0 (Fin.succ i))=firstSpatialAST i := by
  fin_cases i <;> rfl

def firstScalarMatrix : Fin 3 → Fin 3 → NormalizedCoefficient :=
  ![![coefficient26,coefficient27,coefficient28],![coefficient27,coefficient31,coefficient32],
    ![coefficient28,coefficient32,coefficient34]]
def firstGaugeMatrix : Fin 3 → Fin 3 → NormalizedCoefficient :=
  ![![coefficient23,coefficient24,coefficient25],![coefficient24,coefficient29,coefficient30],
    ![coefficient25,coefficient30,coefficient33]]
private theorem firstSpatial_scalar (i j : Fin 3) :
    firstSpatialCoefficients i (Fin.natAdd 3 j)=firstScalarMatrix i j := by fin_cases i <;> fin_cases j <;> rfl
private theorem firstSpatial_gauge (i j : Fin 3) :
    firstSpatialCoefficients i (Fin.castAdd 3 j)=firstGaugeMatrix i j := by fin_cases i <;> fin_cases j <;> rfl
private theorem correction_spatial_shape (i j : Fin 3) :
    correctionCoefficient (Fin.succ i) (Fin.succ j)=
      ⟨MvPolynomial.X 0^3*adjugatePolynomial i j,![0,0,1]⟩ := by
  simp only [correctionCoefficient,inverseCoefficient,Fin.cases_succ,negateCoefficient]
  congr 1
  ring

/-- The scalar entries are exactly the negated clock-cubed adjugate
entries: the identity is proved once on the normalized numerator/pole
pair instead of once per evaluation point with denominators and
evaluated monomials. -/
private theorem prodX_add (s t : Fin 7→₀ℕ) :
    (s+t).prod (fun n e => (MvPolynomial.X n : CentralPolynomial)^e)=
      s.prod (fun n e => (MvPolynomial.X n : CentralPolynomial)^e)*
        t.prod (fun n e => (MvPolynomial.X n : CentralPolynomial)^e) :=
  Finsupp.prod_add_index' (fun _=>pow_zero _) (fun _ _ _=>pow_add _ _ _)

private theorem prodX_single (i : Fin 7) (n : ℕ) :
    (Finsupp.single i n).prod (fun n e => (MvPolynomial.X n : CentralPolynomial)^e)=
      (MvPolynomial.X i)^n :=
  Finsupp.prod_single_index (pow_zero _)

set_option linter.unusedSimpArgs false in
private theorem scalar_matrix_entry (i j : Fin 3) :
    firstScalarMatrix i j=
      ⟨-(MvPolynomial.X 0^3*adjugatePolynomial i j),![0,0,1]⟩ := by
  fin_cases i <;> fin_cases j <;>
    norm_num [firstScalarMatrix,coefficient26,coefficient27,coefficient28,
      coefficient31,coefficient32,coefficient34,adjugatePolynomial,centralQ,
      Matrix.adjugate_fin_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;>
    simp only [MvPolynomial.monomial_eq,prodX_add,prodX_single,map_one,one_mul] <;>
    ring_nf

set_option linter.unusedSimpArgs false in
/-- The gauge entries are the clock-singular adjugate entries: the same
normalized-coefficient identification, computed once per entry. -/
private theorem gauge_matrix_entry (i j : Fin 3) :
    firstGaugeMatrix i j=
      ⟨MvPolynomial.X 0*adjugatePolynomial i j,![0,0,1]⟩ := by
  fin_cases i <;> fin_cases j <;>
    norm_num [firstGaugeMatrix,coefficient23,coefficient24,coefficient25,
      coefficient29,coefficient30,coefficient33,adjugatePolynomial,centralQ,
      Matrix.adjugate_fin_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;>
    simp only [MvPolynomial.monomial_eq,prodX_add,prodX_single,map_one,one_mul] <;>
    ring_nf

theorem first_scalar_coefficient (i j : Fin 3) (x : SourcePhase) :
    coefficientValue (firstSpatialCoefficients i (Fin.natAdd 3 j)) x=
      -coefficientValue (correctionCoefficient (Fin.succ i) (Fin.succ j)) x := by
  rw [firstSpatial_scalar,correction_spatial_shape,scalar_matrix_entry]
  exact negateCoefficient_source
    ⟨MvPolynomial.X 0^3*adjugatePolynomial i j,![0,0,1]⟩ x

private theorem evalC_clock (x : SourcePhase) : evalAt x (MvPolynomial.X 0)=sourceClock x := by
  simp [evalAt,sourceVariables,PreparationVacuumClockJacobian.actualC,sourceClock]

theorem first_gauge_square (i j : Fin 3) (x : SourcePhase) :
    coefficientValue (firstSpatialCoefficients i (Fin.castAdd 3 j)) x*sourceClock x^2=
      -coefficientValue (firstSpatialCoefficients i (Fin.natAdd 3 j)) x := by
  rw [firstSpatial_scalar,firstSpatial_gauge,gauge_matrix_entry,scalar_matrix_entry]
  simp only [coefficientValue_denominator,map_mul,map_pow,map_neg,evalC_clock,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,pow_zero,
    mul_one]
  ring

theorem first_gauge_coefficient (i j : Fin 3) (x : SourcePhase) (hx : x∈poleDomain) :
    coefficientValue (firstSpatialCoefficients i (Fin.castAdd 3 j)) x=
      coefficientValue (correctionCoefficient (Fin.succ i) (Fin.succ j)) x*(sourceClock x)⁻¹^2 := by
  have hc:=poleFunction_nonzero x hx 0
  change sourceClock x≠0 at hc
  rw [inv_pow,←div_eq_mul_inv]
  apply (eq_div_iff (pow_ne_zero 2 hc)).mpr
  rw [first_gauge_square,first_scalar_coefficient,neg_neg]


def firstSpatialValue (i : Fin 3) (x : SourcePhase) : ℝ :=
  ∑ j : Fin 3,
    (coefficientValue (firstSpatialCoefficients i (Fin.castAdd 3 j)) x *
        originalLeaf 1 ⟨10+j.val,by omega⟩ x +
      coefficientValue (firstSpatialCoefficients i (Fin.natAdd 3 j)) x *
        originalLeaf 1 ⟨1+j.val,by omega⟩ x)

theorem fixed_first_spatial_readback (i : Fin 3) (x : SourcePhase) :
    arenaEvaluate (fixedExpression (fixedClockIds 0 (Fin.succ i))) x=(firstSpatialValue i x : ℂ) := by
  rw [fixed_first_spatial_rows]
  simp only [firstSpatialAST,firstSpatialValue,arenaEvaluate_add,arenaEvaluate_row,
    arenaEvaluate_source,List.foldr_cons,List.foldr_nil,arenaEvaluate_literal,
    Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_zero,
    mul_one,add_zero,Fin.sum_univ_three]
  change _ = ((coefficientValue (firstSpatialCoefficients i 0) x : ℂ)*(originalLeaf 1 10 x : ℂ) + (coefficientValue (firstSpatialCoefficients i 3) x : ℂ)*(originalLeaf 1 1 x : ℂ)) + ((coefficientValue (firstSpatialCoefficients i 1) x : ℂ)*(originalLeaf 1 11 x : ℂ) + (coefficientValue (firstSpatialCoefficients i 4) x : ℂ)*(originalLeaf 1 2 x : ℂ)) + ((coefficientValue (firstSpatialCoefficients i 2) x : ℂ)*(originalLeaf 1 12 x : ℂ) + (coefficientValue (firstSpatialCoefficients i 5) x : ℂ)*(originalLeaf 1 3 x : ℂ))
  ring

theorem first_spatial_value_native (i : Fin 3) (x : SourcePhase) (hx : x∈poleDomain) :
    firstSpatialValue i x=sourceEngine 1 (Fin.succ i) (Fin.last 1) x := by
  rw [sourceEngine_generated_normalized 0 (Fin.succ i) x hx]
  rw [Fin.sum_univ_succ]
  have hzero : correctionCoefficient (Fin.succ i) 0=⟨0,![0,0,0]⟩ := by
    simp only [correctionCoefficient,inverseCoefficient,Fin.cases_succ,Fin.cases_zero,negateCoefficient,polynomialCoefficient,neg_zero]
    congr 1
    funext j
    fin_cases j <;> rfl
  rw [hzero]
  have hc0 : coefficientValue (⟨0,![0,0,0]⟩ : NormalizedCoefficient) x=0 := by simp [coefficientValue_denominator]
  rw [hc0,zero_mul,zero_add]
  unfold firstSpatialValue
  apply Finset.sum_congr rfl
  intro j _
  rw [first_gauge_coefficient i j x hx,first_scalar_coefficient,first_residual_native _ x hx]
  have h1 : (⟨1+j.val,by omega⟩ : Fin 14)=Fin.castAdd 10 (Fin.succ j) := by ext; simp; omega
  have h10 : (⟨10+j.val,by omega⟩ : Fin 14)=⟨9+(Fin.succ j).val,by omega⟩ := by ext; simp; omega
  rw [h1,h10]
  ring

theorem fixed_first_spatial_native (i : Fin 3) (x : SourcePhase) (hx : x∈poleDomain) :
    arenaEvaluate (fixedExpression (fixedClockIds 0 (Fin.succ i))) x=
      (sourceEngine 1 (Fin.succ i) (Fin.last 1) x : ℂ) := by
  rw [fixed_first_spatial_readback,first_spatial_value_native i x hx]


private theorem source_first_nine_zero (x : SourcePhase) : originalLeaf 1 9 x=0 := rfl

def firstTimeRows : ArenaExpression 0 :=
  .add (.row coefficient21 [.source 1 0])
    (.add (.row coefficient22 [.source 1 4])
      (.add (.row coefficient22 [.source 1 5]) (.add (.row coefficient22 [.source 1 6]) (.literal 0))))

theorem fixed_first_time_rows : fixedExpression 48=firstTimeRows := rfl

theorem fixed_first_time_zero (x : SourcePhase) : arenaEvaluate (fixedExpression 48) x=0 := by
  rw [fixed_first_time_rows]
  simp only [firstTimeRows,arenaEvaluate_add,arenaEvaluate_row,arenaEvaluate_source,
    List.foldr_cons,List.foldr_nil,arenaEvaluate_literal,source_first_time_zero,
    source_first_four_zero,source_first_five_zero,source_first_six_zero,Complex.ofReal_zero,
    zero_mul,mul_zero,add_zero]

theorem first_time_native_zero (x : SourcePhase) (hx : x∈poleDomain) :
    sourceEngine 1 0 (Fin.last 1) x=0 := by
  rw [sourceEngine_generated_normalized 0 0 x hx,Fin.sum_univ_succ]
  have hzero (j : Fin 3) : correctionCoefficient 0 (Fin.succ j)=⟨0,![0,0,0]⟩ := by
    simp only [correctionCoefficient,inverseCoefficient,Fin.cases_succ,Fin.cases_zero,negateCoefficient,polynomialCoefficient,neg_zero]
    congr 1
    funext j
    fin_cases j <;> rfl
  have hc0 : coefficientValue (⟨0,![0,0,0]⟩ : NormalizedCoefficient) x=0 := by simp [coefficientValue_denominator]
  simp only [hzero,hc0,zero_mul,Finset.sum_const_zero,add_zero]
  rw [first_residual_native 0 x hx]
  change _*(-originalLeaf 1 0 x+(sourceClock x)⁻¹^2*originalLeaf 1 9 x)=0
  rw [source_first_time_zero,source_first_nine_zero]
  ring

theorem fixed_first_clock_native (a : Fin 4) (x : SourcePhase) (hx : x∈poleDomain) :
    arenaEvaluate (fixedExpression (fixedClockIds 0 a)) x=(sourceEngine 1 a (Fin.last 1) x : ℂ) := by
  induction a using Fin.cases with
  | zero =>
    change arenaEvaluate (fixedExpression 48) x=(sourceEngine 1 0 (Fin.last 1) x : ℂ)
    rw [fixed_first_time_zero,first_time_native_zero x hx,Complex.ofReal_zero]
  | succ i => exact fixed_first_spatial_native i x hx

theorem fixed_first_stage_native (i : Fin 5) (x : SourcePhase) (hx : x∈poleDomain) :
    arenaEvaluate (fixedExpression (fixedStageId 0 i)) x=(actualFiveSymbols 1 i x : ℂ) := by
  induction i using Fin.lastCases with
  | last => exact fixed_first_energy_native x
  | cast a => simpa only [fixedStageId,actualFiveSymbols,Fin.lastCases_castSucc] using fixed_first_clock_native a x hx


def emittedFive (labels : CacheLabels 0) (k : ℕ) (i : Fin 5) : ArenaExpression 0 :=
  Fin.lastCases (emittedEnergy labels (k+1)) (fun a=>emittedClock labels k a) i

theorem emittedFive_native (labels : CacheLabels 0) (k : ℕ) (i : Fin 5)
    (x : SourcePhase) (hx : x∈poleDomain) :
    arenaEvaluate (emittedFive labels k i) x=(actualFiveSymbols (k+1) i x : ℂ) := by
  induction i using Fin.lastCases with
  | last=>simpa only [emittedFive,actualFiveSymbols,Fin.lastCases_last] using emittedEnergy_native labels (k+1) x hx
  | cast a=>simpa only [emittedFive,actualFiveSymbols,Fin.lastCases_castSucc] using emittedClock_native labels k a x hx

theorem fixed_first_stage_emitted (labels : CacheLabels 0) (i : Fin 5)
    (x : SourcePhase) (hx : x∈poleDomain) :
    arenaEvaluate (fixedExpression (fixedStageId 0 i)) x=arenaEvaluate (emittedFive labels 0 i) x := by
  rw [fixed_first_stage_native i x hx,emittedFive_native labels 0 i x hx]

open PreparationVacuumNumericSource PreparationVacuumArenaBudget PreparationVacuumEngineBudget PreparationVacuumArenaRows
open PreparationVacuumCentralBudget PreparationVacuumClockBudget PreparationVacuumMoyalNormalization
open PreparationVacuumEngineSmooth CanonicalPreparationCutoff CanonicalPreparationSquareCutoff

theorem actual_original_first_stage_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (M : ℕ) (i : Fin 5) :
    FiniteBound (actualFiveSymbols 1 i) M (originalFiveBounds 0 i) (z,WithLp.toLp 2 u) := by
  have hx:=sourceUnit_admitted z u zbox ubox unit
  have bound:=actual_original_fixed_five_budget z u zbox ubox unit M 0 i
  have germ : arenaEvaluate (fixedExpression (fixedStageId 0 i))=ᶠ[𝓝 (z,WithLp.toLp 2 u)]
      (fun x=>(actualFiveSymbols 1 i x : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with x h
    exact fixed_first_stage_native i x h
  have smooth : SmoothSymbol (actualFiveSymbols 1 i) := by
    induction i using Fin.lastCases with
    | last=>simpa only [actualFiveSymbols,Fin.lastCases_last] using sourceEngineEnergy_smooth 1
    | cast a=>simpa only [actualFiveSymbols,Fin.lastCases_castSucc] using sourceEngine_smooth 1 a (Fin.last 1)
  intro m hm w
  have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  have result:=bound m hm w
  rw [read,realCast_jet _ smooth m w _ hx,Complex.norm_real,Real.norm_eq_abs] at result
  exact result

end LowEnergy.PreparationVacuumOriginalEmitter
