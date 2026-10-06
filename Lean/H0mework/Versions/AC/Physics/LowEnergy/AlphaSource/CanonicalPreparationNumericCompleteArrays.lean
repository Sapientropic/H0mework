import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationNumericPrimitiveArrays

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNumericSource
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumArenaRows
open PreparationVacuumClockSymbol PreparationVacuumCanonicalMoyal PreparationVacuumEngineBudget
open PreparationVacuumEngineSource PreparationVacuumEngineSmooth PreparationVacuumArenaBudget
open PreparationVacuumArenaCollect PreparationVacuumMoyalNormalization PreparationVacuumClockBudget
open PreparationVacuumCentralBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology

def normalizedClockExpression (k : ℕ) (a : Fin 4) : ArenaExpression 0 :=
  normalizedExpression (normalizeMoyal (arena_clock_definition_exprs k a))

theorem normalizedClock_source (k : ℕ) (a : Fin 4) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (normalizedClockExpression k a) x=(sourceEngine (k+1) a (Fin.last (k+1)) x : ℂ) := by
  rw [normalizedClockExpression,normalizedExpression_source _ x hx,normalizeMoyal_source _ x hx]
  exact arena_clock_definition_readback k a x hx

def sourceEnergyArray (k : ℕ) : ArrayBound :=
  expressionArray sourcePrimitiveArrays (moyalNormalizedEnergy k)

def sourceClockCoefficientArray (k : ℕ) (a : Fin 4) : ArrayBound :=
  expressionArray sourcePrimitiveArrays (normalizedClockExpression k a)

theorem sourceEnergyArray_nonnegative (k m : ℕ) : 0 ≤ sourceEnergyArray k m :=
  expressionArray_nonnegative sourcePrimitiveArrays source_primitive_nonnegative _ m

theorem sourceClockCoefficientArray_nonnegative (k m : ℕ) (a : Fin 4) :
    0 ≤ sourceClockCoefficientArray k a m :=
  expressionArray_nonnegative sourcePrimitiveArrays source_primitive_nonnegative _ m

theorem actual_source_expression_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (e : ArenaExpression 0) (M : ℕ) :
    ComplexJetBound (arenaEvaluate e) M (expressionArray sourcePrimitiveArrays e) (z,WithLp.toLp 2 u) :=
  actual_expression_budget sourcePrimitiveArrays source_primitive_nonnegative
    (derivativeDemand e M) _ (sourceUnit_admitted z u zbox ubox unit)
    (source_primitive_bounds z u zbox ubox unit (derivativeDemand e M)) e M le_rfl

theorem actual_source_energy_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (k M : ℕ) :
    FiniteBound (sourceEngineEnergy k) M (sourceEnergyArray k) (z,WithLp.toLp 2 u) := by
  have hx:=sourceUnit_admitted z u zbox ubox unit
  have actual:=actual_source_expression_budget z u zbox ubox unit (moyalNormalizedEnergy k) M
  intro m hm w
  have read:=congrArg (fun D=>D (slotDirection∘w))
    (moyalNormalizedEnergy_jets k m _ hx)
  have result:=actual m hm w
  rw [read,realCast_jet _ (sourceEngineEnergy_smooth k) m w _ hx,
    Complex.norm_real,Real.norm_eq_abs] at result
  exact result

theorem actual_source_clock_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (k M : ℕ) (a : Fin 4) :
    FiniteBound (sourceEngine (k+1) a (Fin.last (k+1))) M (sourceClockCoefficientArray k a)
      (z,WithLp.toLp 2 u) := by
  have hx:=sourceUnit_admitted z u zbox ubox unit
  have actual:=actual_source_expression_budget z u zbox ubox unit (normalizedClockExpression k a) M
  have germ : arenaEvaluate (normalizedClockExpression k a)=ᶠ[𝓝 (z,WithLp.toLp 2 u)]
      (fun x=>(sourceEngine (k+1) a (Fin.last (k+1)) x : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with x h
    exact normalizedClock_source k a x h
  intro m hm w
  have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  have result:=actual m hm w
  rw [read,realCast_jet _ (sourceEngine_smooth (k+1) a (Fin.last (k+1))) m w _ hx,
    Complex.norm_real,Real.norm_eq_abs] at result
  exact result

def sourceFiveArrays (k : ℕ) (i : Fin 5) : ArrayBound :=
  Fin.lastCases (sourceEnergyArray k) (fun a=>sourceClockCoefficientArray (k-1) a) i

theorem sourceFiveArrays_nonnegative (k : ℕ) (i : Fin 5) (m : ℕ) : 0 ≤ sourceFiveArrays k i m := by
  refine Fin.lastCases ?_ (fun a=>?_) i
  · exact sourceEnergyArray_nonnegative k m
  · simpa only [sourceFiveArrays,Fin.lastCases_castSucc] using sourceClockCoefficientArray_nonnegative (k-1) m a

end LowEnergy.PreparationVacuumNumericSource
