import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerAssemblyFeed
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalNormalizationRows
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailConfigurationMoments

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNumericSource
open PreparationVacuumPrincipalBudget PreparationVacuumCentralBudget PreparationVacuumClockBudget
open PreparationVacuumClockJacobian PreparationVacuumClockSymbol PreparationVacuumDAGCoefficient
open PreparationVacuumCanonicalMoyal PreparationVacuumEngineBudget PreparationVacuumArenaRows
open PreparationVacuumUniformFeed PreparationVacuumCoefficientBudget PreparationVacuumLowerAssembly
open PreparationVacuumPoleCancellation PreparationVacuumReciprocalBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev ArrayBound := PreparationVacuumCentralBudget.ArrayBound

def sourceRatioArray (m : ℕ) : ℝ := (1/2 : ℝ)*productArray tArray (inverseBudget aArray 15) m
def sourceClockInverseZero : ℝ := max 1 (30*aArray 0)
def sourceClockArray : ArrayBound := clockArray sourceRatioArray sourceClockInverseZero

def generatedCentralInputs (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) : PrimitiveInputs (z,WithLp.toLp 2 u) N :=
  actualCentralInputs z u zbox ubox unit N
    (generatedCoefficientInputs _ (sourceUnit_admitted z u zbox ubox unit) zbox N)

theorem generated_central_clock (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) :
    (generatedCentralInputs z u zbox ubox unit N).clock=sourceClockArray := rfl

theorem generated_central_spatial (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) :
    (generatedCentralInputs z u zbox ubox unit N).spatial=sArray := rfl

theorem generated_central_A0 (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) :
    (generatedCentralInputs z u zbox ubox unit N).A0=aArray 0 := rfl

def sourceLeafArrays (d : Fin 3) (j : Fin 14) : ArrayBound :=
  Fin.lastCases (principalLeafArray j) (fun e=>lowerLeafArray e j) d

theorem sourceLeafArrays_nonnegative (d : Fin 3) (j : Fin 14) (m : ℕ) :
    0 ≤ sourceLeafArrays d j m := by
  refine Fin.lastCases ?_ (fun e=>?_) d
  · exact principalLeafArray_nonnegative j m
  · simpa only [sourceLeafArrays,Fin.lastCases_castSucc] using lowerLeafArray_nonnegative e j m

theorem generated_leaf_arrays (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) :
    fullLeafArrays (generatedLowerInputs N (z,WithLp.toLp 2 u)
      (sourceUnit_admitted z u zbox ubox unit) zbox (by simpa using unit.le.trans (by norm_num : (1 : ℝ) ≤ 4)))=
        sourceLeafArrays := rfl

theorem source_leaf_bounds (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (d : Fin 3) (j : Fin 14) :
    FiniteBound (originalLeaf d j) N (sourceLeafArrays d j) (z,WithLp.toLp 2 u) := by
  have hx:=sourceUnit_admitted z u zbox ubox unit
  have annulus : (∑ i : Fin 100,((WithLp.toLp 2 u) i)^2) ≤ 4 := by
    simpa using unit.le.trans (by norm_num : (1 : ℝ) ≤ 4)
  exact fullLeafArrays_bounds z u zbox ubox unit N
    (generatedCoefficientInputs _ hx zbox N) (generatedLowerInputs N _ hx zbox annulus) d j

def sourceInverseArrays (i : Fin 3) : ArrayBound :=
  if i=0 then inverseBudget sourceClockArray sourceClockInverseZero else
  if i=1 then sourceTInverseBudget tArray else
    sourceDetInverseBudget (fun n=>6*powerArray (fun n=>3*sArray n+sArray n) 3 n)

def sourceCentralArray (c : NormalizedCoefficient) : ArrayBound :=
  coefficientArray (fieldArrays sourceClockArray sArray) sourceInverseArrays (cancelCoefficient c)

def sourcePrimitiveArrays : PrimitiveArrays 0 where
  leaf:=sourceLeafArrays
  clock _ a:=if a=0 then sourceClockArray else (fun _=>0)
  central:=sourceCentralArray

theorem generated_primitive_arrays (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) :
    canceledSourceArrays (generatedCentralInputs z u zbox ubox unit N) sourceLeafArrays=
      sourcePrimitiveArrays := rfl

theorem source_primitive_bounds (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) :
    PrimitiveBounds sourcePrimitiveArrays N (z,WithLp.toLp 2 u) :=
  canceledSourceArrays_bounds z u zbox ubox unit N
    (generatedCentralInputs z u zbox ubox unit N) sourceLeafArrays
    (source_leaf_bounds z u zbox ubox unit N)

theorem source_primitive_nonnegative : PrimitiveNonnegative sourcePrimitiveArrays := by
  have zbox : ∀ i,|flatSource i-flatSource i| ≤ sourceRadius := by intro i; norm_num [sourceRadius]
  have ubox : ∀ i,|sourceUnitMomentum i-sourceUnitMomentum i| ≤ sourceRadius := by
    intro i; norm_num [sourceRadius]
  exact canceledSourceArrays_nonnegative
    (generatedCentralInputs flatSource sourceUnitMomentum zbox ubox sourceUnitMomentum_unit 0)
    sourceLeafArrays sourceLeafArrays_nonnegative

end LowEnergy.PreparationVacuumNumericSource
