import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceRestGaugeVertex
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationOriginalFieldPoleReturn
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumElectromagneticIdentity
open SourcePropagationNativeActionHessian SourcePropagationConstrainedPoleReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn Polynomial Filter
open scoped BigOperators Matrix Topology
abbrev RestPairIndex:=RestStateIndex×RestStateIndex
abbrev FieldPolynomialMatrix:=Matrix (Fin 289) (Fin 289) ℂ[X]

/-- The original sparse field action is lifted coefficientwise, with spatial variables fixed. -/
def sourceFieldTimeTerm (spatial : Fin 3→ℂ) (term : SourceTerm) : FieldPolynomialMatrix:=
  Matrix.single term.row term.column
    (C (coefficientValue term.coefficient*spatial 0^term.powers.first*
      spatial 1^term.powers.second*spatial 2^term.powers.third)*X^term.powers.temporal)

def sourceFieldTimeMatrix (spatial : Fin 3→ℂ) (terms : List SourceTerm) : FieldPolynomialMatrix:=
  (terms.map (sourceFieldTimeTerm spatial)).sum

private theorem sourceFieldTimeTerm_eval (spatial : Fin 3→ℂ) (lambda : ℂ) (term : SourceTerm) :
    (sourceFieldTimeTerm spatial term).map (evalRingHom lambda)=term.matrix (fullMomentum spatial lambda) := by
  ext row column
  simp only [sourceFieldTimeTerm,SourceTerm.matrix,Matrix.map_apply,Matrix.single_apply]
  split_ifs
  · simp only [coe_evalRingHom,eval_mul,eval_C,eval_pow,eval_X,Powers.value]
    change _=coefficientValue term.coefficient*(lambda^term.powers.temporal*
      spatial 0^term.powers.first*spatial 1^term.powers.second*spatial 2^term.powers.third)
    ring
  · simp

theorem sourceFieldTimeMatrix_eval (spatial : Fin 3→ℂ) (lambda : ℂ) (terms : List SourceTerm) :
    (sourceFieldTimeMatrix spatial terms).map (evalRingHom lambda)=sourceMatrix terms (fullMomentum spatial lambda) := by
  induction terms with
  | nil=>ext row column;simp [sourceFieldTimeMatrix,sourceMatrix]
  | cons term terms ih=>
    ext row column
    have initial:=congrFun (congrFun (sourceFieldTimeTerm_eval spatial lambda term) row) column
    have rest:=congrFun (congrFun ih row) column
    simp only [sourceFieldTimeMatrix,List.map_cons,List.sum_cons,Matrix.map_apply,Matrix.add_apply,
      map_add,sourceMatrix] at initial rest ⊢
    exact congrArg₂ (·+·) initial rest

def sourceFieldTimeExtended (spatial : Fin 3→ℂ) : FieldPolynomialMatrix:=
  sourceFieldTimeMatrix spatial activeTerms+(1-activeProjection).map C

theorem sourceFieldTimeExtended_eval (spatial : Fin 3→ℂ) (lambda : ℂ) :
    (sourceFieldTimeExtended spatial).map (evalRingHom lambda)=extendedKernel (fullMomentum spatial lambda) := by
  have active:=sourceFieldTimeMatrix_eval spatial lambda activeTerms
  ext row column
  have entry:=congrFun (congrFun active row) column
  simp only [sourceFieldTimeExtended,Matrix.map_apply,Matrix.add_apply,coe_evalRingHom,eval_add,eval_C,
    extendedKernel,activeKernel]
  exact congrArg₂ (·+·) entry rfl

def sourceFieldTimeDeterminant (spatial : Fin 3→ℂ) : ℂ[X]:=(sourceFieldTimeExtended spatial).det

theorem sourceFieldTimeDeterminant_eval (spatial : Fin 3→ℂ) (lambda : ℂ) :
    (sourceFieldTimeDeterminant spatial).eval lambda=originalFieldDenominator (fullMomentum spatial lambda) := by
  exact ((evalRingHom lambda).map_det (sourceFieldTimeExtended spatial)).trans
    (congrArg Matrix.det (sourceFieldTimeExtended_eval spatial lambda))

def sourceFieldAnchorSpatial : Fin 3→ℂ:=fun axis=>generatedRegularPoint.val axis.succ

def sourceFieldAnchorTime : ℂ:=generatedRegularPoint.val 0

theorem sourceFieldAnchor_regular : fullMomentum sourceFieldAnchorSpatial sourceFieldAnchorTime∈regularSource := by
  convert! generatedRegularPoint.property using 1

theorem sourceFieldTimeDeterminant_nonzero (spatial : Fin 3→ℂ) (lambda : ℂ)
    (regular : fullMomentum spatial lambda∈regularSource) : sourceFieldTimeDeterminant spatial≠0 := by
  intro zero
  have evaluated:=sourceFieldTimeDeterminant_eval spatial lambda
  rw [zero,eval_zero] at evaluated
  exact (isUnit_iff_ne_zero.mp regular) evaluated.symm

theorem sourceFieldTimeDeterminant_anchor_nonzero : sourceFieldTimeDeterminant sourceFieldAnchorSpatial≠0 :=
  sourceFieldTimeDeterminant_nonzero sourceFieldAnchorSpatial sourceFieldAnchorTime sourceFieldAnchor_regular

def sourceRestFieldDenominatorOrder (spatial : Fin 3→ℂ) (pole : ℂ) : ℕ:=
  (sourceFieldTimeDeterminant spatial).rootMultiplicity pole

def sourceRestFieldPoleQuotient (spatial : Fin 3→ℂ) (pole : ℂ) : ℂ[X]:=
  sourceFieldTimeDeterminant spatial /ₘ (X-C pole)^sourceRestFieldDenominatorOrder spatial pole

theorem sourceRestFieldPole_factor (spatial : Fin 3→ℂ) (pole lambda : ℂ) :
    originalFieldDenominator (fullMomentum spatial lambda)=
      (lambda-pole)^sourceRestFieldDenominatorOrder spatial pole*(sourceRestFieldPoleQuotient spatial pole).eval lambda := by
  rw [←sourceFieldTimeDeterminant_eval]
  have factor:=pow_mul_divByMonic_rootMultiplicity_eq (sourceFieldTimeDeterminant spatial) pole
  have evaluated:=congrArg (eval lambda) factor
  simpa only [eval_mul,eval_pow,eval_sub,eval_X,eval_C,
    sourceRestFieldDenominatorOrder,sourceRestFieldPoleQuotient] using evaluated.symm

theorem sourceRestFieldPoleQuotient_nonzero (spatial : Fin 3→ℂ) (pole : ℂ)
    (nonzero : sourceFieldTimeDeterminant spatial≠0) : (sourceRestFieldPoleQuotient spatial pole).eval pole≠0 :=
  eval_divByMonic_pow_rootMultiplicity_ne_zero pole nonzero

def sourceRestOrdinaryFieldTensor (p : regularSource) (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) :
    Matrix RestPairIndex RestPairIndex ℂ:=fun reader driver=>
  ∑ field : Fin 289,actualRestNativeComplexForcingCovector point reader.1 reader.2 field*
    actualRestNativeGaugeField p point driver.1 driver.2 field

def sourceRestClearedFieldTensor (p : Fin 4→ℂ) (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) :
    Matrix RestPairIndex RestPairIndex ℂ:=fun reader driver=>
  ∑ field : Fin 289,actualRestNativeComplexForcingCovector point reader.1 reader.2 field*
    (originalClearedGreen p*ᵥactualRestNativeComplexForcingCovector point driver.1 driver.2) field

theorem sourceRestClearedFieldTensor_generated (p : regularSource)
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) (reader driver : RestPairIndex) :
    originalFieldDenominator p.val*sourceRestOrdinaryFieldTensor p point reader driver=
      sourceRestClearedFieldTensor p.val point reader driver := by
  unfold sourceRestOrdinaryFieldTensor sourceRestClearedFieldTensor actualRestNativeGaugeField
    PreparationVacuumOriginalGreenFeedback.sourceField
  rw [Finset.mul_sum]
  have clear:=congrArg (fun matrix : FieldMatrix=>matrix*ᵥactualRestNativeComplexForcingCovector point driver.1 driver.2)
    (originalGreen_denominator p)
  rw [Matrix.smul_mulVec] at clear
  apply Finset.sum_congr rfl
  intro field _
  have entry:=congrFun clear field
  rw [mul_left_comm]
  exact congrArg (actualRestNativeComplexForcingCovector point reader.1 reader.2 field*·) entry


def sourceRestNormalizedFieldTensor (spatial : Fin 3→ℂ) (pole lambda : ℂ)
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) : Matrix RestPairIndex RestPairIndex ℂ:=
  ((sourceRestFieldPoleQuotient spatial pole).eval lambda)⁻¹ •
    sourceRestClearedFieldTensor (fullMomentum spatial lambda) point

def sourceRestFieldLeadingTensor (spatial : Fin 3→ℂ) (pole : ℂ)
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) : Matrix RestPairIndex RestPairIndex ℂ:=
  sourceRestNormalizedFieldTensor spatial pole pole point

theorem sourceRestFieldDenominatorOrder_positive (spatial : Fin 3→ℂ) (pole : ℂ)
    (nonzero : sourceFieldTimeDeterminant spatial≠0)
    (root : originalFieldDenominator (fullMomentum spatial pole)=0) :
    0<sourceRestFieldDenominatorOrder spatial pole := by
  apply (rootMultiplicity_pos nonzero).mpr
  exact (sourceFieldTimeDeterminant_eval spatial pole).trans root

theorem sourceRestFieldTensor_scaled (spatial : Fin 3→ℂ) (pole : ℂ)
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint)
    (lambda : ℂ) (regular : fullMomentum spatial lambda∈regularSource) (reader driver : RestPairIndex) :
    (lambda-pole)^sourceRestFieldDenominatorOrder spatial pole*
      sourceRestOrdinaryFieldTensor ⟨fullMomentum spatial lambda,regular⟩ point reader driver=
      sourceRestNormalizedFieldTensor spatial pole lambda point reader driver := by
  have factor:=sourceRestFieldPole_factor spatial pole lambda
  have denominator : originalFieldDenominator (fullMomentum spatial lambda)≠0 := isUnit_iff_ne_zero.mp regular
  have quotient : (sourceRestFieldPoleQuotient spatial pole).eval lambda≠0 := by
    intro zero
    rw [zero,mul_zero] at factor
    exact denominator factor
  have cleared:=sourceRestClearedFieldTensor_generated ⟨fullMomentum spatial lambda,regular⟩ point reader driver
  rw [factor] at cleared
  change _=((sourceRestFieldPoleQuotient spatial pole).eval lambda)⁻¹*
    sourceRestClearedFieldTensor (fullMomentum spatial lambda) point reader driver
  field_simp [quotient]
  linear_combination cleared

private theorem clearedTensor_continuous (spatial : Fin 3→ℂ)
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) (reader driver : RestPairIndex) :
    Continuous (fun lambda : ℂ=>sourceRestClearedFieldTensor (fullMomentum spatial lambda) point reader driver) := by
  have path : Continuous (fun lambda : ℂ=>fullMomentum spatial lambda) := by
    apply continuous_pi
    intro mu
    refine Fin.cases continuous_id (fun _=>continuous_const) mu
  unfold sourceRestClearedFieldTensor Matrix.mulVec dotProduct
  apply continuous_finsetSum
  intro field _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro index _
  exact ((originalClearedGreen_continuous.comp path).matrix_elem field index).mul continuous_const

theorem sourceRestFieldLeadingTensor_generated (spatial : Fin 3→ℂ) (pole : ℂ)
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint)
    (nonzero : sourceFieldTimeDeterminant spatial≠0) (reader driver : RestPairIndex) :
    Tendsto (fun lambda : ℂ=>sourceRestNormalizedFieldTensor spatial pole lambda point reader driver)
      (𝓝 pole) (𝓝 (sourceRestFieldLeadingTensor spatial pole point reader driver)) := by
  have scalar : ContinuousAt (fun lambda : ℂ=>((sourceRestFieldPoleQuotient spatial pole).eval lambda)⁻¹) pole :=
    (sourceRestFieldPoleQuotient spatial pole).continuousAt.inv₀ (sourceRestFieldPoleQuotient_nonzero spatial pole nonzero)
  exact scalar.tendsto.mul (clearedTensor_continuous spatial point reader driver).continuousAt.tendsto


abbrev SourceRestRegularTime (spatial : Fin 3→ℂ):={lambda : ℂ // fullMomentum spatial lambda∈regularSource}

theorem sourceRestField_regular_nearPole (spatial : Fin 3→ℂ) (pole : ℂ)
    (nonzero : sourceFieldTimeDeterminant spatial≠0) :
    ∀ᶠ lambda in 𝓝[≠] pole,fullMomentum spatial lambda∈regularSource := by
  have quotient : ∀ᶠ lambda in 𝓝 pole,(sourceRestFieldPoleQuotient spatial pole).eval lambda≠0 :=
    (sourceRestFieldPoleQuotient spatial pole).continuousAt.eventually_ne
      (sourceRestFieldPoleQuotient_nonzero spatial pole nonzero)
  filter_upwards [quotient.filter_mono inf_le_left,self_mem_nhdsWithin] with lambda regular away
  apply isUnit_iff_ne_zero.mpr
  change originalFieldDenominator (fullMomentum spatial lambda)≠0
  rw [sourceRestFieldPole_factor]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr away)) regular

theorem sourceRestField_regularPoleFilter_nonempty (spatial : Fin 3→ℂ) (pole : ℂ)
    (nonzero : sourceFieldTimeDeterminant spatial≠0) :
    (Filter.comap (Subtype.val : SourceRestRegularTime spatial→ℂ) (𝓝[≠] pole)).NeBot := by
  apply Filter.NeBot.comap_of_range_mem (inferInstance : (𝓝[≠] pole).NeBot)
  rw [Subtype.range_coe_subtype]
  change ∀ᶠ lambda in 𝓝[≠] pole,fullMomentum spatial lambda∈regularSource
  exact sourceRestField_regular_nearPole spatial pole nonzero

theorem sourceRestOrdinaryFieldTensor_poleLeading (spatial : Fin 3→ℂ) (pole : ℂ)
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint)
    (nonzero : sourceFieldTimeDeterminant spatial≠0) (reader driver : RestPairIndex) :
    Tendsto (fun lambda : SourceRestRegularTime spatial=>
      (lambda.val-pole)^sourceRestFieldDenominatorOrder spatial pole*
        sourceRestOrdinaryFieldTensor ⟨fullMomentum spatial lambda.val,lambda.property⟩ point reader driver)
      (Filter.comap Subtype.val (𝓝[≠] pole)) (𝓝 (sourceRestFieldLeadingTensor spatial pole point reader driver)) := by
  have inclusion : Tendsto (Subtype.val : SourceRestRegularTime spatial→ℂ)
      (Filter.comap Subtype.val (𝓝[≠] pole)) (𝓝 pole) :=
    Filter.map_comap_le.trans inf_le_left
  have actual:=(sourceRestFieldLeadingTensor_generated spatial pole point nonzero reader driver).comp inclusion
  apply Tendsto.congr' _ actual
  filter_upwards [] with lambda
  exact (sourceRestFieldTensor_scaled spatial pole point lambda.val lambda.property reader driver).symm


def sourceRestFieldLeadingMode (spatial : Fin 3→ℂ) (pole : ℂ)
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) (driver : RestPairIndex) : Fin 289→ℂ:=
  ((sourceRestFieldPoleQuotient spatial pole).eval pole)⁻¹ •
    (originalClearedGreen (fullMomentum spatial pole)*ᵥactualRestNativeComplexForcingCovector point driver.1 driver.2)

theorem sourceRestFieldLeadingMode_native (spatial : Fin 3→ℂ) (pole : ℂ)
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) (driver : RestPairIndex)
    (root : originalFieldDenominator (fullMomentum spatial pole)=0) :
    nativeFourierHessian nativeHessian (fullMomentum spatial pole)*ᵥsourceRestFieldLeadingMode spatial pole point driver=0 := by
  rw [nativeActionFourierHessian_original,sourceRestFieldLeadingMode,Matrix.mulVec_smul,
    Matrix.mulVec_mulVec,originalClearedGreen_equation,root,zero_smul,Matrix.zero_mulVec,smul_zero]

theorem sourceRestFieldLeadingTensor_mode (spatial : Fin 3→ℂ) (pole : ℂ)
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) (reader driver : RestPairIndex) :
    sourceRestFieldLeadingTensor spatial pole point reader driver=
      ∑ field : Fin 289,actualRestNativeComplexForcingCovector point reader.1 reader.2 field*
        sourceRestFieldLeadingMode spatial pole point driver field := by
  unfold sourceRestFieldLeadingTensor sourceRestNormalizedFieldTensor sourceRestClearedFieldTensor sourceRestFieldLeadingMode
  simp only [Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro field _
  ring

theorem sourceRestFieldLeadingTensor_zero_of_annihilated (spatial : Fin 3→ℂ) (pole : ℂ)
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) (reader driver : RestPairIndex)
    (annihilated : sourceRestFieldLeadingMode spatial pole point driver=0) :
    sourceRestFieldLeadingTensor spatial pole point reader driver=0 := by
  rw [sourceRestFieldLeadingTensor_mode,annihilated]
  simp


def sourceRestFieldDensityRead
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint)
    (reader : RestPairIndex) (field : Fin 289→ℂ) : ℂ:=
  (actualRestNativeGaugeQuadrature 0 point reader.1 reader.2 (fun index=>(field index).re)-
    actualRestNativeGaugeQuadrature 1 point reader.1 reader.2 (fun index=>(field index).im):ℝ)+
  Complex.I*(actualRestNativeGaugeQuadrature 0 point reader.1 reader.2 (fun index=>(field index).im)+
    actualRestNativeGaugeQuadrature 1 point reader.1 reader.2 (fun index=>(field index).re):ℝ)

theorem sourceRestFieldDensityRead_generated
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint)
    (reader : RestPairIndex) (field : Fin 289→ℂ) :
    sourceRestFieldDensityRead point reader field=
      ∑ index : Fin 289,actualRestNativeComplexForcingCovector point reader.1 reader.2 index*field index := by
  have readable (part : Fin 2) (force : Field289) : actualRestNativeGaugeQuadrature part point reader.1 reader.2 force=
      ∑ index : Fin 289,force index*actualRestNativeForcingCovector part point reader.1 reader.2 index :=
    (actualRestNativeForcingCovector_generated part point reader.1 reader.2 force).symm
  unfold sourceRestFieldDensityRead
  simp only [readable]
  apply Complex.ext
  · simp [actualRestNativeComplexForcingCovector,Complex.mul_re,Finset.sum_sub_distrib]
    simp only [mul_comm]
  · simp [actualRestNativeComplexForcingCovector,Complex.mul_im,Finset.sum_add_distrib]
    simp only [mul_comm]

theorem sourceRestOrdinaryFieldTensor_density (p : regularSource)
    (point : SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) (reader driver : RestPairIndex) :
    sourceRestOrdinaryFieldTensor p point reader driver=
      sourceRestFieldDensityRead point reader (actualRestNativeGaugeField p point driver.1 driver.2) :=
  (sourceRestFieldDensityRead_generated point reader _).symm

end LowEnergy.PreparationVacuumElectromagneticIdentity
