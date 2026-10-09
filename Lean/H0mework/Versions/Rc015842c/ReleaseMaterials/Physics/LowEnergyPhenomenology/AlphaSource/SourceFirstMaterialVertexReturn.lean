import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstDifferenceCoreWard

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstGaugeMaterialDifference
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalNormalizedFullField
open PreparationVacuumNativeFieldInjection PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumActualFieldQuantization PreparationVacuumOriginalGreenFeedback
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussNativeMatter GaussHistoryHilbert GaussQuantumMultiplier
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair FullQuantum.CoframeResponse FullQuantum.StateGreen
open PointwiseLorentzianCoframeJet PointwiseDiracSpinConnectionLift
open Filter Set
open scoped BigOperators Matrix Topology ContDiff Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalSourceHarmonicReturn
open PreparationVacuumPhysicalCharacteristic ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource FullQuantum FullSpace PreparationVacuumLowerClassical

open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumNativeSlowCoupling PreparationVacuumPhysicalFeedback
open PreparationPhysicalResponseChargeGrading PreparationVacuumLorentzFieldInjection
open PreparationVacuumPhysicalChargedFieldFactor PreparationPhysicalPoleChargeMatrix
open GaussFockLift GaussCoreHilbert PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalNativePhaseChargeInventory
open scoped InnerProductSpace

open PreparationPhysicalFirstPoleGaugeRemainder PreparationPhysicalMaterialChargeTorque
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalCoframeChargeSelection PreparationPhysicalCoframeChargeExchange
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice CanonicalGradedCharge GaussCoreDifferential GaussQuantumMultiplier
open GaussFockPair GaussLiveMomentum GaussNativePotential
open scoped ContDiff

open NativeHistoryGrade GaussUnitaryHistory CanonicalPhysicalSpatial CanonicalPhysicalWardCore
open PreparationVacuumGradedTransport PreparationVacuumUncutYukawa PreparationPhysicalActualLegNormalization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalPoleAmputation PreparationPhysicalChargedScatteringPoleReturn
open GaussFockWeights GaussDensityCore MeasureTheory PreparationVacuumFieldConstraintResponse PreparationVacuumYukawaTransport
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointResolvent actualC gradedTest

/-- The actual native two-leg correction is an explicit original Gaussian configuration integral. -/
def sourceFirstNativeSandwichRead (v w : GaussLiveMomentum.Ambient) (c : SourceCoordinateSlice→ℝ)
    (f g : QuantumTest) : ℂ :=
  (∫z,inner ℂ (weight (fun N=>complexDensity N z) (covariantMomentum v f z))
      ((c z:ℂ) • nativeFock (lie sourceFirstBrokenLie (inverseL z w).1) (g z))
    ∂GaussHistoryHilbert.configurationMeasure)-
  (∫z,inner ℂ (weight (fun N=>complexDensity N z)
      (nativeFock (lie sourceFirstBrokenLie (inverseL z v).1) (f z)))
      ((c z:ℂ) • covariantMomentum w g z) ∂GaussHistoryHilbert.configurationMeasure)

private theorem native_sandwich_read (v w : GaussLiveMomentum.Ambient) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f g : QuantumTest) :
    sourceFirstNativeSandwich v w c smooth f g=sourceFirstNativeSandwichRead v w c f g := by
  simp only [sourceFirstNativeSandwich,sourcePair_integral,sourceFirstNativeSandwichRead]
  congr 1
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z=>by
      simp only [densityPair,GaussNativeForm.multiply_apply,sourceFirstCovariantTransfer_generated]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z=>by
      simp only [densityPair,GaussNativeForm.multiply_apply,sourceFirstCovariantTransfer_generated]

def sourceFirstNativeRead (f g : QuantumTest) : ℂ :=
  (1/2:ℂ)*(∑a : GaussNativeForm.ScalarIndex,
    sourceFirstNativeSandwichRead (GaussNativeForm.scalarDirection a) (GaussNativeForm.scalarDirection a)
      GaussNativeEnergy.scalarWeight f g)+
  (1/2:ℂ)*(∑a : GaussNativeForm.LieIndex,∑i : Fin 3,∑j : Fin 3,
    sourceFirstNativeSandwichRead (GaussNativeForm.gaugeDirection i a) (GaussNativeForm.gaugeDirection j a)
      (fun z=>GaussNativeEnergy.gaugeWeight z i j) f g)

private theorem native_read (f g : QuantumTest) : sourceFirstNativeTorque f g=sourceFirstNativeRead f g := by
  simp only [sourceFirstNativeTorque,sourceFirstNativeRead,native_sandwich_read]

/-- The full matter connection enters the same weighted Gaussian integral. -/
def sourceFirstMatterRead (f g : QuantumTest) : ℂ :=
  ∫z,inner ℂ (weight (fun N=>complexDensity N z) (f z))
    (Complex.I • quantized (sourceFirstMatterTransferMatrix z) (g z)) ∂GaussHistoryHilbert.configurationMeasure

private theorem matter_read (f g : QuantumTest) :
    sourcePair f (sourceFirstMatterTransferCore g)=sourceFirstMatterRead f g := by
  rw [sourcePair_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z=>by
    simp only [densityPair,sourceFirstMatterTransfer_generated]

/-- The physicalSpan discrepancy is an actual finite-preparation difference, with both endpoints kept. -/
def sourceFirstSpanDifference (F : GaussUnitaryHistory.Index) (g : NativeHistoryGrade.Label) (x : H) : QuantumTest :=
  gradedTest 0 F g (sourceFirstDifference x)-sourceFirstDifferenceCore (gradedTest 0 F g x)

theorem sourceFirstCompressionDifference_return (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x ((actualC 0 F*sourceFirstDifference-sourceFirstDifference*actualC 0 F) y)=
      ∑g : NativeHistoryGrade.Label,
        (sourceFirstNativeRead (gradedTest 0 F g x) (gradedTest 0 F g y)+
          sourceFirstMatterRead (gradedTest 0 F g x) (gradedTest 0 F g y)+
          sourcePair (gradedTest 0 F g x) (GaussDiagonalHistory.diagonalAction (sourceFirstSpanDifference F g y))-
          sourcePair (sourceFirstSpanDifference F g x) (GaussDiagonalHistory.diagonalAction (gradedTest 0 F g y))) := by
  simp only [sub_apply,mul_apply_eq_comp,inner_sub_right]
  rw [←sourceFirstDifference_pair,sourcePhysicalCompression_pair,sourcePhysicalCompression_pair,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g _
  have right : gradedTest 0 F g (sourceFirstDifference y)=
      sourceFirstDifferenceCore (gradedTest 0 F g y)+sourceFirstSpanDifference F g y := by
    unfold sourceFirstSpanDifference
    abel
  have left : gradedTest 0 F g (sourceFirstDifference x)=
      sourceFirstDifferenceCore (gradedTest 0 F g x)+sourceFirstSpanDifference F g x := by
    unfold sourceFirstSpanDifference
    abel
  rw [right,left,map_add]
  have torque:=sourceFirstDifference_diagonalForm (gradedTest 0 F g x) (gradedTest 0 F g y)
  rw [native_read,matter_read] at torque
  have paired:=sourceFirstDifferenceCore_pair (gradedTest 0 F g x) (GaussDiagonalHistory.diagonalAction (gradedTest 0 F g y))
  simp only [sourcePair,map_add,map_sub,inner_add_left,inner_add_right,inner_sub_right] at torque paired ⊢
  rw [paired]
  linear_combination torque

/-- The full scalar supplement returns at arbitrary Hilbert states through the original core approximation, with the actual retainer fixed. -/
theorem sourceFirstRetainedDifference_whole (phi : CanonicalGradedLocalCurrent.Localizer) (x y : H) :
    Tendsto (fun D : GaussUnitaryHistory.Index=>sourcePair (sourceTestApprox D x)
      (sourceFirstRetainedDifferenceCore phi (sourceTestApprox D y))) GaussUnitaryHistory.sourceFilter
      (𝓝 (inner ℂ x ((uncutOperator 0 phi 0*sourceFirstDifference-sourceFirstDifference*uncutOperator 0 phi 0) y))) := by
  have H:=(same_source_approximation x).inner (𝕜:=ℂ)
    ((uncutOperator 0 phi 0*sourceFirstDifference-sourceFirstDifference*uncutOperator 0 phi 0).continuous.tendsto y |>.comp (same_source_approximation y))
  simpa only [Function.comp_apply,sourceFirstRetainedDifference_return,sourcePair] using H

def sourceFirstMaterialDifferenceRead (F : GaussUnitaryHistory.Index) (x y : H) : ℂ :=
  (∑g : NativeHistoryGrade.Label,
    (sourceFirstNativeRead (gradedTest 0 F g x) (gradedTest 0 F g y)+
      sourceFirstMatterRead (gradedTest 0 F g x) (gradedTest 0 F g y)+
      sourcePair (gradedTest 0 F g x) (GaussDiagonalHistory.diagonalAction (sourceFirstSpanDifference F g y))-
      sourcePair (sourceFirstSpanDifference F g x) (GaussDiagonalHistory.diagonalAction (gradedTest 0 F g y))))+
    inner ℂ x ((uncutOperator 0 (finiteRetainer 0 F) 0*sourceFirstDifference-
      sourceFirstDifference*uncutOperator 0 (finiteRetainer 0 F) 0) y)

theorem sourceFirstMaterialDifference_return (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x ((jointGenerator 0 F 0 0*sourceFirstDifference-sourceFirstDifference*jointGenerator 0 F 0 0) y)=
      sourceFirstMaterialDifferenceRead F x y := by
  rw [sourceMaterialJoint_base]
  have split : (actualC 0 F+uncutOperator 0 (finiteRetainer 0 F) 0)*sourceFirstDifference-
      sourceFirstDifference*(actualC 0 F+uncutOperator 0 (finiteRetainer 0 F) 0)=
      (actualC 0 F*sourceFirstDifference-sourceFirstDifference*actualC 0 F)+
      (uncutOperator 0 (finiteRetainer 0 F) 0*sourceFirstDifference-sourceFirstDifference*uncutOperator 0 (finiteRetainer 0 F) 0) := by
    simp only [add_mul,mul_add]
    abel
  rw [split,add_apply,inner_add_right,sourceFirstCompressionDifference_return]
  rfl

/-- The original actualQ material response and the computed D response form the complete first-pole charge response. -/
def sourceFirstMaterialChargeRead (F : GaussUnitaryHistory.Index) (x y : H) : ℂ :=
  sourceMaterialChargeRead F x y+sourceFirstMaterialDifferenceRead F x y

theorem sourceFirstMaterialCharge_return (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x ((jointGenerator 0 F 0 0*sourceFirstCharge-sourceFirstCharge*jointGenerator 0 F 0 0) y)=
      sourceFirstMaterialChargeRead F x y := by
  have charge : sourceFirstCharge=sourceActualGaussCharge+sourceFirstDifference := by
    unfold sourceFirstDifference
    abel
  rw [charge]
  have split : jointGenerator 0 F 0 0*(sourceActualGaussCharge+sourceFirstDifference)-
      (sourceActualGaussCharge+sourceFirstDifference)*jointGenerator 0 F 0 0=
      (jointGenerator 0 F 0 0*sourceActualGaussCharge-sourceActualGaussCharge*jointGenerator 0 F 0 0)+
      (jointGenerator 0 F 0 0*sourceFirstDifference-sourceFirstDifference*jointGenerator 0 F 0 0) := by
    noncomm_ring
  rw [split,add_apply,inner_add_right,sourceMaterialChargeRead_return,sourceFirstMaterialDifference_return]
  rfl

/-- The original action quantum supplies the absolute first-pole charge. -/
def sourceFirstAbsoluteCharge : H→L[ℂ]H := (Stage10.ActionNormalization.phaseMomentum:ℂ) • sourceFirstCharge

/-- Both true material Green legs sandwich the complete evaluated first-pole charge transfer. -/
def sourceFirstChargeResponse (q : PhysicalResponsePoint) : H→L[ℂ]H :=
  jointResolvent 0 q.F q.z 0*(jointGenerator 0 q.F 0 0*sourceFirstAbsoluteCharge-
    sourceFirstAbsoluteCharge*jointGenerator 0 q.F 0 0)*jointResolvent 0 q.F q.w 0

theorem sourceFirstChargeResponse_return (q : PhysicalResponsePoint) (x y : H) :
    inner ℂ x (sourceFirstChargeResponse q y)=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceFirstMaterialChargeRead q.F
        ((jointResolvent 0 q.F q.z 0).adjoint x) (jointResolvent 0 q.F q.w 0 y) := by
  simp only [sourceFirstChargeResponse,sourceFirstAbsoluteCharge,mul_smul_comm,smul_mul_assoc,
    mul_apply_eq_comp]
  rw [←ContinuousLinearMap.adjoint_inner_left]
  have material:=sourceFirstMaterialCharge_return q.F
    ((jointResolvent 0 q.F q.z 0).adjoint x) (jointResolvent 0 q.F q.w 0 y)
  simp only [sub_apply,inner_sub_right] at material
  simp only [sub_apply,smul_apply,inner_sub_right,inner_smul_right]
  linear_combination (Stage10.ActionNormalization.phaseMomentum:ℂ)*material

open Lean Elab Term in
elab "paidFirstInverseWard%" : term => do
  let wanted:=`LowEnergy.PreparationPhysicalActualNoetherVertexReturn.inverse_ward
  let candidates:=(←getEnv).constants.toList.filter fun (name,_)=>
    name.toString.startsWith "_private.H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceAbsoluteNoetherVertex." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return ←Lean.Meta.mkConstWithFreshMVarLevels name
  | _=>throwError "Expected unique original SourceAbsoluteNoetherVertex.inverse_ward"

theorem sourceFirstAbsoluteCharge_prepared (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2) :
    sourceFirstAbsoluteCharge (sourceChargedGaussPrepared epsilon precision side edge)=
      ((Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge edge:ℂ)) •
        sourceChargedGaussPrepared epsilon precision side edge := by
  rw [sourceFirstAbsoluteCharge,smul_apply,sourceFirstCharge_prepared,smul_smul]

/-- The actual inverse mouths fix the signs before external normalization. -/
theorem sourceFirstCharge_ward (q : PhysicalResponsePoint) (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w) • (jointResolvent 0 q.F q.z 0*sourceFirstAbsoluteCharge*jointResolvent 0 q.F q.w 0)=
      jointResolvent 0 q.F q.z 0*sourceFirstAbsoluteCharge-sourceFirstAbsoluteCharge*jointResolvent 0 q.F q.w 0+
        sourceFirstChargeResponse q := by
  exact (paidFirstInverseWard%) _ _ _ _ _ _ _
    (sourceMaterialInverse_left 0 q.F q.z left) (sourceMaterialInverse_right 0 q.F q.w right)

private theorem first_charge_ends (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (A : H→L[ℂ]H) :
    sourceQuantumChargedRead q sL eL sR eR (A*sourceFirstCharge)=
        (sourceActualPhaseCharge eR:ℂ)*sourceQuantumChargedRead q sL eL sR eR A ∧
      sourceQuantumChargedRead q sL eL sR eR (sourceFirstCharge*A)=
        (sourceActualPhaseCharge eL:ℂ)*sourceQuantumChargedRead q sL eL sR eR A := by
  constructor
  · change inner ℂ (sourceChargedGaussPrepared q.epsilon q.precision sL eL)
      (A (sourceFirstCharge (sourceChargedGaussPrepared q.epsilon q.precision sR eR)))=_
    rw [sourceFirstCharge_prepared,map_smul,inner_smul_right]
    rfl
  · change inner ℂ (sourceChargedGaussPrepared q.epsilon q.precision sL eL)
      (sourceFirstCharge (A (sourceChargedGaussPrepared q.epsilon q.precision sR eR)))=_
    rw [←sourceFirstCharge_pair,sourceFirstCharge_prepared,inner_smul_left]
    simp only [Complex.conj_ofReal]
    rfl

private theorem scaled_ends (L : (H→L[ℂ]H)→L[ℂ]ℂ) (Q A : H→L[ℂ]H) (h l r : ℂ)
    (ends : L (A*Q)=r*L A ∧ L (Q*A)=l*L A) :
    L (A*(h • Q))=h*r*L A ∧ L ((h • Q)*A)=h*l*L A := by
  constructor
  · calc
      L (A*(h • Q))=L (h • (A*Q)) := congrArg L (mul_smul_comm h A Q)
      _=h • L (A*Q) := map_smul L h (A*Q)
      _=h*r*L A := by rw [ends.1]; exact (mul_assoc h r (L A)).symm
  · calc
      L ((h • Q)*A)=L (h • (Q*A)) := congrArg L (smul_mul_assoc h Q A)
      _=h • L (Q*A) := map_smul L h (Q*A)
      _=h*l*L A := by rw [ends.2]; exact (mul_assoc h l (L A)).symm

private theorem first_absolute_ends (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (A : H→L[ℂ]H) :
    sourceQuantumChargedRead q sL eL sR eR (A*sourceFirstAbsoluteCharge)=
        (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eR:ℂ)*
          sourceQuantumChargedRead q sL eL sR eR A ∧
      sourceQuantumChargedRead q sL eL sR eR (sourceFirstAbsoluteCharge*A)=
        (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eL:ℂ)*
          sourceQuantumChargedRead q sL eL sR eR A := by
  exact scaled_ends (sourceQuantumChargedRead q sL eL sR eR) sourceFirstCharge A
    (Stage10.ActionNormalization.phaseMomentum:ℂ) (sourceActualPhaseCharge eL:ℂ)
    (sourceActualPhaseCharge eR:ℂ) (first_charge_ends q sL eL sR eR A)

/-- The actual unfiltered four preparations generate the endpoint charge read; the full transfer remains between Green legs. -/
theorem sourceFirstCharge_preparedWard (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w)*sourceQuantumChargedRead q sL eL sR eR
        (jointResolvent 0 q.F q.z 0*sourceFirstAbsoluteCharge*jointResolvent 0 q.F q.w 0)=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eR:ℂ)*
        sourceQuantumChargedRead q sL eL sR eR (jointResolvent 0 q.F q.z 0)-
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eL:ℂ)*
        sourceQuantumChargedRead q sL eL sR eR (jointResolvent 0 q.F q.w 0)+
      sourceQuantumChargedRead q sL eL sR eR (sourceFirstChargeResponse q) := by
  have H:=congrArg (sourceQuantumChargedRead q sL eL sR eR) (sourceFirstCharge_ward q left right)
  simpa only [map_smul,smul_eq_mul,map_add,map_sub,
    (first_absolute_ends q sL eL sR eR _).1,
    (first_absolute_ends q sL eL sR eR _).2] using H

/-- Actual unit legs, independent dual/primal norms and both material Green operators are retained in the first-pole Ward return. -/
theorem sourceFirstUnitCharge_ward (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w)*sourceActualUnitLegRead q sL eL sR eR sourceFirstAbsoluteCharge=
      sourceActualLegNormalization q sL eL sR eR*
        ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w)*
        ((Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eR:ℂ)*
            sourceQuantumChargedRead q sL eL sR eR (jointResolvent 0 q.F q.z 0)-
          (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eL:ℂ)*
            sourceQuantumChargedRead q sL eL sR eR (jointResolvent 0 q.F q.w 0)+
          sourceQuantumChargedRead q sL eL sR eR (sourceFirstChargeResponse q)) := by
  rw [sourceActualUnitLegRead_vertex q sL eL sR eR left right]
  have H:=sourceFirstCharge_preparedWard q sL eL sR eR left right
  linear_combination (sourceActualLegNormalization q sL eL sR eR*
    ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w))*H

/-- D vanishes on the bare source column but its complete two-Green, independent-dual leg correction remains observable. -/
theorem sourceFirstUnitDifference_return (q : PhysicalResponsePoint) (i j : ActualPreparedIndex) :
    sourceActualUnitLegRead q i.1 i.2 j.1 j.2 sourceFirstDifference=
      sourceActualLegNormalization q i.1 i.2 j.1 j.2*
        sourceActualLegCorrection q i.1 i.2 j.1 j.2 sourceFirstDifference := by
  rw [sourceActualUnitLegRead_return]
  have bare : sourceQuantumChargedRead q i.1 i.2 j.1 j.2 sourceFirstDifference=0 := by
    change inner ℂ (sourceChargedGaussPrepared q.epsilon q.precision i.1 i.2)
      (sourceFirstDifference (sourceChargedGaussPrepared q.epsilon q.precision j.1 j.2))=0
    rw [sourceFirstDifference_prepared,inner_zero_right]
  rw [bare,zero_add]

/-- Same original normalization consumes GT rather than assigning its charge to the filtered legs by name. -/
theorem sourceFirstUnitCharge_return (q : PhysicalResponsePoint) (i j : ActualPreparedIndex) :
    (Stage10.ActionNormalization.phaseMomentum:ℂ)⁻¹*
      sourceActualUnitLegRead q i.1 i.2 j.1 j.2 sourceFirstAbsoluteCharge=
      sourceActualLegNormalization q i.1 i.2 j.1 j.2*
        (sourcePreparedChargeUnitMatrix i j+(Stage10.ActionNormalization.phaseMomentum:ℂ)⁻¹*
          sourceActualLegCorrection q i.1 i.2 j.1 j.2 sourceFirstAbsoluteCharge) := by
  have equal : sourceQuantumChargedRead q i.1 i.2 j.1 j.2 sourceFirstAbsoluteCharge=
      sourceQuantumChargedRead q i.1 i.2 j.1 j.2 sourceAbsoluteCharge := by
    change inner ℂ (sourceChargedGaussPrepared q.epsilon q.precision i.1 i.2)
      (sourceFirstAbsoluteCharge (sourceChargedGaussPrepared q.epsilon q.precision j.1 j.2))=
      inner ℂ (sourceChargedGaussPrepared q.epsilon q.precision i.1 i.2)
        (sourceAbsoluteCharge (sourceChargedGaussPrepared q.epsilon q.precision j.1 j.2))
    rw [sourceFirstAbsoluteCharge_prepared,sourceAbsoluteCharge_prepared]
  have gram:=congrArg (fun M : Matrix ActualPreparedIndex ActualPreparedIndex ℂ=>M i j)
    (sourcePreparedChargeUnit_generated q)
  change sourceQuantumChargedRead q i.1 i.2 j.1 j.2 sourceAbsoluteCharge=
    (Stage10.ActionNormalization.phaseMomentum:ℂ)*sourcePreparedChargeUnitMatrix i j at gram
  rw [sourceActualUnitLegRead_return,equal,gram]
  have nonzero : (Stage10.ActionNormalization.phaseMomentum:ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'
  field_simp

/-- The normalized original two-Green charge vertex directly consumes the computed native, matter, scalar and two-span material read. -/
theorem sourceFirstUnitCharge_material_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w)*sourceActualUnitLegRead q sL eL sR eR sourceFirstAbsoluteCharge=
      sourceActualLegNormalization q sL eL sR eR*
        ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w)*
        ((Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eR:ℂ)*
            sourceQuantumChargedRead q sL eL sR eR (jointResolvent 0 q.F q.z 0)-
          (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eL:ℂ)*
            sourceQuantumChargedRead q sL eL sR eR (jointResolvent 0 q.F q.w 0)+
          (Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceFirstMaterialChargeRead q.F
            ((jointResolvent 0 q.F q.z 0).adjoint (sourceChargedGaussPrepared q.epsilon q.precision sL eL))
            (jointResolvent 0 q.F q.w 0 (sourceChargedGaussPrepared q.epsilon q.precision sR eR))) := by
  rw [sourceFirstUnitCharge_ward q sL eL sR eR left right]
  have H:=sourceFirstChargeResponse_return q (sourceChargedGaussPrepared q.epsilon q.precision sL eL)
    (sourceChargedGaussPrepared q.epsilon q.precision sR eR)
  change sourceQuantumChargedRead q sL eL sR eR (sourceFirstChargeResponse q)=_ at H
  exact congrArg (fun z : ℂ=>
    sourceActualLegNormalization q sL eL sR eR*
      ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w)*
      ((Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eR:ℂ)*
          sourceQuantumChargedRead q sL eL sR eR (jointResolvent 0 q.F q.z 0)-
        (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eL:ℂ)*
          sourceQuantumChargedRead q sL eL sR eR (jointResolvent 0 q.F q.w 0)+z)) H

end LowEnergy.PreparationPhysicalFirstGaugeMaterialDifference
