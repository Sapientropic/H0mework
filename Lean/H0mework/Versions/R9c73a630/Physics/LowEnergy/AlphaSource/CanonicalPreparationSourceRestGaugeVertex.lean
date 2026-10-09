import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRestNativeCurrentCoupling
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationOriginalHessianReturn

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumElectromagneticIdentity
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField StageNineGlobalIntegratedAction
open Stage9C.Material.SpinPair Stage10 Stage10.CanonicalMatter Stage9DEF Stage9DEF.Compatibility
open Stage9C.Dynamics.Homogeneous DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineCoframeLocalDifferentiability StageNineP286GaugeConnectionVariationDensity StageNineMatterVariation
open StageNineP286GaugeConnectionActionVariation StageNineP286GaugeConnectionVariation SU7MotherLieAlgebra SU7MotherGaugeTheory
open SU7ExteriorBreakingYukawa SU7ExteriorMatterRepresentation PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical
open SourcePropagationNativeActionHessian PreparationCoordinates YangMills.FullPairing Electromagnetic.ExternalState
open PreparationVacuumOriginalGreenFeedback
open scoped BigOperators Matrix InnerProductSpace

def sourceGaugeDensityWeight (mu : Fin 4) : ℂ := if mu=0 then 1 else (lapse:ℂ)

def sourceGaugeDensityAction (mu : Fin 4) (direction : P286LieBlockData) : Mother :=
  ((lapse:ℂ)*Complex.I) • (diracMatrixMatterAction
    (inverseCoframeDiracGamma {coframe:=homogeneousCoframe lapse,derivative:=0} mu)).comp
      (diracExteriorMotherLieAction (p286LieBlockEmbed direction))

theorem sourceGaugeDensityAction_normal (mu : Fin 4) (direction : P286LieBlockData) :
    sourceGaugeDensityAction mu direction=sourceGaugeDensityWeight mu • currentAction mu direction := by
  apply LinearMap.ext
  intro matter
  unfold sourceGaugeDensityAction sourceGaugeDensityWeight currentAction
  rw [homogeneousInverseGamma lapse lapse_pos.ne']
  simp only [LinearMap.smul_apply,LinearMap.comp_apply]
  by_cases time : mu=0
  · rw [if_pos time,if_pos time,diracMatrixMatterAction_smul_matrix]
    simp only [smul_smul,Complex.ofReal_inv]
    congr 1
    have nonzero : (lapse:ℂ)≠0 := by exact_mod_cast lapse_pos.ne'
    field_simp [nonzero]
  · rw [if_neg time,if_neg time]
    simp only [one_smul,smul_smul]

def sourceGaugeCanonicalAction (mu : Fin 4) (direction : P286LieBlockData) : Mother :=
  phaseInverse.comp (sourceGaugeDensityAction mu direction)

def sourceGaugeVertexMatrix (mu : Fin 4) (direction : P286LieBlockData) : Matrix Source.Index Source.Index ℂ :=
  fun row column=>sourceGaugeDensityWeight mu*(-((diracGammaZero*diracGamma mu) row.1 column.1))*Complex.I*
    ((direction.1:Matrix (Fin 3) (Fin 3) ℂ) (row.2.castLE (by decide)) (column.2.castLE (by decide))+
      if row.2=column.2 then direction.2.2.1 else 0)

private theorem scalar_matrix_current (weight : ℂ) (matrix : DiracMatrix)
    (internal : Matrix (Fin 2) (Fin 2) ℂ) (values : Source.Index→ℂ) (row : Source.Index) :
    weight*(Complex.I*(-∑ spin : Fin 4,matrix row.1 spin*
      ∑ color : Fin 2,values (spin,color)*internal row.2 color))=
      ∑ column : Source.Index,weight*(-(matrix row.1 column.1))*Complex.I*internal row.2 column.2*values column := by
  rw [mul_neg,←neg_mul]
  simp only [Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spin _
  apply Finset.sum_congr rfl
  intro color _
  ring

theorem sourceGaugeCanonicalAction_coordinates (mu : Fin 4) (direction : P286LieBlockData)
    (values : Source.Index→ℂ) (row : Source.Index) :
    coordinates (sourceGaugeCanonicalAction mu direction (embed values)) row=
      (sourceGaugeVertexMatrix mu direction *ᵥ values) row := by
  rw [sourceGaugeCanonicalAction,sourceGaugeDensityAction_normal]
  simp only [LinearMap.comp_apply,LinearMap.smul_apply,currentAction,map_smul,phaseInverse,LinearMap.neg_apply]
  rw [←LinearMap.comp_apply,←diracMatrixMatterAction_mul]
  simp only [map_neg,Pi.smul_apply,Pi.neg_apply,smul_eq_mul]
  change sourceGaugeDensityWeight mu*(Complex.I*(-sourceColorDoubletDual row.2
      (diracMatrixMatterAction (diracGammaZero*diracGamma mu)
        (diracExteriorMotherLieAction (p286LieBlockEmbed direction)
          (sourceColorDiracMatter (fun spin color=>values (spin,color)))) row.1)))=_
  rw [sourceColorDoubletDual_matrixMotherAction]
  exact scalar_matrix_current (sourceGaugeDensityWeight mu) (diracGammaZero*diracGamma mu)
    (fun color other=>(direction.1:Matrix (Fin 3) (Fin 3) ℂ) (color.castLE (by decide)) (other.castLE (by decide))+
      if color=other then direction.2.2.1 else 0) values row

def sourceRestGaugeVertexMixing (mu : Fin 4) (direction : P286LieBlockData) :
    Matrix RestStateIndex RestStateIndex ℂ := fun left right=>
  (1/2:ℂ)*∑ index : Source.Index,star (sourceRestStateValues left index)*
    (sourceGaugeVertexMatrix mu direction *ᵥ sourceRestStateValues right) index

theorem actualRestState_gaugeDensity_mixing (mu : Fin 4) (direction : P286LieBlockData)
    (point : BasePoint) (left right : RestStateIndex) :
    actual.conjugateMatter point
      (canonicalDual (actualRestStatePreparation left)
        (sourceGaugeDensityAction mu direction (actualRestStatePreparation right (actual.matter point))))=
      (ActionNormalization.phaseMomentum:ℂ)*sourceRestGaugeVertexMixing mu direction left right := by
  rw [Electromagnetic.ExternalState.original_prepared_vertex]
  change 4*(spinScale:ℂ)*inner ℂ
    (operator (actualRestStatePreparation left) (YangMills.FullPairing.prepared point))
    (operator ((sourceGaugeCanonicalAction mu direction).comp (actualRestStatePreparation right))
      (YangMills.FullPairing.prepared point))=_
  have composed : operator ((sourceGaugeCanonicalAction mu direction).comp (actualRestStatePreparation right))
      (YangMills.FullPairing.prepared point)=operator (sourceGaugeCanonicalAction mu direction)
        (operator (actualRestStatePreparation right) (YangMills.FullPairing.prepared point)) := by
    simp [YangMills.FullPairing.prepared,operator_coordinates]
  rw [composed,actualRestState_full_prepared,actualRestState_full_prepared,operator_coordinates,inner_embed]
  simp only [sourceGaugeCanonicalAction_coordinates,actualRestStateCoordinates,Pi.smul_apply,smul_eq_mul,star_mul,
    Matrix.mulVec_smul,Pi.smul_apply]
  have factor : (∑ index : Source.Index,(star (sourceRestStateValues left index)*star (actualRestAmplitude point))*
      (actualRestAmplitude point*(sourceGaugeVertexMatrix mu direction *ᵥ sourceRestStateValues right) index))=
      (star (actualRestAmplitude point)*actualRestAmplitude point)*
        ∑ index : Source.Index,star (sourceRestStateValues left index)*
          (sourceGaugeVertexMatrix mu direction *ᵥ sourceRestStateValues right) index := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  have amplitude : star (actualRestAmplitude point)*actualRestAmplitude point=(1/2:ℂ) := by
    have unit:=actualRestState_orthonormal point (0,0) (0,0)
    rw [actualRestState_full_prepared,inner_embed] at unit
    simp only [actualRestStateCoordinates,coordinates_embed,Pi.smul_apply,smul_eq_mul,star_mul] at unit
    simp [sourceRestStateValues,sourceRestStateCoefficients,Fintype.sum_prod_type,
      ChargedPreparation.CanonicalParticle.upperValues,Fin.sum_univ_four,Fin.sum_univ_two] at unit
    change (starRingEnd ℂ) (actualRestAmplitude point)*actualRestAmplitude point=(1/2:ℂ)
    linear_combination unit/2
  rw [factor,amplitude,ActionNormalization.phaseMomentum_source]
  simp only [sourceRestGaugeVertexMixing]
  push_cast
  rfl


private theorem gaugeSlot_injective (mu nu : Fin 4) (a b : Fin 12) :
    gaugeSlot mu a=gaugeSlot nu b ↔ mu=nu ∧ a=b := by
  constructor
  · intro equal
    have value:=congrArg Fin.val equal
    simp only [gaugeSlot,Fin.val_mk] at value
    constructor <;> apply Fin.ext <;> omega
  · rintro ⟨rfl,rfl⟩
    rfl

theorem sourceGaugeUnit_generated (mu nu : Fin 4) (a : Fin 12) :
    p286CoordinateEquiv.symm (fieldGauge (Pi.single (gaugeSlot mu a) 1) nu)=
      if nu=mu then p286CoordinateEquiv.symm (originalUnit a) else 0 := by
  have coordinate : fieldGauge (Pi.single (gaugeSlot mu a) 1) nu=
      if nu=mu then originalUnit a else 0 := by
    unfold fieldGauge
    by_cases time : nu=mu
    · subst nu
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ off
        have distinct : gaugeSlot mu a≠gaugeSlot mu b := by
          intro equal
          exact off (gaugeSlot_injective mu mu a b |>.mp equal).2.symm
        simp [distinct]
      · simp
    · apply Eq.trans (b:=0)
      · apply Finset.sum_eq_zero
        intro b _
        have distinct : gaugeSlot mu a≠gaugeSlot nu b := by
          intro equal
          exact time (gaugeSlot_injective mu nu a b |>.mp equal).1.symm
        simp [distinct]
      · simp [time]
  rw [coordinate]
  split_ifs <;> simp

theorem actualRestNativeGaugeSlotCurrent (point : BasePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) :
    sourceNativeGaugeCurrentComplex point (actualRestPairPoint point left right) (Pi.single (gaugeSlot mu a) 1)=
      (ActionNormalization.phaseMomentum:ℂ)*sourceRestGaugeVertexMixing mu
        (p286CoordinateEquiv.symm (originalUnit a)) left right := by
  have frame : (actualRestPairPoint point left right).coframe=homogeneousCoframe lapse := congrFun actual_coframe point
  have volume : generatedVolumeDensity (actualRestPairPoint point left right)=lapse := by
    change |(actualRestPairPoint point left right).coframe.det|=lapse
    rw [frame]
    simp [homogeneousCoframe,Matrix.det_diagonal,Fin.prod_univ_four,abs_of_pos lapse_pos]
  unfold sourceNativeGaugeCurrentComplex matterGaugeConnectionVariationVector matterGaugeKineticSum
  rw [volume]
  simp only [sourceGaugeMatterDirection,sourceGaugeUnit_generated,
    matterDualFrameRelative_zeroChart,matterDerivativeFrameRelative_zeroChart]
  rw [Finset.sum_eq_single mu]
  · rw [if_pos rfl,frame]
    change (lapse:ℂ)*(actual.conjugateMatter point)
      (canonicalDual (actualRestStatePreparation left)
        (Complex.I • diracMatrixMatterAction
          (inverseCoframeDiracGamma {coframe:=homogeneousCoframe lapse,derivative:=0} mu)
          (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (originalUnit a)))
            (actualRestStatePreparation right (actual.matter point)))))=_
    have density:=actualRestState_gaugeDensity_mixing mu (p286CoordinateEquiv.symm (originalUnit a)) point left right
    unfold sourceGaugeDensityAction at density
    simp only [LinearMap.smul_apply,LinearMap.comp_apply,map_smul,smul_eq_mul] at density ⊢
    convert! density using 1
    ring
  · intro nu _ off
    have zero : diracExteriorMotherLieAction (p286LieBlockEmbed (0:P286LieBlockData))
        (actualRestPairPoint point left right).matter=0 := by
      simp [diracExteriorMotherLieAction,internalMatterLinearAction,exteriorSpinorMotherLieAction]
      rfl
    simp only [if_neg off,zero,map_zero]
  · simp

theorem actualRestNativeComplexForcingCovector_gaugeSlot (point : BasePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) :
    actualRestNativeComplexForcingCovector point left right (gaugeSlot mu a)=
      (ActionNormalization.phaseMomentum:ℂ)*sourceRestGaugeVertexMixing mu
        (p286CoordinateEquiv.symm (originalUnit a)) left right := by
  have generated:=actualRestNativeComplexForcingCovector_generated point left right (Pi.single (gaugeSlot mu a) 1)
  rw [actualRestNativeGaugeSlotCurrent] at generated
  simp only [Pi.single_apply] at generated
  simp only [apply_ite,Complex.ofReal_one,Complex.ofReal_zero,ite_mul,one_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true] at generated
  exact generated


private theorem gaugeSlot_sum (function : Fin 289→ℂ) (outside : ∀ field : Fin 289,
    field.val<9 ∨ 57≤field.val → function field=0) :
    (∑ field : Fin 289,function field)=∑ mu : Fin 4,∑ a : Fin 12,function (gaugeSlot mu a) := by
  let embedding : (Fin 4×Fin 12)→Fin 289:=fun index=>gaugeSlot index.1 index.2
  have injective : Function.Injective embedding := by
    intro x y equal
    exact Prod.ext (gaugeSlot_injective x.1 y.1 x.2 y.2 |>.mp equal).1
      (gaugeSlot_injective x.1 y.1 x.2 y.2 |>.mp equal).2
  have restricted : (∑ field ∈ Finset.univ.image embedding,function field)=∑ field : Fin 289,function field := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro field _ absent
    apply outside
    by_contra inside
    have lower : 9≤field.val := by omega
    have upper : field.val<57 := by omega
    have muBound : (field.val-9)/12<4 := by omega
    have aBound : (field.val-9)%12<12 := Nat.mod_lt _ (by decide)
    apply absent
    apply Finset.mem_image.mpr
    refine ⟨(⟨(field.val-9)/12,muBound⟩,⟨(field.val-9)%12,aBound⟩),Finset.mem_univ _,?_⟩
    apply Fin.ext
    simp only [embedding,gaugeSlot,Fin.val_mk]
    omega
  rw [←restricted,Finset.sum_image (fun x _ y _ equal=>injective equal)]
  exact Fintype.sum_prod_type _

private theorem complexForcing_off (point : BasePoint) (left right : RestStateIndex) (field : Fin 289)
    (outside : field.val<9 ∨ 57≤field.val) : actualRestNativeComplexForcingCovector point left right field=0 := by
  simp only [actualRestNativeComplexForcingCovector,
    actualRestNativeForcingCovector_supported 0 point left right field outside,
    actualRestNativeForcingCovector_supported 1 point left right field outside,
    Complex.ofReal_zero,mul_zero,add_zero]

def sourceRestGaugeConstraintSlot (index : Fin 9) : Fin 289:=⟨112+index.val,by omega⟩

def sourceRestGaugeConstraintTensor (p : Fin 4→ℂ) (index : Fin 9) : Matrix RestStateIndex RestStateIndex ℂ :=
  fun left right=>(ActionNormalization.phaseMomentum:ℂ)*∑ mu : Fin 4,∑ a : Fin 12,
    originalReadback p (sourceRestGaugeConstraintSlot index) (gaugeSlot mu a)*
      sourceRestGaugeVertexMixing mu (p286CoordinateEquiv.symm (originalUnit a)) left right

theorem actualRestNativeGaugeConstraints_generated (p : Fin 4→ℂ) (point : BasePoint)
    (left right : RestStateIndex) (index : Fin 9) :
    sourceCompatibility p (actualRestNativeComplexForcingCovector point left right)
      (sourceRestGaugeConstraintSlot index)=sourceRestGaugeConstraintTensor p index left right := by
  unfold sourceCompatibility nullProjection projectionMatrix
  rw [Matrix.mulVec_diagonal]
  have active : nullFlag (sourceRestGaugeConstraintSlot index)=true := by
    simp only [nullFlag,sourceRestGaugeConstraintSlot,Fin.val_mk,decide_eq_true_eq]
    omega
  simp only [active,ite_true,one_mul]
  change (∑ field : Fin 289,originalReadback p (sourceRestGaugeConstraintSlot index) field*
    actualRestNativeComplexForcingCovector point left right field)=_
  rw [gaugeSlot_sum (fun field=>originalReadback p (sourceRestGaugeConstraintSlot index) field*
    actualRestNativeComplexForcingCovector point left right field)
    (fun field outside=>by rw [complexForcing_off point left right field outside,mul_zero])]
  simp only [actualRestNativeComplexForcingCovector_gaugeSlot,sourceRestGaugeConstraintTensor,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  apply Finset.sum_congr rfl
  intro a _
  ring

def actualRestNativeGaugeField (p : regularSource) (point : BasePoint) (left right : RestStateIndex) : Fin 289→ℂ :=
  PreparationVacuumOriginalGreenFeedback.sourceField p (actualRestNativeComplexForcingCovector point left right)

theorem actualRestNativeGaugeField_generated (p : regularSource) (point : BasePoint) (left right : RestStateIndex) :
    nativeFourierHessian nativeHessian p.val*ᵥactualRestNativeGaugeField p point left right=
      actualRestNativeComplexForcingCovector point left right-
        originalRowLift p.val*ᵥsourceCompatibility p.val (actualRestNativeComplexForcingCovector point left right) :=
  nativeAction_sourceField p _

end LowEnergy.PreparationVacuumElectromagneticIdentity
