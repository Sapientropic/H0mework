import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualChargedFieldRead

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumElectromagneticIdentity PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumPhysicalModeChargeRead
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumGaugeSourceInjection
open PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical PreparationVacuumSourceActionJets
open PreparationVacuumOriginalDensity PreparationVacuumPhysicalChargedFieldFactor
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussCoreHilbert GaussFockLift
open CanonicalGradedSpatialSource CanonicalGradedCharge
open CanonicalPreparationCreation PreparationVacuumPhysicalLockedGaussBalance
open GaussQuantumMultiplier
open GaussComposite GaussComposite.PhysicalModeEMCurrent
open Stage10 Stage10.CanonicalMatter Stage9DEF Stage9DEF.Compatibility
open Stage9C.Material.SpinPair Electromagnetic.ExternalState DiracExteriorMatterAction
open DiracCliffordRepresentation FullQuantum.StateGreen FullQuantum.CoframeResponse
open ChargedPreparation.Dynamics ChargedPreparation.SpatialSpectrum
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7MotherLieAlgebra
open SU7ExteriorMatterGaugeCovariantJet
open ProofFreeRicherAnholonomicSource YangMills.FullPairing QuantizationCheck.Fermion
open StageNineHolonomicField
open PreparationCoordinates
open scoped BigOperators Matrix InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=Classical.decEq _
local instance : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def sourceChargedRestIndex (side edge : Fin 2) : RestStateIndex :=
  (side,if edge=0 then 1 else 3)

def sourceChargedPolarity (edge : Fin 2) : ℝ := if edge=0 then 1 else -1

def sourceChargedRestriction (side edge : Fin 2) : DiracExteriorMatterCarrier :=
  actualRestStatePreparation (sourceChargedRestIndex side edge) (embed (Source.vector 0))

def sourceChargedCoordinates (side edge : Fin 2) : Mode→ℂ :=
  Sum.elim (Quantum.coordinates (sourceChargedRestriction side edge)) (fun _=>0)

def sourceChargedCreation (side edge : Fin 2) : FiberOp :=
  ∑i : Mode,sourceChargedCoordinates side edge i • GaussCARHistory.createFiber i

def sourceChargedFiber (side edge : Fin 2) : FockFiber :=
  oneParticleFiber (sourceChargedCoordinates side edge)

def sourceChargedGaussPrepared (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2) : H :=
  lift (sourceChargedCreation side edge)
    (GaussHalfDensity.fockHalfDensityEquiv.symm (slot ∅ (sourcePoleBase epsilon precision)))

private def creationRead : (Mode→ℂ)→ₗ[ℂ] FiberOp where
  toFun values:=∑i : Mode,values i • GaussCARHistory.createFiber i
  map_add' u v:=by
    simp only [Pi.add_apply]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact add_smul (u i) (v i) (GaussCARHistory.createFiber i)
  map_smul' c values:=by
    simp only [Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul,RingHom.id_apply]

theorem sourceChargedCreation_vacuum (side edge : Fin 2) :
    sourceChargedCreation side edge vacuumFiber=sourceChargedFiber side edge := by
  apply fiberCoordinates.injective
  simp only [sourceChargedCreation,sum_apply,smul_apply,map_sum,map_smul]
  change (∑i : Mode,sourceChargedCoordinates side edge i •
    fiberCoordinates (SourceCARBound.createOp i vacuumFiber))=fiberCoordinates (sourceChargedFiber side edge)
  simp only [SourceCARBound.createOp,SourceCARBound.coordinates_liftOp,vacuumFiber,sourceChargedFiber,
    oneParticleFiber,LinearEquiv.apply_symm_apply]
  simpa only [Fermion.waveCreation,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.sum_apply,LinearMap.smul_apply] using
    Fermion.waveCreation_vacuum (sourceChargedCoordinates side edge)

theorem sourceChargedGaussPrepared_coordinates (epsilon : ℝ) (precision : 0<epsilon)
    (side edge : Fin 2) (word : Occupation) :
    GaussHalfDensity.fockHalfDensityEquiv (sourceChargedGaussPrepared epsilon precision side edge) word=
      sourceChargedFiber side edge word • sourcePoleBase epsilon precision := by
  simp only [sourceChargedGaussPrepared,lift_apply,LinearIsometryEquiv.apply_symm_apply]
  rw [flatLift_apply]
  simp only [slot_apply,smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold entry
  rw [←vacuumFiber_single,sourceChargedCreation_vacuum]

/-- Actual rest restrictions are expanded by the complete moving basis, including degenerate subspaces. -/
def sourceChargedMovingCoefficient (p : PhysicalMomentum) (side edge : Fin 2)
    (state : RestStateIndex) : ℂ :=
  ∑i : Source.Index,star (sourceMovingPoleValues p state i)*
    ((spinScale:ℂ)⁻¹ • sourceRestStateValues (sourceChargedRestIndex side edge)) i

theorem sourceChargedRestriction_moving (p : PhysicalMomentum) (side edge : Fin 2) :
    sourceChargedRestriction side edge=∑state : RestStateIndex,
      sourceChargedMovingCoefficient p side edge state •
        actualMovingPolePreparation p state (embed (Source.vector 0)) := by
  have scale : (spinScale:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt spinScale_pos)
  have h:=congrArg (fun values : Source.Index→ℂ=>
    embed ((actualRestAmplitude 0*(spinScale:ℂ)) • values))
      (sourceMovingPole_complete p ((spinScale:ℂ)⁻¹ •
        sourceRestStateValues (sourceChargedRestIndex side edge)))
  simp only [Finset.smul_sum,map_sum,map_smul,smul_smul] at h
  unfold sourceChargedRestriction
  rw [actualRestState_source,actualRestStateCoordinates]
  simp only [actualMovingPole_source]
  have cancel : (actualRestAmplitude 0*(spinScale:ℂ))*(spinScale:ℂ)⁻¹=actualRestAmplitude 0 := by
    field_simp [scale]
  rw [cancel] at h
  simpa only [sourceChargedMovingCoefficient,map_smul,smul_smul,mul_comm] using h.symm

theorem sourceChargedCoordinates_moving (p : PhysicalMomentum) (side edge : Fin 2) :
    sourceChargedCoordinates side edge=∑state : RestStateIndex,
      sourceChargedMovingCoefficient p side edge state • sourcePoleCoordinates p state := by
  have h:=congrArg Quantum.coordinates (sourceChargedRestriction_moving p side edge)
  simp only [map_sum,map_smul] at h
  funext i
  cases i with
  | inl i=>simpa only [sourceChargedCoordinates,sourcePoleCoordinates,sourcePolePrimalCoordinates,
      Sum.elim_inl,Finset.sum_apply,Pi.smul_apply] using congrFun h i
  | inr i=>simp [sourceChargedCoordinates,sourcePoleCoordinates]

theorem sourceChargedGaussPrepared_moving (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (side edge : Fin 2) :
    sourceChargedGaussPrepared epsilon precision side edge=∑state : RestStateIndex,
      sourceChargedMovingCoefficient p side edge state • sourcePolePrepared epsilon precision p state := by
  have h:=congrArg creationRead (sourceChargedCoordinates_moving p side edge)
  simp only [map_sum,map_smul] at h
  change sourceChargedCreation side edge=∑state : RestStateIndex,
    sourceChargedMovingCoefficient p side edge state • sourcePoleCreation p state at h
  have fiber:=congrArg (fun A : FiberOp=>A vacuumFiber) h
  simp only [sourceChargedCreation_vacuum,sum_apply,smul_apply,sourcePoleCreation_vacuum] at fiber
  apply GaussHalfDensity.fockHalfDensityEquiv.injective
  simp only [map_sum,map_smul]
  apply PiLp.ext
  intro word
  rw [sourceChargedGaussPrepared_coordinates,fiber]
  simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,
    sourcePolePrepared_coordinates,Finset.sum_smul,smul_smul,smul_eq_mul]

/-- The expansion coefficients are actual Hilbert inner products on the same Gauss base. -/
theorem sourceChargedMovingCoefficient_inner (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (side edge : Fin 2) (state : RestStateIndex) :
    inner ℂ (sourcePolePrepared epsilon precision p state)
      (sourceChargedGaussPrepared epsilon precision side edge)=
        sourceChargedMovingCoefficient p side edge state := by
  rw [sourceChargedGaussPrepared_moving epsilon precision p side edge,inner_sum]
  simp only [inner_smul_right,sourcePolePrepared_orthonormal,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq Finset.univ state]
  rw [if_pos (Finset.mem_univ state)]

private theorem lockedValues_charged (side edge : Fin 2) :
    sourceLockedValues 2 (sourceRestStateValues (sourceChargedRestIndex side edge))=
      (sourceChargedPolarity edge:ℂ) • (Complex.I •
        sourceRestStateValues (sourceChargedRestIndex side edge)) := by
  funext index
  rcases index with ⟨spin,color⟩
  fin_cases side <;> fin_cases edge <;> fin_cases spin <;> fin_cases color <;>
    norm_num [sourceChargedRestIndex,sourceChargedPolarity,sourceLockedValues,
      sourceRestStateValues,sourceRestStateCoefficients,ChargedPreparation.CanonicalParticle.upperValues,
      lowerValues,sourceColorPauli,spinRotation,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,Matrix.mul_apply,Fintype.sum_prod_type,
      Fin.sum_univ_four,Fin.sum_univ_two,Fin.mk.injEq,spinScale] <;> ring_nf

private theorem lockedValues_smul (c : ℂ) (v : Source.Index→ℂ) :
    sourceLockedValues 2 (c • v)=c • sourceLockedValues 2 v := by
  funext index
  rcases index with ⟨spin,color⟩
  simp only [sourceLockedValues,Pi.smul_apply,smul_eq_mul,Fin.sum_univ_two,Fin.sum_univ_four]
  ring

private theorem source_embedding_charge (values : Source.Index→ℂ) :
    diracExteriorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
      (embed values)=Complex.I • embed values := by
  have doublet (state : Fin 2) :
      exteriorSpinorMotherLieAction
        (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
        (sourceColorDoubletMatter state)=Complex.I • sourceColorDoubletMatter state := by
    have weight : exteriorHyperchargeWeight
        (sourceColorDoubletIndex state)=1 := by fin_cases state <;> decide
    simp [sourceColorDoubletMatter,exteriorSpinorMotherLieAction,
      HyperchargeResponse.exterior_charge_basis,weight]
  funext spin
  change exteriorSpinorMotherLieAction
    (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
    (∑color : Fin 2,values (spin,color) • sourceColorDoubletMatter color)=
      Complex.I • (∑color : Fin 2,values (spin,color) • sourceColorDoubletMatter color)
  simp only [map_sum,map_smul,doublet,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro color _
  exact smul_comm _ _ _

theorem sourceChargedRestriction_locked (side edge : Fin 2) :
    sourceLockedAction 2 (sourceChargedRestriction side edge)=
      (sourceChargedPolarity edge:ℂ) •
        diracExteriorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
          (sourceChargedRestriction side edge) := by
  unfold sourceChargedRestriction
  rw [actualRestState_source,actualRestStateCoordinates,sourceLockedAction_embedding,
    lockedValues_smul,lockedValues_charged,source_embedding_charge]
  simp only [map_smul]
  module

def sourceNativeYField (mu : Fin 4) : Field289 :=
  ∑a : Fin 12,rawCoordinates nativeY a • gaugeField mu a

private theorem density_sum (s : ActionState) (k : Fin 4) (f : Fin 12→Field289)
    (c : Fin 12→ℝ) :
    densityVariation (∑a : Fin 12,c a • f a) s k=
      ∑a : Fin 12,c a • densityVariation (f a) s k := by
  have direction : fieldDirection (∑a : Fin 12,c a • f a)=
      ∑a : Fin 12,c a • fieldDirection (f a) :=
    show fieldDirectionLinear _=_ from by rw [map_sum];simp only [map_smul];rfl
  unfold densityVariation lowerVariation principalVariation
  rw [direction]
  simp only [map_sum,map_smul,Finset.sum_mul,Finset.smul_sum,smul_mul_assoc,smul_comm Complex.I]
  cases k using Fin.cases <;> simp only [Fin.cases_zero,Fin.cases_succ,smul_sub,Finset.sum_sub_distrib]

theorem sourceNativeYField_density (mu : Fin 4) (s : ActionState)
    (nondegenerate : s.1.det≠0) (k : Fin 4) :
    densityVariation (sourceNativeYField mu) s k=
      if k=0 then stateVolume s •
        (coefficientMatrix mu s.1*GaussNativeMatter.nativePrimal nativeY) else 0 := by
  unfold sourceNativeYField
  rw [density_sum]
  simp only [gauge_density mu _ s nondegenerate k]
  by_cases h : k=0
  · simp only [h,ite_true]
    have native:=congrArg GaussNativeMatter.nativePrimal (raw_original_expansion nativeY)
    simp only [map_sum,map_smul] at native
    rw [native,Finset.mul_sum,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_smul_comm,smul_comm]
  · simp [h]

def sourceNativeYCoefficient (mu : Fin 4) (s : ActionState) : SourceMatrix :=
  densityActionMatrix*(stateVolume s •
    (coefficientMatrix mu s.1*GaussNativeMatter.nativePrimal nativeY))

theorem sourceNativeYField_raw (mu : Fin 4) (p : PhysicalMomentum)
    (s : ActionState) (nondegenerate : s.1.det≠0) :
    rawActionSymbol (sourceNativeYField mu) p s=
      oppositeDual*SourceRealScalarFock.branches (sourceNativeYCoefficient mu s) := by
  unfold rawActionSymbol rawFourier
  simp only [sourceNativeYField_density mu s nondegenerate]
  change oppositeDual*realFourierMatrix
    (fun k=>densityActionMatrix*(if k=0 then stateVolume s •
      (coefficientMatrix mu s.1*GaussNativeMatter.nativePrimal nativeY) else 0)) p=_
  simp [realFourierMatrix,affineMatrix,sourceNativeYCoefficient,SourceRealScalarFock.branches]

private theorem sourceChargedPrimal_locked (side edge : Fin 2) :
    Quantum.operatorMatrix (sourceLockedAction 2)*ᵥQuantum.coordinates (sourceChargedRestriction side edge)=
      (sourceChargedPolarity edge:ℂ) •
        (GaussNativeMatter.nativePrimal nativeY*ᵥQuantum.coordinates (sourceChargedRestriction side edge)) := by
  have h:=congrArg Quantum.coordinates (sourceChargedRestriction_locked side edge)
  rw [←Quantum.matrix_action,map_smul,←Quantum.matrix_action] at h
  have native : GaussNativeMatter.nativePrimal nativeY=
      Quantum.operatorMatrix (diracExteriorMotherLieAction
        (p286LieBlockEmbed HyperchargeResponse.chargeDirection)) := by
    change Quantum.operatorMatrix (diracExteriorMotherLieAction
      (p286LieBlockEmbed (p286CoordinateEquiv.symm nativeY)))=_
    rw [nativeY,p286CoordinateEquiv.symm_apply_apply]
  rw [native]
  exact h

/-- The full original density (opposite dual retained) annihilates the actual charged restriction difference. -/
theorem sourceCharged_raw_difference (mu : Fin 4) (p : PhysicalMomentum)
    (s : ActionState) (nondegenerate : s.1.det≠0) (side edge : Fin 2) :
    (rawActionSymbol (sourceLockedField mu 2) p s-
      (sourceChargedPolarity edge:ℂ) • rawActionSymbol (sourceNativeYField mu) p s)*ᵥ
        sourceChargedCoordinates side edge=0 := by
  rw [sourceLockedSymbol_generated mu 2 p s nondegenerate,sourceNativeYField_raw mu p s nondegenerate]
  have primal : (sourceLockedCoefficient mu 2 s-
      (sourceChargedPolarity edge:ℂ) • sourceNativeYCoefficient mu s)*ᵥ
        Quantum.coordinates (sourceChargedRestriction side edge)=0 := by
    rw [Matrix.sub_mulVec,Matrix.smul_mulVec]
    unfold sourceLockedCoefficient sourceNativeYCoefficient
    simp only [←Matrix.mulVec_mulVec,Matrix.smul_mulVec,sourceChargedPrimal_locked,
      Matrix.mulVec_smul]
    module
  unfold sourceLockedSymbol SourceRealScalarFock.branches
  rw [←mul_smul_comm,←mul_sub,←Matrix.mulVec_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec]
  unfold sourceChargedCoordinates
  simp only [Matrix.fromBlocks_mulVec,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    Matrix.zero_mulVec,add_zero,zero_add]
  have first:=primal
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec] at first
  have joined : Sum.elim
      (sourceLockedCoefficient mu 2 s*ᵥQuantum.coordinates (sourceChargedRestriction side edge))
        (0 : Quantum.Index→ℂ)-
      (sourceChargedPolarity edge:ℂ) • Sum.elim
        (sourceNativeYCoefficient mu s*ᵥQuantum.coordinates (sourceChargedRestriction side edge))
          (0 : Quantum.Index→ℂ)=0 := by
    funext i
    cases i with
    | inl i=>simpa using congrFun first i
    | inr i=>simp
  change oppositeDual*ᵥ
    (Sum.elim (sourceLockedCoefficient mu 2 s*ᵥQuantum.coordinates (sourceChargedRestriction side edge))
      (-(sourceLockedCoefficient mu 2 s).map star*ᵥ(0 : Quantum.Index→ℂ))-
      (sourceChargedPolarity edge:ℂ) •
        Sum.elim (sourceNativeYCoefficient mu s*ᵥQuantum.coordinates (sourceChargedRestriction side edge))
          (-(sourceNativeYCoefficient mu s).map star*ᵥ(0 : Quantum.Index→ℂ)))=0
  rw [Matrix.mulVec_zero,Matrix.mulVec_zero,joined,Matrix.mulVec_zero]

/-- Full CAR is applied first; the one-particle source then consumes its genuine matrix action. -/
theorem sourceCharged_fullCAR_difference (mu : Fin 4) (p : PhysicalMomentum)
    (s : ActionState) (nondegenerate : s.1.det≠0) (side edge : Fin 2) :
    quantized (rawActionSymbol (sourceLockedField mu 2) p s-
      (sourceChargedPolarity edge:ℂ) • rawActionSymbol (sourceNativeYField mu) p s)
        (sourceChargedFiber side edge)=0 := by
  unfold sourceChargedFiber
  rw [quantized_oneParticle,sourceCharged_raw_difference mu p s nondegenerate]
  change fiberCoordinates.symm (LowEnergy.Fermion.oneParticleLinear 0)=0
  rw [map_zero,map_zero]

private theorem fiberAction_entries (A : FiberOp) (v : FockFiber) (word : Occupation) :
    A v word=∑input : Occupation,entry A word input*v input := by
  have basis : v=∑input : Occupation,v input • EuclideanSpace.single input 1 := by
    apply PiLp.ext
    intro output
    simp [WithLp.ofLp_sum,Finset.sum_apply,EuclideanSpace.single,Pi.single_apply]
  conv_lhs => rw [basis,map_sum]
  simp only [map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,entry]
  exact Finset.sum_congr rfl (fun _ _=>mul_comm _ _)

theorem sourceChargedGauss_action_coordinates (epsilon : ℝ) (precision : 0<epsilon)
    (side edge : Fin 2) (A : FiberOp) (word : Occupation) :
    GaussHalfDensity.fockHalfDensityEquiv (lift A (sourceChargedGaussPrepared epsilon precision side edge)) word=
      A (sourceChargedFiber side edge) word • sourcePoleBase epsilon precision := by
  simp only [lift_apply,LinearIsometryEquiv.apply_symm_apply]
  rw [flatLift_apply]
  simp only [sourceChargedGaussPrepared_coordinates,smul_smul]
  rw [←Finset.sum_smul,←fiberAction_entries]

/-- The raw full-Noether difference vanishes on the actual common Gauss preparation, for every source coframe. -/
theorem sourceCharged_fullGauss_difference (epsilon : ℝ) (precision : 0<epsilon)
    (mu : Fin 4) (p : PhysicalMomentum) (s : ActionState) (nondegenerate : s.1.det≠0)
    (side edge : Fin 2) :
    lift (quantized (rawActionSymbol (sourceLockedField mu 2) p s-
      (sourceChargedPolarity edge:ℂ) • rawActionSymbol (sourceNativeYField mu) p s))
        (sourceChargedGaussPrepared epsilon precision side edge)=0 := by
  apply GaussHalfDensity.fockHalfDensityEquiv.injective
  apply PiLp.ext
  intro word
  rw [sourceChargedGauss_action_coordinates,sourceCharged_fullCAR_difference mu p s nondegenerate]
  simp

theorem sourceChargedGauss_gram (epsilon : ℝ) (precision : 0<epsilon)
    (side edge other opposite : Fin 2) :
    inner ℂ (sourceChargedGaussPrepared epsilon precision side edge)
      (sourceChargedGaussPrepared epsilon precision other opposite)=
        if sourceChargedRestIndex side edge=sourceChargedRestIndex other opposite then 1 else 0 := by
  have base : inner ℂ (sourcePoleBase epsilon precision) (sourcePoleBase epsilon precision)=1 := by
    rw [inner_self_eq_norm_sq_to_K,sourcePoleBase_unit]
    norm_num
  rw [←GaussHalfDensity.fockHalfDensityEquiv.inner_map_map,PiLp.inner_apply]
  simp only [sourceChargedGaussPrepared_coordinates,inner_smul_left,inner_smul_right,base,mul_one]
  change inner ℂ (sourceChargedFiber side edge) (sourceChargedFiber other opposite)=_
  rw [SourceQuantumFockGauge.fiber_pairing]
  simp only [sourceChargedFiber,oneParticleFiber,LinearEquiv.apply_symm_apply]
  rw [pairing_oneParticle]
  simp only [sourceChargedCoordinates,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    star_zero,mul_zero,Finset.sum_const_zero,add_zero]
  change Quantum.coordinatePair _ _=_
  rw [Quantum.coordinatePair_full,←YangMills.FullPairing.natural_inner]
  have unit:=actualRestState_orthonormal 0 (sourceChargedRestIndex side edge)
    (sourceChargedRestIndex other opposite)
  simpa only [YangMills.FullPairing.prepared,YangMills.FullPairing.operator_coordinates,
    sourceChargedRestriction] using unit

theorem sourceChargedGauss_unit (epsilon : ℝ) (precision : 0<epsilon) (side edge : Fin 2) :
    ‖sourceChargedGaussPrepared epsilon precision side edge‖=1 := by
  have gram:=sourceChargedGauss_gram epsilon precision side edge side edge
  simp only [ite_true] at gram
  have real:=congrArg Complex.re gram
  change RCLike.re (inner ℂ (sourceChargedGaussPrepared epsilon precision side edge)
    (sourceChargedGaussPrepared epsilon precision side edge))=1 at real
  rw [inner_self_eq_norm_sq] at real
  nlinarith [norm_nonneg (sourceChargedGaussPrepared epsilon precision side edge)]

end LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge
