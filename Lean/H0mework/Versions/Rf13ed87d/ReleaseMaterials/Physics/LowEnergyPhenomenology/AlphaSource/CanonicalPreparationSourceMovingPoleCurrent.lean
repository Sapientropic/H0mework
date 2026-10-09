import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceRestGaugeVertex
import Mathlib.Analysis.Matrix.Spectrum
import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Plane.Dynamics

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumElectromagneticIdentity
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource
open DiracExteriorMatterAction DiracCliffordRepresentation Stage9C.Material.SpinPair
open Stage10 Stage10.CanonicalMatter YangMills.FullPairing Electromagnetic.ExternalState
open Stage9DEF Stage9DEF.Compatibility ChargedPreparation.Dynamics ChargedPreparation.SpatialSpectrum
open SourcePropagationNativeActionHessian PreparationCoordinates PreparationVacuumOriginalGreenFeedback
open PreparationVacuumLowerClassical PreparationVacuumMixedFieldReturn
open SU7MotherLieAlgebra SU7MotherGaugeTheory StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity StageNineMatterVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineCoframeLocalDifferentiability Stage9C.Dynamics.Homogeneous
open StageNineMatterCovariantDerivativeAffine StageNineDiracDualFormNativeMatterVariation
open StageNineP286GaugeConnectionVariation StageNineDiracKineticLocalSpinDensity
open LowEnergy.FiniteKernel StageNineDiracDualFormNativeRepairedMatterResponseOperator
open scoped BigOperators Matrix InnerProductSpace ContDiff

private theorem movingFour_hermitian (z a b w : ℂ)
    (hz : star z=z) (ha : star a=a) (hb : star b=b) (hw : star w=w) :
    (!![3*w+z,0,a-Complex.I*b,0; 0,2*w+z,w,a-Complex.I*b;
         a+Complex.I*b,w,2*w-z,0; 0,a+Complex.I*b,0,3*w-z]).IsHermitian := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [Matrix.conjTranspose_apply,map_add,map_sub,map_mul,hz,ha,hb,hw]
  all_goals ring

theorem sourceMovingHamiltonian_hermitian (momentum : Fin 3→ℝ) :
    (ChargedPreparation.SpatialSpectrum.sourceMatrix momentum).IsHermitian := by
  convert movingFour_hermitian ((lapse:ℂ)*(momentum 2:ℂ))
    ((lapse:ℂ)*(momentum 0:ℂ)) ((lapse:ℂ)*(momentum 1:ℂ)) (frequency:ℂ)
    (by simp) (by simp) (by simp) (by simp) using 1
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [ChargedPreparation.SpatialSpectrum.sourceMatrix]
  all_goals ring

def sourceMovingPoleBasis (momentum : Fin 3→ℝ) : OrthonormalBasis (Fin 4) ℂ (EuclideanSpace ℂ (Fin 4)) :=
  (sourceMovingHamiltonian_hermitian momentum).eigenvectorBasis

def sourceMovingPoleEnergy (momentum : Fin 3→ℝ) (state : RestStateIndex) : ℝ :=
  (if state.1=0 then -1 else 1)*(sourceMovingHamiltonian_hermitian momentum).eigenvalues state.2

def sourceMovingPoleValues (momentum : Fin 3→ℝ) (state : RestStateIndex) : Source.Index→ℂ :=
  if state.1=0 then ChargedPreparation.CanonicalParticle.upperValues
    (fun i=>sourceMovingPoleBasis momentum state.2 i)
  else lowerValues (fun i=>sourceMovingPoleBasis momentum state.2 i)

theorem sourceMovingPole_hamiltonian (point : BasePoint) (momentum : Fin 3→ℝ) (state : RestStateIndex) :
    FullQuantum.hamiltonian Runtime.configuration point momentum (embed (sourceMovingPoleValues momentum state))=
      (sourceMovingPoleEnergy momentum state:ℂ) • embed (sourceMovingPoleValues momentum state) := by
  have eigen := (sourceMovingHamiltonian_hermitian momentum).mulVec_eigenvectorBasis state.2
  change ChargedPreparation.SpatialSpectrum.sourceMatrix momentum *ᵥ
    (fun i=>sourceMovingPoleBasis momentum state.2 i)=
      ((sourceMovingHamiltonian_hermitian momentum).eigenvalues state.2) •
        (fun i=>sourceMovingPoleBasis momentum state.2 i) at eigen
  have complexEigen : ChargedPreparation.SpatialSpectrum.sourceMatrix momentum *ᵥ
      (fun i=>sourceMovingPoleBasis momentum state.2 i)=
      ((sourceMovingHamiltonian_hermitian momentum).eigenvalues state.2:ℂ) •
        (fun i=>sourceMovingPoleBasis momentum state.2 i) := by
    rw [eigen]
    funext i
    simp only [Pi.smul_apply,Complex.real_smul,smul_eq_mul]
  by_cases upper : state.1=0
  · simp only [sourceMovingPoleValues,upper,if_true]
    rw [ChargedPreparation.CanonicalParticle.physical_upper_matrix,complexEigen]
    simp only [sourceMovingPoleEnergy,upper,if_true,neg_one_mul,Complex.ofReal_neg,
      ←neg_smul]
    rw [show ChargedPreparation.CanonicalParticle.upperValues
      (-((sourceMovingHamiltonian_hermitian momentum).eigenvalues state.2:ℂ) •
        (fun i=>sourceMovingPoleBasis momentum state.2 i))=
      (-((sourceMovingHamiltonian_hermitian momentum).eigenvalues state.2:ℂ)) •
        ChargedPreparation.CanonicalParticle.upperValues (fun i=>sourceMovingPoleBasis momentum state.2 i) by
          ext i
          rcases i with ⟨spin,color⟩
          fin_cases spin <;> fin_cases color <;> simp [ChargedPreparation.CanonicalParticle.upperValues]]
    exact map_smul _ _ _
  · simp only [sourceMovingPoleValues,upper,if_false]
    rw [ChargedPreparation.SpatialSpectrum.physical_matrix,complexEigen,
      lowerValues_smul,map_smul]
    simp [sourceMovingPoleEnergy,upper]

private theorem movingSide_inner (side other : Fin 2) (u v : Fin 4→ℂ) :
    (∑ index : Source.Index,
      star ((if side=0 then ChargedPreparation.CanonicalParticle.upperValues u else lowerValues u) index)*
        ((if other=0 then ChargedPreparation.CanonicalParticle.upperValues v else lowerValues v) index))=
      if side=other then ∑ i : Fin 4,star (u i)*v i else 0 := by
  fin_cases side <;> fin_cases other <;>
    simp [Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two,
      ChargedPreparation.CanonicalParticle.upperValues,lowerValues]
  all_goals ring

theorem sourceMovingPole_orthonormal (momentum : Fin 3→ℝ) (left right : RestStateIndex) :
    (∑ index : Source.Index,star (sourceMovingPoleValues momentum left index)*
      sourceMovingPoleValues momentum right index)=if left=right then 1 else 0 := by
  rw [sourceMovingPoleValues,sourceMovingPoleValues,movingSide_inner]
  have unit := (sourceMovingPoleBasis momentum).orthonormal
  have inner := orthonormal_iff_ite.mp unit left.2 right.2
  rw [EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm] at inner
  simp only [dotProduct,Pi.star_apply] at inner
  by_cases side : left.1=right.1
  · rw [if_pos side,show (∑ i : Fin 4,star (sourceMovingPoleBasis momentum left.2 i)*
        sourceMovingPoleBasis momentum right.2 i)=if left.2=right.2 then 1 else 0 from inner]
    simp [Prod.ext_iff,side]
  · simp [side,Prod.ext_iff]

theorem sourceMovingPole_nonzero (momentum : Fin 3→ℝ) (state : RestStateIndex) :
    sourceMovingPoleValues momentum state≠0 := by
  intro zero
  have unit:=sourceMovingPole_orthonormal momentum state state
  simp [zero] at unit

private theorem movingOrthonormal (momentum : Fin 3→ℝ) :
    Orthonormal ℂ (fun state : RestStateIndex=>WithLp.toLp 2 (sourceMovingPoleValues momentum state)) := by
  apply orthonormal_iff_ite.mpr
  intro left right
  rw [EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm]
  exact sourceMovingPole_orthonormal momentum left right

def sourceMovingFullBasis (momentum : Fin 3→ℝ) :
    OrthonormalBasis RestStateIndex ℂ (EuclideanSpace ℂ Source.Index) :=
  OrthonormalBasis.mk (movingOrthonormal momentum)
    ((movingOrthonormal momentum).linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [finrank_euclideanSpace,RestStateIndex,Source.Index])).ge

theorem sourceMovingPole_complete (momentum : Fin 3→ℝ) (values : Source.Index→ℂ) :
    (∑ state : RestStateIndex,
      (∑ index : Source.Index,star (sourceMovingPoleValues momentum state index)*values index) •
        sourceMovingPoleValues momentum state)=values := by
  have complete := (sourceMovingFullBasis momentum).sum_repr' (WithLp.toLp 2 values)
  have basis (state : RestStateIndex) : sourceMovingFullBasis momentum state=
      WithLp.toLp 2 (sourceMovingPoleValues momentum state) := by
    exact congrFun (OrthonormalBasis.coe_mk (movingOrthonormal momentum) _) state
  simp only [basis,EuclideanSpace.inner_eq_star_dotProduct] at complete
  try simp_rw [dotProduct_comm] at complete
  have same := congrArg (fun v : EuclideanSpace ℂ Source.Index=>v.ofLp) complete
  simpa only [WithLp.ofLp_sum,WithLp.ofLp_smul,WithLp.ofLp_toLp,dotProduct,Pi.star_apply,mul_comm] using same

def sourceMovingRestCoefficient (momentum : Fin 3→ℝ) (state basisState : RestStateIndex) : ℂ :=
  (spinScale:ℂ)/2 * ∑ index : Source.Index,star (sourceRestStateValues basisState index)*
    sourceMovingPoleValues momentum state index

def actualMovingPolePreparation (momentum : Fin 3→ℝ) (state : RestStateIndex) : Mother :=
  ∑ basisState : RestStateIndex,sourceMovingRestCoefficient momentum state basisState •
    actualRestStatePreparation basisState

private theorem restBasis_reconstruction (values : Source.Index→ℂ) (row : Source.Index) :
    (∑ state : RestStateIndex,((spinScale:ℂ)/2 *
      ∑ index : Source.Index,star (sourceRestStateValues state index)*values index)*
        sourceRestStateValues state row)=(spinScale:ℂ)*values row := by
  have square : (spinScale:ℂ)^2=2 := by exact_mod_cast spinScale_sq
  have cube : (spinScale:ℂ)^3=2*(spinScale:ℂ) := by rw [pow_succ,square]
  rcases row with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    norm_num [Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two,sourceRestStateValues,
      sourceRestStateCoefficients,ChargedPreparation.CanonicalParticle.upperValues,lowerValues]
  all_goals dsimp only [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp only [eq_mpr_eq_cast,cast_eq]
  all_goals norm_num
  all_goals try ring_nf
  all_goals try simp only [cube]
  all_goals first | rfl | (ring_nf <;> rfl)

theorem actualMovingPole_source (point : BasePoint) (momentum : Fin 3→ℝ) (state : RestStateIndex) :
    actualMovingPolePreparation momentum state (embed (Source.vector point))=
      embed ((actualRestAmplitude point*(spinScale:ℂ)) • sourceMovingPoleValues momentum state) := by
  simp only [actualMovingPolePreparation,LinearMap.sum_apply,LinearMap.smul_apply,actualRestState_source]
  simp_rw [←map_smul]
  rw [←map_sum]
  congr 1
  funext row
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,actualRestStateCoordinates,sourceMovingRestCoefficient]
  rw [show (∑ s : RestStateIndex,((spinScale:ℂ)/2 *
        ∑ index : Source.Index,star (sourceRestStateValues s index)*sourceMovingPoleValues momentum state index)*
          (actualRestAmplitude point*sourceRestStateValues s row))=
      actualRestAmplitude point*(∑ s : RestStateIndex,((spinScale:ℂ)/2 *
        ∑ index : Source.Index,star (sourceRestStateValues s index)*sourceMovingPoleValues momentum state index)*
          sourceRestStateValues s row) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring]
  rw [restBasis_reconstruction]
  ring

theorem actualMovingPole_full_prepared (point : BasePoint) (momentum : Fin 3→ℝ) (state : RestStateIndex) :
    operator (actualMovingPolePreparation momentum state) (prepared point)=
      naturalCoordinates (embed ((actualRestAmplitude point*(spinScale:ℂ)) • sourceMovingPoleValues momentum state)) := by
  rw [prepared,operator_coordinates,actualMovingPole_source]

private theorem actualMovingAmplitude_square (point : BasePoint) :
    star (actualRestAmplitude point*(spinScale:ℂ))*(actualRestAmplitude point*(spinScale:ℂ))=1 := by
  have unit:=actualRestState_orthonormal point (0,0) (0,0)
  rw [actualRestState_full_prepared,inner_embed] at unit
  simp only [actualRestStateCoordinates,coordinates_embed,Pi.smul_apply,smul_eq_mul,star_mul] at unit
  norm_num [sourceRestStateValues,sourceRestStateCoefficients,ChargedPreparation.CanonicalParticle.upperValues,
    Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two] at unit
  dsimp only [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go] at unit
  simp only [eq_mpr_eq_cast,cast_eq] at unit
  norm_num at unit
  have square : (spinScale:ℂ)^2=2 := by exact_mod_cast spinScale_sq
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
  calc
    _=((starRingEnd ℂ) (actualRestAmplitude point)*actualRestAmplitude point)*(spinScale:ℂ)^2 := by ring
    _=1 := by rw [square]; linear_combination unit

private theorem movingPair_factor (β : ℂ) (u v : Source.Index→ℂ) :
    (∑ index : Source.Index,star (β*u index)*(β*v index))=
      (star β*β)*(∑ index : Source.Index,star (u index)*v index) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_mul]
  ring

theorem actualMovingPole_orthonormal (point : BasePoint) (momentum : Fin 3→ℝ) (left right : RestStateIndex) :
    inner ℂ (operator (actualMovingPolePreparation momentum left) (prepared point))
      (operator (actualMovingPolePreparation momentum right) (prepared point))=if left=right then 1 else 0 := by
  rw [actualMovingPole_full_prepared,actualMovingPole_full_prepared,inner_embed]
  simp only [coordinates_embed,Pi.smul_apply,smul_eq_mul]
  rw [movingPair_factor,actualMovingAmplitude_square,one_mul,sourceMovingPole_orthonormal]

theorem actualMovingPole_hamiltonian (point : BasePoint) (momentum : Fin 3→ℝ) (state : RestStateIndex) :
    FullQuantum.hamiltonian Runtime.configuration point momentum
      (actualMovingPolePreparation momentum state (actual.matter point))=
      (sourceMovingPoleEnergy momentum state:ℂ) •
        actualMovingPolePreparation momentum state (actual.matter point) := by
  have material : actual.matter point=(2:ℂ) • embed (Source.vector point) := by
    apply naturalCoordinates.injective
    simpa only [map_smul,prepared] using actual_eq_twice_prepared point
  rw [material,map_smul,actualMovingPole_source]
  simp only [map_smul]
  rw [sourceMovingPole_hamiltonian]
  module

def sourceMovingGaugeVertex (mu : Fin 4) (direction : P286LieBlockData)
    (leftMomentum rightMomentum : Fin 3→ℝ) (left right : RestStateIndex) : ℂ :=
  ∑ index : Source.Index,star (sourceMovingPoleValues leftMomentum left index)*
    (sourceGaugeVertexMatrix mu direction *ᵥ sourceMovingPoleValues rightMomentum right) index

theorem actualMovingPole_gaugeDensity_vertex (mu : Fin 4) (direction : P286LieBlockData)
    (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ) (left right : RestStateIndex) :
    actual.conjugateMatter point
      (canonicalDual (actualMovingPolePreparation leftMomentum left)
        (sourceGaugeDensityAction mu direction
          (actualMovingPolePreparation rightMomentum right (actual.matter point))))=
      (ActionNormalization.phaseMomentum:ℂ)*sourceMovingGaugeVertex mu direction leftMomentum rightMomentum left right := by
  rw [original_prepared_vertex]
  have composed : operator ((phaseInverse.comp (sourceGaugeDensityAction mu direction)).comp
      (actualMovingPolePreparation rightMomentum right)) (prepared point)=
      operator (sourceGaugeCanonicalAction mu direction)
        (operator (actualMovingPolePreparation rightMomentum right) (prepared point)) := by
    simp [prepared,sourceGaugeCanonicalAction,operator_coordinates]
  change 4*(spinScale:ℂ)*inner ℂ (operator (actualMovingPolePreparation leftMomentum left) (prepared point))
    (operator ((phaseInverse.comp (sourceGaugeDensityAction mu direction)).comp
      (actualMovingPolePreparation rightMomentum right)) (prepared point))=_
  rw [composed,actualMovingPole_full_prepared,actualMovingPole_full_prepared,operator_coordinates,inner_embed]
  simp only [sourceGaugeCanonicalAction_coordinates,Pi.smul_apply,smul_eq_mul,Matrix.mulVec_smul]
  rw [movingPair_factor,actualMovingAmplitude_square,one_mul,ActionNormalization.phaseMomentum_source]
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,sourceMovingGaugeVertex]

def actualMovingPairConfiguration (leftMomentum rightMomentum : Fin 3→ℝ) (left right : RestStateIndex) :
    StageNineHolonomicConfiguration :=
  { actual with
    matter:=fun point=>actualMovingPolePreparation rightMomentum right (actual.matter point)
    conjugateMatter:=fun point=>(actual.conjugateMatter point).comp (canonicalDual (actualMovingPolePreparation leftMomentum left)) }

def actualMovingPairPoint (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ) (left right : RestStateIndex) :
    StageNineContinuumPointField := toContinuumPointField (actualMovingPairConfiguration leftMomentum rightMomentum left right) point

theorem actualMovingPole_nativeGaugeSlot (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) :
    sourceNativeGaugeCurrentComplex point (actualMovingPairPoint point leftMomentum rightMomentum left right) (Pi.single (gaugeSlot mu a) 1)=
      (ActionNormalization.phaseMomentum:ℂ)*sourceMovingGaugeVertex mu
        (p286CoordinateEquiv.symm (originalUnit a)) leftMomentum rightMomentum left right := by
  have frame : (actualMovingPairPoint point leftMomentum rightMomentum left right).coframe=homogeneousCoframe lapse := congrFun actual_coframe point
  have volume : generatedVolumeDensity (actualMovingPairPoint point leftMomentum rightMomentum left right)=lapse := by
    change |(actualMovingPairPoint point leftMomentum rightMomentum left right).coframe.det|=lapse
    rw [frame]
    simp [homogeneousCoframe,Matrix.det_diagonal,Fin.prod_univ_four,abs_of_pos lapse_pos]
  unfold sourceNativeGaugeCurrentComplex matterGaugeConnectionVariationVector matterGaugeKineticSum
  rw [volume]
  simp only [sourceGaugeMatterDirection,sourceGaugeUnit_generated,
    matterDualFrameRelative_zeroChart,matterDerivativeFrameRelative_zeroChart]
  rw [Finset.sum_eq_single mu]
  · rw [if_pos rfl,frame]
    change (lapse:ℂ)*(actual.conjugateMatter point)
      (canonicalDual (actualMovingPolePreparation leftMomentum left)
        (Complex.I • diracMatrixMatterAction
          (inverseCoframeDiracGamma {coframe:=homogeneousCoframe lapse,derivative:=0} mu)
          (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (originalUnit a)))
            (actualMovingPolePreparation rightMomentum right (actual.matter point)))))=_
    have density:=actualMovingPole_gaugeDensity_vertex mu (p286CoordinateEquiv.symm (originalUnit a)) point leftMomentum rightMomentum left right
    unfold sourceGaugeDensityAction at density
    simp only [LinearMap.smul_apply,LinearMap.comp_apply,map_smul,smul_eq_mul] at density ⊢
    convert! density using 1
    ring
  · intro nu _ off
    have zero : diracExteriorMotherLieAction (p286LieBlockEmbed (0:P286LieBlockData))
        (actualMovingPairPoint point leftMomentum rightMomentum left right).matter=0 := by
      simp [diracExteriorMotherLieAction,internalMatterLinearAction,exteriorSpinorMotherLieAction]
      rfl
    simp only [if_neg off,zero,map_zero]
  · simp

private theorem movingGaugeDirection_add (field : StageNineContinuumPointField) (u v : Field289) :
    sourceGaugeMatterDirection field (u+v)=sourceGaugeMatterDirection field u+sourceGaugeMatterDirection field v := by
  funext mu
  simp only [sourceGaugeMatterDirection,fieldGauge_add,map_add,p286LieBlockEmbed_add,
    StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_add,LinearMap.add_apply,Pi.add_apply]

private theorem movingGaugeDirection_smul (field : StageNineContinuumPointField) (r : ℝ) (u : Field289) :
    sourceGaugeMatterDirection field (r • u)=r • sourceGaugeMatterDirection field u := by
  funext mu
  simp only [sourceGaugeMatterDirection,fieldGauge_smul,map_smul,p286LieBlockEmbed_real_smul,
    StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_real_smul,LinearMap.smul_apply]
  rfl

def sourceMovingGaugeCurrentLinear (point : BasePoint) (field : StageNineContinuumPointField) : Field289 →ₗ[ℝ] ℂ where
  toFun force:=sourceNativeGaugeCurrentComplex point field force
  map_add' u v:=by
    change (generatedVolumeDensity field:ℂ)*matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
        (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field
          (sourceGaugeMatterDirection field (u+v)))=_
    rw [movingGaugeDirection_add,matterCovariantDerivativeVariationVector_add,map_add,mul_add]
    rfl
  map_smul' r u:=by
    change (generatedVolumeDensity field:ℂ)*matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
        (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field
          (sourceGaugeMatterDirection field (r • u)))=_
    rw [movingGaugeDirection_smul,matterCovariantDerivativeVariationVector_real_smul]
    change (generatedVolumeDensity field:ℂ)*matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
      ((r:ℂ) • matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field
        (sourceGaugeMatterDirection field u))=r • _
    rw [map_smul]
    simp only [smul_eq_mul,Complex.real_smul]
    change (generatedVolumeDensity field:ℂ)*((r:ℂ)*matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
      (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field
        (sourceGaugeMatterDirection field u)))=
      (r:ℂ)*((generatedVolumeDensity field:ℂ)*matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
        (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field
          (sourceGaugeMatterDirection field u)))
    ring

def actualMovingNativeForcing (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) : Fin 289→ℂ :=
  fun index=>sourceMovingGaugeCurrentLinear point (actualMovingPairPoint point leftMomentum rightMomentum left right)
    (Pi.single index 1)

theorem actualMovingNativeForcing_generated (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (force : Field289) :
    (∑ index : Fin 289,(force index:ℂ)*actualMovingNativeForcing point leftMomentum rightMomentum left right index)=
      sourceNativeGaugeCurrentComplex point (actualMovingPairPoint point leftMomentum rightMomentum left right) force := by
  have reconstruction : force=∑ index : Fin 289,force index • (Pi.single index 1 : Field289) := by
    ext index
    simp [Pi.single_apply]
  change _=sourceMovingGaugeCurrentLinear point (actualMovingPairPoint point leftMomentum rightMomentum left right) force
  conv_rhs=>rw [reconstruction]
  rw [map_sum]
  simp only [map_smul,RCLike.real_smul_eq_coe_mul,actualMovingNativeForcing]
  rfl

theorem actualMovingNativeForcing_slot (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    actualMovingNativeForcing point leftMomentum rightMomentum left right (gaugeSlot mu a)=
      (ActionNormalization.phaseMomentum:ℂ)*sourceMovingGaugeVertex mu
        (p286CoordinateEquiv.symm (originalUnit a)) leftMomentum rightMomentum left right :=
  actualMovingPole_nativeGaugeSlot point leftMomentum rightMomentum left right mu a

theorem actualMovingNativeForcing_density (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (force : Field289) :
    (∑ index : Fin 289,force index*(actualMovingNativeForcing point leftMomentum rightMomentum left right index).re)=
      sourceNativeGaugeCurrentLinear point (actualMovingPairPoint point leftMomentum rightMomentum left right) force := by
  rw [sourceNativeGaugeCurrentLinear_complex]
  have current:=congrArg Complex.re (actualMovingNativeForcing_generated point leftMomentum rightMomentum left right force)
  simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using current

def actualMovingGaugeKineticCurve (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (force : Field289) (parameter : ℝ) : ℝ :=
  let field:=actualMovingPairPoint point leftMomentum rightMomentum left right
  generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
    (withP286GaugeConnectionJets field (p286CurvatureCoordinate field) field.scalarCovariantDerivative
      (field.matterCovariantDerivative+parameter • sourceGaugeMatterDirection field force))

theorem actualMovingGaugeKineticCurve_hasDerivAt (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (force : Field289) (parameter : ℝ) :
    HasDerivAt (actualMovingGaugeKineticCurve point leftMomentum rightMomentum left right force)
      (∑ index : Fin 289,force index*(actualMovingNativeForcing point leftMomentum rightMomentum left right index).re) parameter := by
  rw [actualMovingNativeForcing_density]
  let field:=actualMovingPairPoint point leftMomentum rightMomentum left right
  let direction:=sourceGaugeMatterDirection field force
  have affine (r : ℝ) : actualMovingGaugeKineticCurve point leftMomentum rightMomentum left right force r=
      generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point field+
        r*sourceNativeGaugeCurrentLinear point field force := by
    change generatedVolumeDensity field*
      (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
        (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field
          (field.matterCovariantDerivative+r • direction))).re=
      generatedVolumeDensity field*
        (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
          (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field field.matterCovariantDerivative)).re+_
    rw [matterCovariantDerivativeVariationVector_add,map_add,Complex.add_re]
    have scaled : (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
        (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field (r • direction))).re=
        r*(matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
          (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field direction)).re := by
      rw [matterCovariantDerivativeVariationVector_real_smul]
      change (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
        ((r:ℂ) • matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field direction)).re=_
      rw [map_smul]
      simp only [smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [scaled]
    change _=generatedVolumeDensity field*
      (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
        (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field field.matterCovariantDerivative)).re+
      r*(generatedVolumeDensity field*
        (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
          (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field direction)).re)
    ring
  have curve:=((hasDerivAt_id parameter).mul_const (sourceNativeGaugeCurrentLinear point field force)).const_add
    (generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point field)
  convert! curve using 1
  · exact funext affine
  · simp [field]

theorem actualMovingNativeForcing_supported (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (index : Fin 289) (outside : index.val<9 ∨ 57 ≤ index.val) :
    actualMovingNativeForcing point leftMomentum rightMomentum left right index=0 := by
  have gauges (mu : Fin 4) : fieldGauge (Pi.single index 1) mu=0 := by
    unfold fieldGauge
    apply Finset.sum_eq_zero
    intro a _
    have off : index≠gaugeSlot mu a := by
      intro equal
      have value:=congrArg Fin.val equal
      simp only [gaugeSlot,Fin.val_mk] at value
      omega
    simp [off]
  have direction : sourceGaugeMatterDirection (actualMovingPairPoint point leftMomentum rightMomentum left right)
      (Pi.single index 1)=0 := by
    funext mu
    simp [sourceGaugeMatterDirection,gauges,diracExteriorMotherLieAction,internalMatterLinearAction,
      exteriorSpinorMotherLieAction]
    rfl
  change (generatedVolumeDensity (actualMovingPairPoint point leftMomentum rightMomentum left right):ℂ)*
    matterDualFrameRelative positiveSmoothUnifiedSource 0 point
      (actualMovingPairPoint point leftMomentum rightMomentum left right).conjugateMatter
      (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point
        (actualMovingPairPoint point leftMomentum rightMomentum left right)
        (sourceGaugeMatterDirection (actualMovingPairPoint point leftMomentum rightMomentum left right) (Pi.single index 1)))=0
  rw [direction]
  simp [matterCovariantDerivativeVariationVector,matterCovariantDerivativeKineticSum]

private theorem movingGaugeSlot_sum (function : Fin 289→ℂ) (outside : ∀ field : Fin 289,
    field.val<9 ∨ 57≤field.val → function field=0) :
    (∑ field : Fin 289,function field)=∑ mu : Fin 4,∑ a : Fin 12,function (gaugeSlot mu a) := by
  let embedding : (Fin 4×Fin 12)→Fin 289:=fun index=>gaugeSlot index.1 index.2
  have injective : Function.Injective embedding := by
    intro x y equal
    have value:=congrArg Fin.val equal
    simp only [embedding,gaugeSlot,Fin.val_mk] at value
    apply Prod.ext <;> apply Fin.ext <;> omega
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

def sourceMovingConstraintTensor (p : Fin 4→ℂ) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (constraint : Fin 9) : ℂ :=
  (ActionNormalization.phaseMomentum:ℂ)*∑ mu : Fin 4,∑ a : Fin 12,
    originalReadback p (sourceRestGaugeConstraintSlot constraint) (gaugeSlot mu a)*
      sourceMovingGaugeVertex mu (p286CoordinateEquiv.symm (originalUnit a)) leftMomentum rightMomentum left right

theorem actualMovingConstraintCurrent_generated (p : Fin 4→ℂ) (point : BasePoint)
    (leftMomentum rightMomentum : Fin 3→ℝ) (left right : RestStateIndex) (constraint : Fin 9) :
    sourceCompatibility p (actualMovingNativeForcing point leftMomentum rightMomentum left right)
      (sourceRestGaugeConstraintSlot constraint)=sourceMovingConstraintTensor p leftMomentum rightMomentum left right constraint := by
  unfold sourceCompatibility nullProjection projectionMatrix
  rw [Matrix.mulVec_diagonal]
  have active : nullFlag (sourceRestGaugeConstraintSlot constraint)=true := by
    simp only [nullFlag,sourceRestGaugeConstraintSlot,Fin.val_mk,decide_eq_true_eq]
    omega
  simp only [active,ite_true,one_mul]
  change (∑ field : Fin 289,originalReadback p (sourceRestGaugeConstraintSlot constraint) field*
    actualMovingNativeForcing point leftMomentum rightMomentum left right field)=_
  rw [movingGaugeSlot_sum (fun field=>originalReadback p (sourceRestGaugeConstraintSlot constraint) field*
    actualMovingNativeForcing point leftMomentum rightMomentum left right field)
    (fun field outside=>by rw [actualMovingNativeForcing_supported point leftMomentum rightMomentum left right field outside,mul_zero])]
  simp only [actualMovingNativeForcing_slot,sourceMovingConstraintTensor,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  apply Finset.sum_congr rfl
  intro a _
  ring

def sourceMovingWaveArgument (momentum : Fin 3→ℝ) (state : RestStateIndex) : BasePoint →L[ℝ] ℝ :=
  (∑ axis : Fin 3,momentum axis • (EuclideanSpace.proj axis.succ : BasePoint →L[ℝ] ℝ))-
    sourceMovingPoleEnergy momentum state • (EuclideanSpace.proj (0:Fin 4) : BasePoint →L[ℝ] ℝ)

def sourceMovingWavePhase (momentum : Fin 3→ℝ) (state : RestStateIndex) (point : BasePoint) : ℂ :=
  Complex.exp ((sourceMovingWaveArgument momentum state point:ℂ)*Complex.I)

theorem sourceMovingWavePhase_smooth (momentum : Fin 3→ℝ) (state : RestStateIndex) :
    ContDiff ℝ ∞ (sourceMovingWavePhase momentum state) :=
  ((Complex.ofRealCLM.contDiff.comp (sourceMovingWaveArgument momentum state).contDiff).mul contDiff_const).cexp

theorem sourceMovingWavePhase_hasFDerivAt (momentum : Fin 3→ℝ) (state : RestStateIndex) (point : BasePoint) :
    HasFDerivAt (sourceMovingWavePhase momentum state)
      ((sourceMovingWaveArgument momentum state).smulRight (sourceMovingWavePhase momentum state point*Complex.I)) point := by
  have scalar : HasDerivAt (fun time : ℝ=>Complex.exp ((time:ℂ)*Complex.I))
      (sourceMovingWavePhase momentum state point*Complex.I) (sourceMovingWaveArgument momentum state point) := by
    simpa [sourceMovingWavePhase] using (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).cexp
  have generated:=scalar.hasFDerivAt.comp point (sourceMovingWaveArgument momentum state).hasFDerivAt
  convert generated using 1 <;> rfl

theorem sourceMovingWavePhase_time (momentum : Fin 3→ℝ) (state : RestStateIndex) (point : BasePoint) :
    fieldDirectionalDerivative (sourceMovingWavePhase momentum state) point 0=
      (-Complex.I*(sourceMovingPoleEnergy momentum state:ℂ))*sourceMovingWavePhase momentum state point := by
  rw [fieldDirectionalDerivative,(sourceMovingWavePhase_hasFDerivAt momentum state point).fderiv]
  change (sourceMovingWaveArgument momentum state (coordinateDirection 0):ℂ)*
    (sourceMovingWavePhase momentum state point*Complex.I)=_
  have time : sourceMovingWaveArgument momentum state (coordinateDirection 0)=-sourceMovingPoleEnergy momentum state := by
    simp [sourceMovingWaveArgument,coordinateDirection]
  rw [time]
  push_cast
  ring

theorem sourceMovingWavePhase_space (momentum : Fin 3→ℝ) (state : RestStateIndex) (point : BasePoint) (axis : Fin 3) :
    fieldDirectionalDerivative (sourceMovingWavePhase momentum state) point axis.succ=
      (Complex.I*(momentum axis:ℂ))*sourceMovingWavePhase momentum state point := by
  rw [fieldDirectionalDerivative,(sourceMovingWavePhase_hasFDerivAt momentum state point).fderiv]
  change (sourceMovingWaveArgument momentum state (coordinateDirection axis.succ):ℂ)*
    (sourceMovingWavePhase momentum state point*Complex.I)=_
  have space : sourceMovingWaveArgument momentum state (coordinateDirection axis.succ)=momentum axis := by
    simp [sourceMovingWaveArgument,coordinateDirection,eq_comm]
  rw [space]
  ring

theorem sourceMovingWavePhase_unit (momentum : Fin 3→ℝ) (state : RestStateIndex) (point : BasePoint) :
    star (sourceMovingWavePhase momentum state point)*sourceMovingWavePhase momentum state point=1 := by
  simp only [sourceMovingWavePhase,Complex.star_def,←Complex.exp_conj,←Complex.exp_add]
  have cancel : (starRingEnd ℂ) ((sourceMovingWaveArgument momentum state point:ℂ)*Complex.I)+
      (sourceMovingWaveArgument momentum state point:ℂ)*Complex.I=0 := by simp
  rw [cancel,Complex.exp_zero]

def sourceMovingWaveModes (momentum : Fin 3→ℝ) (state : RestStateIndex) : Modes Unit where
  value _:=sourceMovingWavePhase momentum state
  smooth _:=sourceMovingWavePhase_smooth momentum state

def sourceMovingWaveSeed (momentum : Fin 3→ℝ) (state : RestStateIndex) : DiracExteriorMatterCarrier :=
  actualMovingPolePreparation momentum state (actual.matter 0)

def sourceMovingWaveDualSeed (momentum : Fin 3→ℝ) (state : RestStateIndex) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (actual.conjugateMatter 0).comp (canonicalDual (actualMovingPolePreparation momentum state))

def sourceMovingWaveFields (momentum : Fin 3→ℝ) (state : RestStateIndex) : StageNineHolonomicConfiguration :=
  configuration Runtime.configuration (sourceMovingWaveModes momentum state)
    (fun _ : Unit=>sourceMovingWaveSeed momentum state) (fun _ : Unit=>sourceMovingWaveDualSeed momentum state)

theorem sourceMovingWave_matter (momentum : Fin 3→ℝ) (state : RestStateIndex) (point : BasePoint) :
    (sourceMovingWaveFields momentum state).matter point=
      sourceMovingWavePhase momentum state point • sourceMovingWaveSeed momentum state := by
  simp [sourceMovingWaveFields,configuration,profile,sourceMovingWaveModes]

theorem sourceMovingWave_dual (momentum : Fin 3→ℝ) (state : RestStateIndex) (point : BasePoint) :
    (sourceMovingWaveFields momentum state).conjugateMatter point=
      star (sourceMovingWavePhase momentum state point) • sourceMovingWaveDualSeed momentum state := by
  simp [sourceMovingWaveFields,configuration,dualProfile,sourceMovingWaveModes]

theorem sourceMovingWave_smooth (momentum : Fin 3→ℝ) (state : RestStateIndex) :
    (sourceMovingWaveFields momentum state).Smooth := by
  rcases actual_smooth with ⟨coframe,gravity,gravityAux,multiplier,gauge,gaugeAux,scalar,_,_⟩
  rw [sourceMovingWaveFields,Runtime.configuration_eq]
  refine ⟨coframe,gravity,gravityAux,multiplier,gauge,gaugeAux,scalar,?_,?_⟩
  · exact profile_smooth (sourceMovingWaveModes momentum state) _
  · intro index
    exact dualProfile_smooth (sourceMovingWaveModes momentum state) _ _

theorem sourceMovingWave_matter_time (momentum : Fin 3→ℝ) (state : RestStateIndex) (point : BasePoint) :
    matterCoordinateEquiv.symm (fieldDirectionalDerivative
      (fun candidate=>matterCoordinateEquiv ((sourceMovingWaveFields momentum state).matter candidate)) point 0)=
      (-Complex.I*(sourceMovingPoleEnergy momentum state:ℂ)) • (sourceMovingWaveFields momentum state).matter point := by
  change matterCoordinateEquiv.symm (fieldDirectionalDerivative
    (fun candidate=>matterCoordinateEquiv (profile (sourceMovingWaveModes momentum state)
      (fun _ : Unit=>sourceMovingWaveSeed momentum state) candidate)) point 0)=_
  rw [profile_directional,sourceMovingWave_matter]
  simp [sourceMovingWaveModes,sourceMovingWavePhase_time,smul_smul]

theorem sourceMovingWave_matter_space (momentum : Fin 3→ℝ) (state : RestStateIndex) (point : BasePoint) (axis : Fin 3) :
    matterCoordinateEquiv.symm (fieldDirectionalDerivative
      (fun candidate=>matterCoordinateEquiv ((sourceMovingWaveFields momentum state).matter candidate)) point axis.succ)=
      (Complex.I*(momentum axis:ℂ)) • (sourceMovingWaveFields momentum state).matter point := by
  change matterCoordinateEquiv.symm (fieldDirectionalDerivative
    (fun candidate=>matterCoordinateEquiv (profile (sourceMovingWaveModes momentum state)
      (fun _ : Unit=>sourceMovingWaveSeed momentum state) candidate)) point axis.succ)=_
  rw [profile_directional,sourceMovingWave_matter]
  simp [sourceMovingWaveModes,sourceMovingWavePhase_space,smul_smul]

theorem sourceMovingWave_spatial_jet (momentum : Fin 3→ℝ) (state : RestStateIndex) (point : BasePoint) (axis : Fin 3) :
    holonomicMatterCovariantDerivative (sourceMovingWaveFields momentum state) point axis.succ=
      (Complex.I*(momentum axis:ℂ)) • (sourceMovingWaveFields momentum state).matter point+
        FullQuantum.connection (sourceMovingWaveFields momentum state) point axis.succ
          ((sourceMovingWaveFields momentum state).matter point) := by
  change holonomicMatterCovariantDerivative (configuration Runtime.configuration
    (sourceMovingWaveModes momentum state) (fun _ : Unit=>sourceMovingWaveSeed momentum state)
    (fun _ : Unit=>sourceMovingWaveDualSeed momentum state)) point axis.succ=_
  rw [profile_covariant,sourceMovingWave_matter]
  simp only [sourceMovingWaveModes,sourceMovingWavePhase_space,sourceMovingWaveFields,
    configuration,FullQuantum.connection,map_smul,smul_smul]
  simp

theorem sourceMovingWave_seed_hamiltonian (point : BasePoint) (momentum : Fin 3→ℝ) (state : RestStateIndex) :
    FullQuantum.hamiltonian Runtime.configuration point momentum (sourceMovingWaveSeed momentum state)=
      (sourceMovingPoleEnergy momentum state:ℂ) • sourceMovingWaveSeed momentum state := by
  rw [sourceMovingWaveSeed,ChargedPreparation.CanonicalParticle.Plane.source_matter_twice,map_smul,actualMovingPole_source]
  simp only [map_smul]
  rw [sourceMovingPole_hamiltonian]
  module

theorem sourceMovingWave_hamiltonian (point : BasePoint) (momentum : Fin 3→ℝ) (state : RestStateIndex) :
    FullQuantum.hamiltonian (sourceMovingWaveFields momentum state) point momentum
      ((sourceMovingWaveFields momentum state).matter point)=
      (sourceMovingPoleEnergy momentum state:ℂ) • (sourceMovingWaveFields momentum state).matter point := by
  have background : FullQuantum.hamiltonian (sourceMovingWaveFields momentum state) point momentum=
      FullQuantum.hamiltonian Runtime.configuration point momentum := rfl
  rw [background,sourceMovingWave_matter,map_smul,sourceMovingWave_seed_hamiltonian]
  exact smul_comm _ _ _

theorem sourceMovingWave_original_action_time_velocity (point : BasePoint) (momentum : Fin 3→ℝ) (state : RestStateIndex) :
    matterCoordinateEquiv.symm (fieldDirectionalDerivative
      (fun candidate=>matterCoordinateEquiv ((sourceMovingWaveFields momentum state).matter candidate)) point 0)=
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity (sourceMovingWaveFields momentum state) point := by
  have time : matterCoordinateEquiv.symm (fieldDirectionalDerivative
      (fun candidate=>matterCoordinateEquiv ((sourceMovingWaveFields momentum state).matter candidate)) point 0)=
      FullQuantum.drift (sourceMovingWaveFields momentum state) point momentum
        ((sourceMovingWaveFields momentum state).matter point) := by
    rw [←FullQuantum.hamiltonian_drift]
    simp only [LinearMap.smul_apply,sourceMovingWave_hamiltonian,smul_smul,sourceMovingWave_matter_time]
  rw [time]
  exact FullQuantum.drift_original (sourceMovingWaveFields momentum state) point momentum
    (sourceMovingWave_spatial_jet momentum state point)

def sourceMovingWavePairFields (leftMomentum rightMomentum : Fin 3→ℝ) (left right : RestStateIndex) :
    StageNineHolonomicConfiguration :=
  {sourceMovingWaveFields rightMomentum right with
    conjugateMatter:=(sourceMovingWaveFields leftMomentum left).conjugateMatter}

def sourceMovingWavePairPoint (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ) (left right : RestStateIndex) :
    StageNineContinuumPointField := toContinuumPointField (sourceMovingWavePairFields leftMomentum rightMomentum left right) point

theorem sourceMovingWavePair_current (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (force : Field289) :
    sourceNativeGaugeCurrentComplex point (sourceMovingWavePairPoint point leftMomentum rightMomentum left right) force=
      (star (sourceMovingWavePhase leftMomentum left point)*sourceMovingWavePhase rightMomentum right point)*
        sourceNativeGaugeCurrentComplex 0 (actualMovingPairPoint 0 leftMomentum rightMomentum left right) force := by
  let field:=sourceMovingWavePairPoint point leftMomentum rightMomentum left right
  have frame : field.coframe=homogeneousCoframe lapse := by
    change Runtime.configuration.coframe point=_
    rw [Runtime.configuration_eq]
    exact congrFun actual_coframe point
  have origin : (actualMovingPairPoint 0 leftMomentum rightMomentum left right).coframe=homogeneousCoframe lapse :=
    congrFun actual_coframe 0
  have volume : generatedVolumeDensity field=lapse := by
    change |field.coframe.det|=lapse
    rw [frame]
    simp [homogeneousCoframe,Matrix.det_diagonal,Fin.prod_univ_four,abs_of_pos lapse_pos]
  have originVolume : generatedVolumeDensity (actualMovingPairPoint 0 leftMomentum rightMomentum left right)=lapse := by
    change |(actualMovingPairPoint 0 leftMomentum rightMomentum left right).coframe.det|=lapse
    rw [origin]
    simp [homogeneousCoframe,Matrix.det_diagonal,Fin.prod_univ_four,abs_of_pos lapse_pos]
  change sourceNativeGaugeCurrentComplex point field force=_
  unfold sourceNativeGaugeCurrentComplex matterGaugeConnectionVariationVector matterGaugeKineticSum
  rw [volume,originVolume]
  simp only [sourceGaugeMatterDirection,matterDualFrameRelative_zeroChart,matterDerivativeFrameRelative_zeroChart]
  rw [frame,origin]
  have primal : field.matter=sourceMovingWavePhase rightMomentum right point • sourceMovingWaveSeed rightMomentum right :=
    sourceMovingWave_matter rightMomentum right point
  have dual : field.conjugateMatter=star (sourceMovingWavePhase leftMomentum left point) • sourceMovingWaveDualSeed leftMomentum left :=
    sourceMovingWave_dual leftMomentum left point
  have originPrimal : (actualMovingPairPoint 0 leftMomentum rightMomentum left right).matter=
      sourceMovingWaveSeed rightMomentum right := rfl
  have originDual : (actualMovingPairPoint 0 leftMomentum rightMomentum left right).conjugateMatter=
      sourceMovingWaveDualSeed leftMomentum left := rfl
  rw [primal,dual,originPrimal,originDual]
  change (lapse:ℂ)*(star (sourceMovingWavePhase leftMomentum left point) • sourceMovingWaveDualSeed leftMomentum left)
    (Complex.I • ∑ mu : Fin 4,diracMatrixMatterAction
      (inverseCoframeDiracGamma {coframe:=homogeneousCoframe lapse,derivative:=0} mu)
      (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (fieldGauge force mu)))
        (sourceMovingWavePhase rightMomentum right point • sourceMovingWaveSeed rightMomentum right)))=_
  simp only [map_smul,LinearMap.smul_apply]
  rw [←Finset.smul_sum,map_smul]
  simp only [smul_eq_mul]
  ring

def sourceMovingWaveForcing (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) : Fin 289→ℂ := fun index=>
  (star (sourceMovingWavePhase leftMomentum left point)*sourceMovingWavePhase rightMomentum right point)*
    actualMovingNativeForcing 0 leftMomentum rightMomentum left right index

theorem sourceMovingWaveForcing_generated (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (force : Field289) :
    (∑ index : Fin 289,(force index:ℂ)*sourceMovingWaveForcing point leftMomentum rightMomentum left right index)=
      sourceNativeGaugeCurrentComplex point (sourceMovingWavePairPoint point leftMomentum rightMomentum left right) force := by
  rw [sourceMovingWavePair_current,←actualMovingNativeForcing_generated]
  simp only [sourceMovingWaveForcing,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sourceMovingWaveForcing_slot (point : BasePoint) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    sourceMovingWaveForcing point leftMomentum rightMomentum left right (gaugeSlot mu a)=
      (star (sourceMovingWavePhase leftMomentum left point)*sourceMovingWavePhase rightMomentum right point)*
        ((ActionNormalization.phaseMomentum:ℂ)*sourceMovingGaugeVertex mu
          (p286CoordinateEquiv.symm (originalUnit a)) leftMomentum rightMomentum left right) := by
  rw [sourceMovingWaveForcing,actualMovingNativeForcing_slot]

theorem sourceMovingWaveForcing_constraints (p : Fin 4→ℂ) (point : BasePoint)
    (leftMomentum rightMomentum : Fin 3→ℝ) (left right : RestStateIndex) (constraint : Fin 9) :
    sourceCompatibility p (sourceMovingWaveForcing point leftMomentum rightMomentum left right)
      (sourceRestGaugeConstraintSlot constraint)=
      (star (sourceMovingWavePhase leftMomentum left point)*sourceMovingWavePhase rightMomentum right point)*
        sourceMovingConstraintTensor p leftMomentum rightMomentum left right constraint := by
  change sourceCompatibility p
    ((star (sourceMovingWavePhase leftMomentum left point)*sourceMovingWavePhase rightMomentum right point) •
      actualMovingNativeForcing 0 leftMomentum rightMomentum left right) (sourceRestGaugeConstraintSlot constraint)=_
  rw [sourceCompatibility,Matrix.mulVec_smul,Matrix.mulVec_smul]
  rw [←actualMovingConstraintCurrent_generated p 0 leftMomentum rightMomentum left right constraint]
  rfl

end LowEnergy.PreparationVacuumElectromagneticIdentity
