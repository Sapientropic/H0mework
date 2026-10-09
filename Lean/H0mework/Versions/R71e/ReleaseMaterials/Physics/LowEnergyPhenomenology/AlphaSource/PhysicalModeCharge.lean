import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativeModeAction
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedPoleCurrent
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceRestPoleSpectrum
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActionTimeMatrix

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.PhysicalModeCharge

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumSourceActionJets PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumPhysicalLockedCurrentFirstResidue
open PreparationVacuumPhysicalModeChargeRead PreparationVacuumFullSlowFieldResponse
open PreparationVacuumNativePoleTensor PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalCharacteristic
open FullQuantum.StateGreen Electromagnetic.CanonicalCoframe
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge CanonicalGradedSpatialSource
open SourceQuantumResidualGaugeSlice SourceQuantumScalarChart SourceQuantumNativeDimensions
open DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9DEF Stage9DEF.Compatibility
open Stage10 Stage10.CanonicalMatter YangMills.FullPairing
open ChargedPreparation.Dynamics ChargedPreparation.SpatialSpectrum
open Stage9C.Material.SpinPair Electromagnetic.ExternalState
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open Filter Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator Topology InnerProductSpace
local instance : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- Original mode current density, before the source actionScale normalization. -/
def modeCurrentDensity (point : BasePoint) (mu : Fin 4) (F : Fin 289→ℂ)
    (left right : RestStateIndex) : ℂ :=
  actual.conjugateMatter point
    (canonicalDual (actualRestStatePreparation left)
      (sourceModeCurrent F mu (actualRestStatePreparation right (actual.matter point))))

/-- The source gauge/Lorentz vertex is the normalized source action rate times the density. -/
def modeVertex (point : BasePoint) (mu : Fin 4)
    (left right : RestStateIndex) : (Fin 289→ℂ)→L[ℂ] ℂ :=
  ∑j : Fin 289,(ContinuousLinearMap.proj j : (Fin 289→ℂ)→L[ℂ] ℂ).smulRight
    ((Stage10.ActionNormalization.actionScale:ℂ)*modeCurrentDensity point mu (Pi.single j 1) left right)

private theorem sourceModeCurrent_linear (mu : Fin 4) (a : ℂ) (F G : Fin 289→ℂ) :
    sourceModeCurrent (a • F+G) mu=a • sourceModeCurrent F mu+sourceModeCurrent G mu := by
  unfold sourceModeCurrent sourceModeMother
  rw [(sourceModeConnection mu).map_add,(sourceModeConnection mu).map_smul]
  have symL : ⇑(Quantum.operatorMatrix.symm)=⇑(Quantum.operatorMatrix.symm.toLinearEquiv):=rfl
  rw [symL,map_add,map_smul,LinearMap.comp_add,LinearMap.comp_smul]
  module

private theorem modeCurrentDensity_linear (point : BasePoint) (mu : Fin 4)
    (left right : RestStateIndex) (a : ℂ) (F G : Fin 289→ℂ) :
    modeCurrentDensity point mu (a • F+G) left right=
      a*modeCurrentDensity point mu F left right+modeCurrentDensity point mu G left right := by
  unfold modeCurrentDensity
  rw [sourceModeCurrent_linear]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,smul_eq_mul]

private theorem modeCurrentDensity_sum (point : BasePoint) (mu : Fin 4)
    (left right : RestStateIndex) (w : Fin 289→ℂ) (s : Finset (Fin 289)) :
    modeCurrentDensity point mu (∑j∈s,w j • Pi.single j 1) left right=
      ∑j∈s,w j • modeCurrentDensity point mu (Pi.single j 1) left right := by
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty,Finset.sum_empty]
      have curr : sourceModeCurrent (0:Fin 289→ℂ) mu=(0:Mother):=by
        unfold sourceModeCurrent sourceModeMother
        rw [map_zero]
        have symL : ⇑(Quantum.operatorMatrix.symm)=
            ⇑(Quantum.operatorMatrix.symm.toLinearEquiv):=rfl
        rw [symL,map_zero,LinearMap.comp_zero,smul_zero]
      unfold modeCurrentDensity
      rw [curr,LinearMap.zero_apply,map_zero,map_zero]
  | @insert a s hs ih =>
      rw [Finset.sum_insert hs,Finset.sum_insert hs]
      rw [modeCurrentDensity_linear]
      rw [ih]
      simp only [smul_eq_mul]

/-- The vertex on an arbitrary complex field is the action-normalized density. -/
theorem modeVertex_actual (point : BasePoint) (mu : Fin 4)
    (left right : RestStateIndex) (F : Fin 289→ℂ) :
    modeVertex point mu left right F=
      (Stage10.ActionNormalization.actionScale:ℂ)*modeCurrentDensity point mu F left right := by
  have basis : F=∑j : Fin 289,F j • Pi.single j (1:ℂ):=by
    funext k
    simp only [Pi.smul_apply,Pi.single_apply,smul_eq_mul,Finset.sum_apply]
    simp only [mul_ite,mul_one,mul_zero]
    rw [Finset.sum_ite_eq Finset.univ k (fun j=>F j)]
    simp
  simp only [modeVertex,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  conv_rhs => rw [basis]
  rw [modeCurrentDensity_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_eq_mul]
  ring

/-- Whole mode-current tensor: for each field, the Fin 4-indexed RestStateIndex matrix. -/
def modeCurrentTensor (point : BasePoint) :
    (Fin 289→ℂ)→L[ℂ](Fin 4→Matrix RestStateIndex RestStateIndex ℂ) :=
  ContinuousLinearMap.pi (fun mu=>
    ContinuousLinearMap.pi (fun left=>
      ContinuousLinearMap.pi (fun right=>modeVertex point mu left right)))

/-- Every tensor component is the normalized mode current density. -/
theorem modeCurrentTensor_actual (point : BasePoint) (F : Fin 289→ℂ)
    (mu : Fin 4) (left right : RestStateIndex) :
    modeCurrentTensor point F mu left right=
      (Stage10.ActionNormalization.actionScale:ℂ)*modeCurrentDensity point mu F left right := by
  simp only [modeCurrentTensor,ContinuousLinearMap.pi_apply]
  exact modeVertex_actual point mu left right F

/-- On a locked source field the μ-component reproduces the original locked mixing exactly. -/
theorem modeCurrentTensor_locked (point : BasePoint) (mu : Fin 4) (i : Fin 3)
    (left right : RestStateIndex) :
    modeCurrentTensor point (fun j=>(sourceLockedField mu i j:ℂ)) mu left right=
      sourceRestLockedMixing mu i left right := by
  rw [modeCurrentTensor_actual]
  unfold modeCurrentDensity
  have current : sourceModeCurrent (fun j=>(sourceLockedField mu i j:ℂ)) mu=
      sourceLockedCurrent mu i := by
    unfold sourceModeCurrent sourceLockedCurrent
    rw [sourceLockedModeMother]
  rw [current]
  rw [actualRestState_locked_current]
  rw [←mul_assoc,LowEnergy.PreparationPhysicalActionUnits.sourceActionScale_momentum,one_mul]

/-- Locked-source charge operator: the temporal component of the locked mode tensor. -/
def lockedCharge (point : BasePoint) : Matrix RestStateIndex RestStateIndex ℂ :=
  modeCurrentTensor point (fun j=>(sourceLockedField 0 2 j:ℂ)) 0

/-- The generated source charge is the diagonal block-two values, not a new table. -/
theorem lockedCharge_generated (point : BasePoint) :
    lockedCharge point=
      Matrix.diagonal (fun state : RestStateIndex=>
        if state.2=(1:Fin 4) then -1
        else if state.2=(3:Fin 4) then (1:ℂ) else 0):=by
  funext left right
  unfold lockedCharge
  rw [modeCurrentTensor_locked,sourceRestLockedCharge_generated,Matrix.diagonal_apply]
  rcases left with ⟨leftSide,leftState⟩
  rcases right with ⟨rightSide,rightState⟩
  fin_cases leftSide <;> fin_cases rightSide <;>
    fin_cases leftState <;> fin_cases rightState <;>
    norm_num [sourceRestLockedChargeBlock,Prod.mk.injEq,Fin.ext_iff,Fin.mk.injEq]

/-- The squared locked charge is the diagonal spectral square of the generated charge. -/
theorem lockedCharge_sq (point : BasePoint) :
    lockedCharge point*lockedCharge point=
      Matrix.diagonal (fun state : RestStateIndex=>
        if state.2=(1:Fin 4)∨state.2=(3:Fin 4) then (1:ℂ) else 0):=by
  rw [lockedCharge_generated,Matrix.diagonal_mul_diagonal]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

/-- The negative charge sector projector, generated from the locked charge itself. -/
def chargeMinus (point : BasePoint) : Matrix RestStateIndex RestStateIndex ℂ :=
  ((2:ℂ)⁻¹) • (lockedCharge point*lockedCharge point-lockedCharge point)

/-- The positive charge sector projector, generated from the locked charge itself. -/
def chargePlus (point : BasePoint) : Matrix RestStateIndex RestStateIndex ℂ :=
  ((2:ℂ)⁻¹) • (lockedCharge point*lockedCharge point+lockedCharge point)

/-- The neutral charge sector projector, generated from the locked charge itself. -/
def chargeNeutral (point : BasePoint) : Matrix RestStateIndex RestStateIndex ℂ :=
  1-lockedCharge point*lockedCharge point

private theorem chargeMinus_diagonal (point : BasePoint) :
    chargeMinus point=Matrix.diagonal (fun state:RestStateIndex=>
      if state.2=(1:Fin 4) then (1:ℂ) else 0):=by
  unfold chargeMinus
  rw [lockedCharge_sq,lockedCharge_generated,Matrix.diagonal_sub,
    ←Matrix.diagonal_smul]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

private theorem chargePlus_diagonal (point : BasePoint) :
    chargePlus point=Matrix.diagonal (fun state:RestStateIndex=>
      if state.2=(3:Fin 4) then (1:ℂ) else 0):=by
  unfold chargePlus
  rw [lockedCharge_sq,lockedCharge_generated,Matrix.diagonal_add,
    ←Matrix.diagonal_smul]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

private theorem chargeNeutral_diagonal (point : BasePoint) :
    chargeNeutral point=Matrix.diagonal (fun state:RestStateIndex=>
      if state.2=(0:Fin 4)∨state.2=(2:Fin 4) then (1:ℂ) else 0):=by
  unfold chargeNeutral
  rw [lockedCharge_sq,←Matrix.diagonal_one,Matrix.diagonal_sub]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

/-- The generated sector projectors are idempotent. -/
theorem chargeMinus_idempotent (point : BasePoint) :
    chargeMinus point*chargeMinus point=chargeMinus point:=by
  rw [chargeMinus_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

theorem chargePlus_idempotent (point : BasePoint) :
    chargePlus point*chargePlus point=chargePlus point:=by
  rw [chargePlus_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

theorem chargeNeutral_idempotent (point : BasePoint) :
    chargeNeutral point*chargeNeutral point=chargeNeutral point:=by
  rw [chargeNeutral_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

/-- The generated projectors partition the identity. -/
theorem chargeProjector_partition (point : BasePoint) :
    chargeMinus point+chargePlus point+chargeNeutral point=1:=by
  rw [chargeMinus_diagonal,chargePlus_diagonal,chargeNeutral_diagonal,
    Matrix.diagonal_add,Matrix.diagonal_add,←Matrix.diagonal_one]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

/-- The generated projectors are pairwise orthogonal. -/
theorem chargeMinus_plus_orthogonal (point : BasePoint) :
    chargeMinus point*chargePlus point=0:=by
  rw [chargeMinus_diagonal,chargePlus_diagonal,Matrix.diagonal_mul_diagonal,
    ←Matrix.diagonal_zero]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

theorem chargeMinus_neutral_orthogonal (point : BasePoint) :
    chargeMinus point*chargeNeutral point=0:=by
  rw [chargeMinus_diagonal,chargeNeutral_diagonal,Matrix.diagonal_mul_diagonal,
    ←Matrix.diagonal_zero]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

theorem chargePlus_neutral_orthogonal (point : BasePoint) :
    chargePlus point*chargeNeutral point=0:=by
  rw [chargePlus_diagonal,chargeNeutral_diagonal,Matrix.diagonal_mul_diagonal,
    ←Matrix.diagonal_zero]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

/-- The locked charge acts with sign −1 on the minus sector. -/
theorem lockedCharge_minus_eigen (point : BasePoint) :
    lockedCharge point*chargeMinus point=-chargeMinus point:=by
  rw [lockedCharge_generated,chargeMinus_diagonal,Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_neg]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

/-- The locked charge acts with sign +1 on the plus sector. -/
theorem lockedCharge_plus_eigen (point : BasePoint) :
    lockedCharge point*chargePlus point=chargePlus point:=by
  rw [lockedCharge_generated,chargePlus_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

/-- The locked charge annihilates the neutral sector. -/
theorem lockedCharge_neutral_eigen (point : BasePoint) :
    lockedCharge point*chargeNeutral point=0:=by
  rw [lockedCharge_generated,chargeNeutral_diagonal,Matrix.diagonal_mul_diagonal,
    ←Matrix.diagonal_zero]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;> norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

/-- Locked-values scale linearly in the source representation. -/
private theorem lockedValues_smul (i : Fin 3) (c : ℂ) (values : Stage9DEF.Source.Index→ℂ) :
    sourceLockedValues i (c • values)=c • sourceLockedValues i values:=by
  funext index
  rcases index with ⟨spin,color⟩
  simp only [sourceLockedValues,Pi.smul_apply,smul_eq_mul,
    Fin.sum_univ_two,Fin.sum_univ_four]
  ring

/-- The temporal source current direction equals i times the locked-values action,
the public phase-seam used instead of the private sourceTemporalLockedValues. -/
private theorem lockedCurrentValues_temporal (i : Fin 3) (values : Stage9DEF.Source.Index→ℂ) :
    sourceLockedCurrentValues 0 i values=Complex.I • sourceLockedValues i values:=by
  have source:=sourceLockedCurrentDirection_embedding 0 i values
  simp only [sourceLockedCurrentDirection,sourceLockedCurrent,LinearMap.comp_apply,
    LinearMap.smul_apply,map_smul,diracGamma,Matrix.cons_val_zero,phase_inverse_source] at source
  rw [sourceLockedAction_embedding] at source
  have read:=congrArg coordinates source
  simpa only [map_smul,coordinates_embed] using read.symm

/-- The locked block-two action on the state-1 source value is the +i eigenvalue. -/
private theorem lockedValues_eigen_minus (side : Fin 2) :
    sourceLockedValues 2 (sourceRestStateValues (side,1))=
      Complex.I • sourceRestStateValues (side,1):=by
  funext index
  rcases index with ⟨spin,color⟩
  fin_cases side <;> fin_cases spin <;> fin_cases color <;>
    norm_num [sourceLockedValues,sourceRestStateValues,sourceRestStateCoefficients,
      ChargedPreparation.CanonicalParticle.upperValues,lowerValues,sourceColorPauli,
      spinRotation,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,
      diracGammaThree,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_four,
      Fin.sum_univ_two,Fin.mk.injEq,spinScale] <;> ring_nf

/-- The locked block-two action on the state-3 source value is the -i eigenvalue. -/
private theorem lockedValues_eigen_plus (side : Fin 2) :
    sourceLockedValues 2 (sourceRestStateValues (side,3))=
      -(Complex.I • sourceRestStateValues (side,3)):=by
  funext index
  rcases index with ⟨spin,color⟩
  fin_cases side <;> fin_cases spin <;> fin_cases color <;>
    norm_num [sourceLockedValues,sourceRestStateValues,sourceRestStateCoefficients,
      ChargedPreparation.CanonicalParticle.upperValues,lowerValues,sourceColorPauli,
      spinRotation,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,
      diracGammaThree,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_four,
      Fin.sum_univ_two,Fin.mk.injEq,spinScale] <;> ring_nf

/-- The actual prepared matter expands to the source embedding. -/
private theorem actual_prepared_matter (point : BasePoint) (state : RestStateIndex) :
    actualRestStatePreparation state (actual.matter point)=
      (2:ℂ) • embed
        (actualRestAmplitude point • sourceRestStateValues state):=by
  have material : actual.matter point=(2 : ℂ) • embed (Stage9DEF.Source.vector point) := by
    apply naturalCoordinates.injective
    simpa only [map_smul,YangMills.FullPairing.prepared] using actual_eq_twice_prepared point
  rw [material,map_smul,actualRestState_source,actualRestStateCoordinates]

/-- The locked temporal mode acts as charge −1 on the actual state-1 pole. -/
theorem modeCharge_minus_eigen (point : BasePoint) (side : Fin 2) :
    sourceModeCurrentDirection (fun j=>(sourceLockedField 0 2 j:ℂ)) 0
      (actualRestStatePreparation (side,1) (actual.matter point))=
    -(actualRestStatePreparation (side,1) (actual.matter point)):=by
  have current : sourceModeCurrentDirection (fun j=>(sourceLockedField 0 2 j:ℂ)) 0=
      sourceLockedCurrentDirection 0 2 := by
    unfold sourceModeCurrentDirection sourceLockedCurrentDirection
    have curr : sourceModeCurrent (fun j=>(sourceLockedField 0 2 j:ℂ)) 0=
        sourceLockedCurrent 0 2 := by
      unfold sourceModeCurrent sourceLockedCurrent
      rw [sourceLockedModeMother]
    rw [curr]
  have double (state : RestStateIndex) :
      Complex.I • (Complex.I • sourceRestStateValues state)=
        -sourceRestStateValues state:=by
    rw [smul_smul,Complex.I_mul_I,neg_one_smul]
  rw [actual_prepared_matter,current,map_smul,sourceLockedCurrentDirection_embedding,
    sourceLockedCurrentValues_smul,lockedCurrentValues_temporal,lockedValues_eigen_minus,
    double,smul_neg,map_neg,smul_neg]

/-- The locked temporal mode acts as charge +1 on the actual state-3 pole. -/
theorem modeCharge_plus_eigen (point : BasePoint) (side : Fin 2) :
    sourceModeCurrentDirection (fun j=>(sourceLockedField 0 2 j:ℂ)) 0
      (actualRestStatePreparation (side,3) (actual.matter point))=
    actualRestStatePreparation (side,3) (actual.matter point):=by
  have current : sourceModeCurrentDirection (fun j=>(sourceLockedField 0 2 j:ℂ)) 0=
      sourceLockedCurrentDirection 0 2 := by
    unfold sourceModeCurrentDirection sourceLockedCurrentDirection
    have curr : sourceModeCurrent (fun j=>(sourceLockedField 0 2 j:ℂ)) 0=
        sourceLockedCurrent 0 2 := by
      unfold sourceModeCurrent sourceLockedCurrent
      rw [sourceLockedModeMother]
    rw [curr]
  have double (state : RestStateIndex) :
      Complex.I • (Complex.I • sourceRestStateValues state)=
        -sourceRestStateValues state:=by
    rw [smul_smul,Complex.I_mul_I,neg_one_smul]
  rw [actual_prepared_matter,current,map_smul,sourceLockedCurrentDirection_embedding,
    sourceLockedCurrentValues_smul,lockedCurrentValues_temporal,lockedValues_eigen_plus]
  rw [smul_neg,double,neg_neg]

/-- The state-1 prepared external pole is nonzero. -/
theorem modeCharge_minus_nonzero (point : BasePoint) (side : Fin 2) :
    actualRestStatePreparation (side,1) (actual.matter point)≠0:=by
  rw [actual_prepared_matter]
  intro zero
  have killed : actualRestAmplitude point • sourceRestStateValues (side,1)=(0:Stage9DEF.Source.Index→ℂ):=by
    have half : (2:ℂ) • embed (actualRestAmplitude point • sourceRestStateValues (side,1))=0:=zero
    rw [smul_eq_zero] at half
    rcases half with two|emb
    · norm_num at two
    · have vals:=congrArg coordinates emb
      simpa only [coordinates_embed,map_zero] using vals
  rw [smul_eq_zero] at killed
  rcases killed with amp|state
  · have square : star (actualRestAmplitude point)*actualRestAmplitude point=(1/2 : ℂ):=by
      have unit:=actualRestState_orthonormal point (0,0) (0,0)
      rw [actualRestState_full_prepared,inner_embed] at unit
      norm_num [coordinates_embed,actualRestStateCoordinates,sourceRestStateValues,
        sourceRestStateCoefficients,ChargedPreparation.CanonicalParticle.upperValues,
        Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two] at unit
      change (starRingEnd ℂ) (actualRestAmplitude point)*actualRestAmplitude point=(1/2 : ℂ)
      linear_combination unit/2
    rw [amp] at square
    norm_num at square
  · have entry := congrFun state (⟨(0:Fin 4),(0:Fin 2)⟩ : Stage9DEF.Source.Index)
    have entry' := congrFun state (⟨(2:Fin 4),(0:Fin 2)⟩ : Stage9DEF.Source.Index)
    fin_cases side
    · rw [Pi.zero_apply] at entry
      norm_num [sourceRestStateValues,sourceRestStateCoefficients,
        ChargedPreparation.CanonicalParticle.upperValues] at entry
      exact (ne_of_gt spinScale_pos) (by exact_mod_cast entry)
    · rw [Pi.zero_apply] at entry'
      norm_num [sourceRestStateValues,sourceRestStateCoefficients,
        lowerValues] at entry'
      exact (ne_of_gt spinScale_pos) (by exact_mod_cast entry')

/-- The state-3 prepared external pole is nonzero. -/
theorem modeCharge_plus_nonzero (point : BasePoint) (side : Fin 2) :
    actualRestStatePreparation (side,3) (actual.matter point)≠0:=by
  rw [actual_prepared_matter]
  intro zero
  have killed : actualRestAmplitude point • sourceRestStateValues (side,3)=(0:Stage9DEF.Source.Index→ℂ):=by
    have half : (2:ℂ) • embed (actualRestAmplitude point • sourceRestStateValues (side,3))=0:=zero
    rw [smul_eq_zero] at half
    rcases half with two|emb
    · norm_num at two
    · have vals:=congrArg coordinates emb
      simpa only [coordinates_embed,map_zero] using vals
  rw [smul_eq_zero] at killed
  rcases killed with amp|state
  · have square : star (actualRestAmplitude point)*actualRestAmplitude point=(1/2 : ℂ):=by
      have unit:=actualRestState_orthonormal point (0,0) (0,0)
      rw [actualRestState_full_prepared,inner_embed] at unit
      norm_num [coordinates_embed,actualRestStateCoordinates,sourceRestStateValues,
        sourceRestStateCoefficients,ChargedPreparation.CanonicalParticle.upperValues,
        Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two] at unit
      change (starRingEnd ℂ) (actualRestAmplitude point)*actualRestAmplitude point=(1/2 : ℂ)
      linear_combination unit/2
    rw [amp] at square
    norm_num at square
  · have entry := congrFun state (⟨(1:Fin 4),(1:Fin 2)⟩ : Stage9DEF.Source.Index)
    have entry' := congrFun state (⟨(3:Fin 4),(1:Fin 2)⟩ : Stage9DEF.Source.Index)
    fin_cases side
    · rw [Pi.zero_apply] at entry
      norm_num [sourceRestStateValues,sourceRestStateCoefficients,
        ChargedPreparation.CanonicalParticle.upperValues] at entry
      exact (ne_of_gt spinScale_pos) (by exact_mod_cast entry)
    · rw [Pi.zero_apply] at entry'
      norm_num [sourceRestStateValues,sourceRestStateCoefficients,
        lowerValues] at entry'
      exact (ne_of_gt spinScale_pos) (by exact_mod_cast entry')

/-- The state-1 prepared external pole has unit prepared-state norm. -/
theorem modeCharge_minus_unit (point : BasePoint) (side : Fin 2) :
    ‖operator (actualRestStatePreparation (side,1)) (YangMills.FullPairing.prepared point)‖=1:=by
  have unit:=actualRestState_orthonormal point (side,1) (side,1)
  rw [if_pos rfl] at unit
  have squared:=inner_self_eq_norm_sq (𝕜:=ℂ)
    (operator (actualRestStatePreparation (side,1)) (YangMills.FullPairing.prepared point))
  rw [unit,RCLike.one_re] at squared
  rcases sq_eq_one_iff.mp squared.symm with one|neg
  · exact one
  · have nn:=norm_nonneg
      (a:=operator (actualRestStatePreparation (side,1)) (YangMills.FullPairing.prepared point))
    rw [neg] at nn
    norm_num at nn

/-- The state-3 prepared external pole has unit prepared-state norm. -/
theorem modeCharge_plus_unit (point : BasePoint) (side : Fin 2) :
    ‖operator (actualRestStatePreparation (side,3)) (YangMills.FullPairing.prepared point)‖=1:=by
  have unit:=actualRestState_orthonormal point (side,3) (side,3)
  rw [if_pos rfl] at unit
  have squared:=inner_self_eq_norm_sq (𝕜:=ℂ)
    (operator (actualRestStatePreparation (side,3)) (YangMills.FullPairing.prepared point))
  rw [unit,RCLike.one_re] at squared
  rcases sq_eq_one_iff.mp squared.symm with one|neg
  · exact one
  · have nn:=norm_nonneg
      (a:=operator (actualRestStatePreparation (side,3)) (YangMills.FullPairing.prepared point))
    rw [neg] at nn
    norm_num at nn

/-- The state-1 prepared pole sits on the generated source rest pole spectrum. -/
theorem modeCharge_minus_pole (point : BasePoint) (side : Fin 2) :
    FullQuantum.hamiltonian Runtime.configuration point 0
      (actualRestStatePreparation (side,1) (actual.matter point))=
        sourceRestPoleEnergy (sourceRestStatePole (side,1)) •
          actualRestStatePreparation (side,1) (actual.matter point):=
  actualRestState_hamiltonian point (side,1)

/-- The state-3 prepared pole sits on the generated source rest pole spectrum. -/
theorem modeCharge_plus_pole (point : BasePoint) (side : Fin 2) :
    FullQuantum.hamiltonian Runtime.configuration point 0
      (actualRestStatePreparation (side,3) (actual.matter point))=
        sourceRestPoleEnergy (sourceRestStatePole (side,3)) •
          actualRestStatePreparation (side,3) (actual.matter point):=
  actualRestState_hamiltonian point (side,3)

/-- The observed pole tensor: the complete mode-current tensor evaluated on the
actual native pole field sheet. -/
def observedPoleTensor (point : BasePoint) (q : PhysicalResponsePoint)
    (epsilon s : ℝ) (n p : PhysicalMomentum) (left right : RestStateIndex) (T : ℝ) :
    Fin 4→Matrix RestStateIndex RestStateIndex ℂ :=
  modeCurrentTensor point (actualSheetField q epsilon s n p left right T)

/-- The observed residue: the complete mode-current tensor of the actual residue field. -/
def observedPoleResidue (point : BasePoint) (q : PhysicalResponsePoint)
    (epsilon s : ℝ) (n p : PhysicalMomentum) (left right : RestStateIndex) (T : ℝ) :
    Fin 4→Matrix RestStateIndex RestStateIndex ℂ :=
  modeCurrentTensor point (actualSheetResidue q epsilon s n p left right T)

/-- The observed tensor carries the exact eventual punctured-sheet residue contract. -/
theorem observed_pole_residue (point : BasePoint) (q : PhysicalResponsePoint)
    (branch : Fin 2) (n p : PhysicalMomentum) (unit : PreparationVacuumPhysicalCharacteristic.spatialSquare n=1)
    (left right : RestStateIndex) (T : ℝ) :
    ∀ᶠ e in scaleApproach,Tendsto
      (fun t=>((t-sourceSheet branch n unit e.val:ℝ):ℂ)•
        observedPoleTensor point q e.val t n p left right T)
      (𝓝[≠](sourceSheet branch n unit e.val))
      (𝓝 (observedPoleResidue point q e.val
        (sourceSheet branch n unit e.val) n p left right T)):=by
  filter_upwards [actualSheetField_residue q branch n p unit left right T] with e h
  unfold observedPoleTensor observedPoleResidue
  have step:=((modeCurrentTensor point).continuous.tendsto _).comp h
  rw [Function.comp_def] at step
  simpa only [map_smul] using step

/-- Direct consumer: the arbitrary-field vertex is the action-normalized original
Noether density, and the locked field delivers the signed charged external poles
with their generated Hamiltonian pole and unit prepared-state norm. -/
theorem modeCharge_noether_consumer (point : BasePoint) (mu : Fin 4)
    (left right : RestStateIndex) (F : Fin 289→ℂ) :
    modeVertex point mu left right F=
      (Stage10.ActionNormalization.actionScale:ℂ)*
        (4*(spinScale : ℂ)*
          inner ℂ
            (operator (actualRestStatePreparation left) (YangMills.FullPairing.prepared point))
            (operator (phaseInverse.comp
              ((sourceModeCurrent F mu).comp (actualRestStatePreparation right)))
              (YangMills.FullPairing.prepared point))):=by
  rw [modeVertex_actual]
  unfold modeCurrentDensity
  rw [Electromagnetic.ExternalState.original_prepared_vertex]

/-- The full bundle: complete tensor semantics, signed generated charges,
nonzero charged external poles on the source Hamiltonian spectrum. -/
theorem modeCharge_complete (point : BasePoint) (side : Fin 2) :
    (∀ mu left right (F : Fin 289→ℂ),
        modeCurrentTensor point F mu left right=
          (Stage10.ActionNormalization.actionScale:ℂ)*
            modeCurrentDensity point mu F left right)
    ∧ modeCurrentTensor point (fun j=>(sourceLockedField 0 2 j:ℂ)) 0=
        lockedCharge point
    ∧ (sourceModeCurrentDirection (fun j=>(sourceLockedField 0 2 j:ℂ)) 0
        (actualRestStatePreparation (side,1) (actual.matter point))=
        -(actualRestStatePreparation (side,1) (actual.matter point)))
    ∧ (sourceModeCurrentDirection (fun j=>(sourceLockedField 0 2 j:ℂ)) 0
        (actualRestStatePreparation (side,3) (actual.matter point))=
        actualRestStatePreparation (side,3) (actual.matter point))
    ∧ FullQuantum.hamiltonian Runtime.configuration point 0
        (actualRestStatePreparation (side,1) (actual.matter point))=
        sourceRestPoleEnergy (sourceRestStatePole (side,1)) •
          actualRestStatePreparation (side,1) (actual.matter point):=
  ⟨fun mu left right F=>modeCurrentTensor_actual point F mu left right,
    rfl,modeCharge_minus_eigen point side,modeCharge_plus_eigen point side,
    modeCharge_minus_pole point side⟩

end LowEnergy.GaussComposite.PhysicalModeCharge
