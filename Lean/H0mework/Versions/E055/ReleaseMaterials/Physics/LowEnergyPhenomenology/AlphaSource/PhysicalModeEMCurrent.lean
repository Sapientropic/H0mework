import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.PhysicalModeCharge
import H0mework.Versions.AB.Physics.MotherSource.CanonicalMatter.Dual
import H0mework.Versions.R2.Physics.QuantumCompatibility.Current

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.PhysicalModeEMCurrent

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
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction SU7ExteriorMatterGaugeCovariantJet
open SU7MotherLieAlgebra
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open LowEnergy.GaussComposite.PhysicalModeCharge
open Filter Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator Topology InnerProductSpace
local instance : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- Local recreation of the source hypercharge eigen on the doublet carrier. -/
private theorem doublet_hypercharge_eigen (state : Fin 2) :
    exteriorSpinorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
      (sourceColorDoubletMatter state) = Complex.I • sourceColorDoubletMatter state := by
  have weight : exteriorHyperchargeWeight (sourceColorDoubletIndex state) = 1 := by
    fin_cases state <;> decide
  simp [sourceColorDoubletMatter, exteriorSpinorMotherLieAction,
    HyperchargeResponse.exterior_charge_basis, weight]

/-- Local recreation: the hypercharge generator acts as i on every embedded source value. -/
private theorem source_hypercharge_eigen (values : Stage9DEF.Source.Index → ℂ) :
    diracExteriorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
      (embed values) = Complex.I • embed values := by
  funext spin
  change exteriorSpinorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
    (∑ color : Fin 2, values (spin,color) • sourceColorDoubletMatter color) =
      Complex.I • (∑ color : Fin 2, values (spin,color) • sourceColorDoubletMatter color)
  simp only [map_sum, map_smul, doublet_hypercharge_eigen, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro color _
  exact smul_comm _ _ _

/-- Locked-values scale linearly in the source representation. -/
private theorem lockedValues_smul (i : Fin 3) (c : ℂ) (values : Stage9DEF.Source.Index→ℂ) :
    sourceLockedValues i (c • values)=c • sourceLockedValues i values:=by
  funext index
  rcases index with ⟨spin,color⟩
  simp only [sourceLockedValues,Pi.smul_apply,smul_eq_mul,
    Fin.sum_univ_two,Fin.sum_univ_four]
  ring

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

/-- The locked two-direction acts as +i on the embedded state-1 pole. -/
private theorem lockedAction_eigen_minus (point : BasePoint) (side : Fin 2) :
    sourceLockedAction 2 (embed (actualRestAmplitude point • sourceRestStateValues (side,1)))=
      Complex.I • embed (actualRestAmplitude point • sourceRestStateValues (side,1)):=by
  rw [sourceLockedAction_embedding,lockedValues_smul,lockedValues_eigen_minus,
    smul_comm,map_smul]

/-- The locked two-direction acts as -i on the embedded state-3 pole. -/
private theorem lockedAction_eigen_plus (point : BasePoint) (side : Fin 2) :
    sourceLockedAction 2 (embed (actualRestAmplitude point • sourceRestStateValues (side,3)))=
      -(Complex.I • embed (actualRestAmplitude point • sourceRestStateValues (side,3))):=by
  rw [sourceLockedAction_embedding,lockedValues_smul,lockedValues_eigen_plus,
    smul_neg,smul_comm,map_neg,map_smul]

/-- The hypercharge generator acts as +i on every embedded actual pole state. -/
private theorem gaugeAction_embed_eigen (point : BasePoint) (state : RestStateIndex) :
    diracExteriorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
      (embed (actualRestAmplitude point • sourceRestStateValues state))=
      Complex.I • embed (actualRestAmplitude point • sourceRestStateValues state):=by
  rw [map_smul,map_smul,source_hypercharge_eigen,smul_comm,←map_smul]

/-- The canonical normalized electrical-current tensor on actual rest states. -/
def canonicalCurrentTensor (point : BasePoint) (mu : Fin 4) :
    Matrix RestStateIndex RestStateIndex ℂ :=
  fun left right=>(Stage10.ActionNormalization.actionScale:ℂ)*
    actual.conjugateMatter point
      (canonicalDual (actualRestStatePreparation left)
        (currentAction mu HyperchargeResponse.chargeDirection
          (actualRestStatePreparation right (actual.matter point))))

/-- All four mode currents at the locked two-field agree with the canonical
electrical current on the negative-charge actual pole. -/
theorem modeCurrent_minus_actual (point : BasePoint) (side : Fin 2) (mu : Fin 4) :
    sourceModeCurrent (fun j=>(sourceLockedField mu 2 j:ℂ)) mu
      (actualRestStatePreparation (side,1) (actual.matter point))=
    currentAction mu HyperchargeResponse.chargeDirection
      (actualRestStatePreparation (side,1) (actual.matter point)):=by
  have prepared:=actual_prepared_matter point (side,1)
  have curr : sourceModeCurrent (fun j=>(sourceLockedField mu 2 j:ℂ)) mu=
      sourceLockedCurrent mu 2:=by
    unfold sourceModeCurrent sourceLockedCurrent
    rw [sourceLockedModeMother]
  rw [curr,prepared]
  simp only [sourceLockedCurrent,currentAction,LinearMap.smul_apply,LinearMap.comp_apply]
  conv_lhs => rw [map_smul,lockedAction_eigen_minus]
  conv_rhs => rw [map_smul,gaugeAction_embed_eigen]

/-- All four mode currents at the locked two-field agree with minus the canonical
electrical current on the positive-charge actual pole. -/
theorem modeCurrent_plus_actual (point : BasePoint) (side : Fin 2) (mu : Fin 4) :
    sourceModeCurrent (fun j=>(sourceLockedField mu 2 j:ℂ)) mu
      (actualRestStatePreparation (side,3) (actual.matter point))=
    -currentAction mu HyperchargeResponse.chargeDirection
      (actualRestStatePreparation (side,3) (actual.matter point)):=by
  have prepared:=actual_prepared_matter point (side,3)
  have curr : sourceModeCurrent (fun j=>(sourceLockedField mu 2 j:ℂ)) mu=
      sourceLockedCurrent mu 2:=by
    unfold sourceModeCurrent sourceLockedCurrent
    rw [sourceLockedModeMother]
  rw [curr,prepared]
  simp only [sourceLockedCurrent,currentAction,LinearMap.smul_apply,LinearMap.comp_apply]
  conv_lhs => rw [map_smul,lockedAction_eigen_plus,smul_neg]
  conv_rhs => rw [map_smul,gaugeAction_embed_eigen]
  rw [map_neg,smul_neg]

/-- Charged-column identification: the full mode tensor column on the negative
pole is the canonical electrical-current column, for every Lorentz index and
every left state. -/
theorem modeTensor_minus_column (point : BasePoint) (mu : Fin 4)
    (left : RestStateIndex) (side : Fin 2) :
    modeCurrentTensor point (fun j=>(sourceLockedField mu 2 j:ℂ)) mu left (side,1)=
      canonicalCurrentTensor point mu left (side,1):=by
  rw [modeCurrentTensor_actual]
  unfold canonicalCurrentTensor modeCurrentDensity
  rw [modeCurrent_minus_actual]

/-- Charged-column identification on the positive pole, with the canonical
sign reversed. -/
theorem modeTensor_plus_column (point : BasePoint) (mu : Fin 4)
    (left : RestStateIndex) (side : Fin 2) :
    modeCurrentTensor point (fun j=>(sourceLockedField mu 2 j:ℂ)) mu left (side,3)=
      -canonicalCurrentTensor point mu left (side,3):=by
  rw [modeCurrentTensor_actual]
  unfold canonicalCurrentTensor modeCurrentDensity
  rw [modeCurrent_plus_actual,map_neg,map_neg,mul_neg]

/-- The charge-minus sector, rederived from the public locked-charge data. -/
private theorem chargeMinus_diag (point : BasePoint) :
    chargeMinus point=Matrix.diagonal (fun state:RestStateIndex=>
      if state.2=(1:Fin 4) then (1:ℂ) else 0):=by
  unfold chargeMinus
  rw [lockedCharge_sq,lockedCharge_generated,Matrix.diagonal_sub,
    ←Matrix.diagonal_smul]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;>
    norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,
      smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

/-- The charge-plus sector, rederived from the public locked-charge data. -/
private theorem chargePlus_diag (point : BasePoint) :
    chargePlus point=Matrix.diagonal (fun state:RestStateIndex=>
      if state.2=(3:Fin 4) then (1:ℂ) else 0):=by
  unfold chargePlus
  rw [lockedCharge_sq,lockedCharge_generated,Matrix.diagonal_add,
    ←Matrix.diagonal_smul]
  congr 1
  funext state
  rcases state with ⟨side,state⟩
  fin_cases side <;> fin_cases state <;>
    norm_num [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.zero_apply,Pi.one_apply,
      smul_eq_mul,Fin.ext_iff,Fin.mk.injEq]

/-- On the generated charge-minus sector the mode tensor is exactly the
canonical electrical-current tensor, at all four Lorentz indices. -/
theorem modeTensor_minus_sector (point : BasePoint) (mu : Fin 4) :
    (modeCurrentTensor point (fun j=>(sourceLockedField mu 2 j:ℂ)) mu)*
      chargeMinus point=canonicalCurrentTensor point mu*chargeMinus point:=by
  rw [chargeMinus_diag]
  funext left right
  rw [Matrix.mul_diagonal,Matrix.mul_diagonal]
  rcases right with ⟨rightSide,rightState⟩
  fin_cases rightSide <;> fin_cases rightState <;>
    norm_num [modeTensor_minus_column,Fin.ext_iff,Fin.mk.injEq]

/-- On the generated charge-plus sector the mode tensor is minus the canonical
electrical-current tensor, at all four Lorentz indices. -/
theorem modeTensor_plus_sector (point : BasePoint) (mu : Fin 4) :
    (modeCurrentTensor point (fun j=>(sourceLockedField mu 2 j:ℂ)) mu)*
      chargePlus point=-(canonicalCurrentTensor point mu*chargePlus point):=by
  rw [chargePlus_diag]
  funext left right
  rw [Matrix.mul_diagonal,Matrix.neg_apply,Matrix.mul_diagonal]
  rcases right with ⟨rightSide,rightState⟩
  fin_cases rightSide <;> fin_cases rightState <;>
    norm_num [Fin.ext_iff,Fin.mk.injEq]
  all_goals exact modeTensor_plus_column point mu left _

/-- Zero-momentum sign: the forward mode charge on the negative actual pole is -1. -/
theorem modeTemporal_minus_unit (point : BasePoint) (side : Fin 2) :
    modeCurrentTensor point (fun j=>(sourceLockedField 0 2 j:ℂ)) 0 (side,1) (side,1)=-1:=by
  rw [modeCurrentTensor_locked,sourceRestLockedCharge_generated]
  norm_num [sourceRestLockedChargeBlock,Prod.mk.injEq,Fin.ext_iff,Fin.mk.injEq]

/-- Zero-momentum sign: the forward mode charge on the positive actual pole is +1. -/
theorem modeTemporal_plus_unit (point : BasePoint) (side : Fin 2) :
    modeCurrentTensor point (fun j=>(sourceLockedField 0 2 j:ℂ)) 0 (side,3) (side,3)=1:=by
  rw [modeCurrentTensor_locked,sourceRestLockedCharge_generated]
  norm_num [sourceRestLockedChargeBlock,Prod.mk.injEq,Fin.ext_iff,Fin.mk.injEq]

/-- The canonical temporal electrical current is the generated unit hypercharge
channel on every actual rest state. -/
theorem canonicalTemporal (point : BasePoint) (state : RestStateIndex) :
    canonicalCurrentTensor point 0 state state=-1:=by
  unfold canonicalCurrentTensor
  rw [actualRestState_hypercharge_current,mul_neg,
    LowEnergy.PreparationPhysicalActionUnits.sourceActionScale_momentum]

/-- Explicit neutral counter: the source mode charge vanishes on the state-0
pole while the canonical temporal current stays -1, so the identification is
bound to the generated charged sectors, not to all eight states. -/
theorem modeEM_neutral_counter (point : BasePoint) (side : Fin 2) :
    modeCurrentTensor point (fun j=>(sourceLockedField 0 2 j:ℂ)) 0 (side,0) (side,0)=0
    ∧ canonicalCurrentTensor point 0 (side,0) (side,0)=-1:=
  ⟨by rw [modeCurrentTensor_locked,sourceRestLockedCharge_generated]
      norm_num [sourceRestLockedChargeBlock,Prod.mk.injEq,Fin.ext_iff,Fin.mk.injEq],
    canonicalTemporal point (side,0)⟩

/-- The observed charged-sector tensor: the complete native-pole mode tensor
projected by the generated charge-sector polynomial. -/
def observedChargedTensor (point : BasePoint) (q : PhysicalResponsePoint)
    (epsilon s : ℝ) (n p : PhysicalMomentum) (left right : RestStateIndex) (T : ℝ) :
    Fin 4→Matrix RestStateIndex RestStateIndex ℂ :=
  fun mu=>(observedPoleTensor point q epsilon s n p left right T mu)*
    (chargeMinus point+chargePlus point)

/-- The observed charged-sector residue. -/
def observedChargedResidue (point : BasePoint) (q : PhysicalResponsePoint)
    (epsilon s : ℝ) (n p : PhysicalMomentum) (left right : RestStateIndex) (T : ℝ) :
    Fin 4→Matrix RestStateIndex RestStateIndex ℂ :=
  fun mu=>(observedPoleResidue point q epsilon s n p left right T mu)*
    (chargeMinus point+chargePlus point)

/-- The charged-sector projection carries the exact eventual punctured-sheet
residue contract of the native pole. -/
theorem observed_charged_residue (point : BasePoint) (q : PhysicalResponsePoint)
    (branch : Fin 2) (n p : PhysicalMomentum)
    (unit : PreparationVacuumPhysicalCharacteristic.spatialSquare n=1)
    (left right : RestStateIndex) (T : ℝ) :
    ∀ᶠ e in scaleApproach,Tendsto
      (fun t=>((t-sourceSheet branch n unit e.val:ℝ):ℂ)•
        observedChargedTensor point q e.val t n p left right T)
      (𝓝[≠](sourceSheet branch n unit e.val))
      (𝓝 (observedChargedResidue point q e.val
        (sourceSheet branch n unit e.val) n p left right T)):=by
  filter_upwards [observed_pole_residue point q branch n p unit left right T] with e h
  unfold observedChargedTensor observedChargedResidue
  rw [tendsto_pi_nhds] at h ⊢
  intro mu
  have per:=(h mu).mul_const (chargeMinus point+chargePlus point)
  simpa only [Pi.smul_apply,Matrix.smul_mul] using per

/-- Direct consumer: every four-current component on the generated charged
poles coincides (with canonical sign) with the canonical electrical current,
the temporal units are the generated source charges, the neutral sector is an
explicit counter, and both poles carry their generated source Hamiltonian energies. -/
theorem modeEM_direct_consumer (point : BasePoint) (side : Fin 2) :
    (∀ mu left,modeCurrentTensor point (fun j=>(sourceLockedField mu 2 j:ℂ)) mu
        left (side,1)=canonicalCurrentTensor point mu left (side,1))
    ∧ (∀ mu left,modeCurrentTensor point (fun j=>(sourceLockedField mu 2 j:ℂ)) mu
        left (side,3)=-canonicalCurrentTensor point mu left (side,3))
    ∧ (∀ mu,(modeCurrentTensor point (fun j=>(sourceLockedField mu 2 j:ℂ)) mu)*
        chargeMinus point=canonicalCurrentTensor point mu*chargeMinus point)
    ∧ (∀ mu,(modeCurrentTensor point (fun j=>(sourceLockedField mu 2 j:ℂ)) mu)*
        chargePlus point=-(canonicalCurrentTensor point mu*chargePlus point))
    ∧ modeCurrentTensor point (fun j=>(sourceLockedField 0 2 j:ℂ)) 0 (side,1) (side,1)=-1
    ∧ modeCurrentTensor point (fun j=>(sourceLockedField 0 2 j:ℂ)) 0 (side,3) (side,3)=1
    ∧ (modeCurrentTensor point (fun j=>(sourceLockedField 0 2 j:ℂ)) 0 (side,0) (side,0)=0
        ∧ canonicalCurrentTensor point 0 (side,0) (side,0)=-1)
    ∧ FullQuantum.hamiltonian Stage10.Runtime.configuration point 0
        (actualRestStatePreparation (side,1) (actual.matter point))=
        sourceRestPoleEnergy (sourceRestStatePole (side,1)) •
          actualRestStatePreparation (side,1) (actual.matter point)
    ∧ FullQuantum.hamiltonian Stage10.Runtime.configuration point 0
        (actualRestStatePreparation (side,3) (actual.matter point))=
        sourceRestPoleEnergy (sourceRestStatePole (side,3)) •
          actualRestStatePreparation (side,3) (actual.matter point):=
  ⟨fun mu left=>modeTensor_minus_column point mu left side,
    fun mu left=>modeTensor_plus_column point mu left side,
    fun mu=>modeTensor_minus_sector point mu,
    fun mu=>modeTensor_plus_sector point mu,
    modeTemporal_minus_unit point side,modeTemporal_plus_unit point side,
    modeEM_neutral_counter point side,
    modeCharge_minus_pole point side,modeCharge_plus_pole point side⟩

end LowEnergy.GaussComposite.PhysicalModeEMCurrent
