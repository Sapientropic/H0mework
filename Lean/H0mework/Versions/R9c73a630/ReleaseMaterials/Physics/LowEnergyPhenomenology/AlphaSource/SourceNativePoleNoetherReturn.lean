import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeOriginAction

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePoleChargeReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair StageNineHolonomicField Stage10 Stage10.CanonicalMatter
open SU7MotherLieAlgebra DiracExteriorMatterAction DiracCliffordRepresentation
open ChargedPreparation.Dynamics ChargedPreparation.SpatialSpectrum
open Electromagnetic Electromagnetic.ExternalState YangMills.FullPairing
open PreparationVacuumElectromagneticIdentity PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumPhysicalModeChargeRead
open PreparationPhysicalNativePhotonFluxReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumSoftPoleSelection SourceQuantumScalarChart
open CanonicalGradedSpatialSource Stage9DEF Stage9DEF.Compatibility
open FullQuantum FullSpace PreparationPhysicalChargedScatteringPoleReturn
open PreparationPhysicalChargedPacketQuantumReturn MeasureTheory Filter
open scoped Matrix BigOperators InnerProductSpace Topology
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three
attribute [local irreducible] actualRestStatePreparation sourceModeCurrent sourceModeCurrentDirection

/-- The full original density action is evaluated on the actual native endpoint gauge field. -/
def sourceNativeOriginDensityAction (branch : Fin 2) : YangMills.FullPairing.Mother :=
  ∑mu : Fin 4,sourceGaugeDensityAction mu
    (p286CoordinateEquiv.symm (fieldGauge (sourceNativeOriginReal branch) mu))

def sourceNativeOriginRestMixing (branch : Fin 2) : Matrix RestStateIndex RestStateIndex ℂ :=
  ∑mu : Fin 4,sourceRestGaugeVertexMixing mu
    (p286CoordinateEquiv.symm (fieldGauge (sourceNativeOriginReal branch) mu))

/-- Every external pair is the original prepared primal and repaired independent dual, with its original action coefficient. -/
theorem sourceNativeOriginNoether_pair (branch : Fin 2) (point : BasePoint) (left right : RestStateIndex) :
    actual.conjugateMatter point (canonicalDual (actualRestStatePreparation left)
      (sourceNativeOriginDensityAction branch (actualRestStatePreparation right (actual.matter point))))=
      (ActionNormalization.phaseMomentum:ℂ)*sourceNativeOriginRestMixing branch left right := by
  unfold sourceNativeOriginDensityAction sourceNativeOriginRestMixing
  simp only [LinearMap.sum_apply,map_sum,Matrix.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  exact actualRestState_gaugeDensity_mixing mu _ point left right

private theorem gauge_matrix_scale (mu : Fin 4) (direction : P286LieBlockData) (r : ℝ)
    (row column : Source.Index) :
    sourceGaugeVertexMatrix mu (r • direction) row column=(r:ℂ)*sourceGaugeVertexMatrix mu direction row column := by
  change sourceGaugeDensityWeight mu*(-((diracGammaZero*diracGamma mu) row.1 column.1))*Complex.I*
    ((r:ℂ)*(direction.1.val (row.2.castLE (by decide)) (column.2.castLE (by decide)))+
      if row.2=column.2 then (r:ℂ)*direction.2.2.1 else 0)=_
  unfold sourceGaugeVertexMatrix
  split_ifs <;> ring

private theorem gauge_mixing_scale (mu : Fin 4) (direction : P286LieBlockData) (r : ℝ)
    (left right : RestStateIndex) :
    sourceRestGaugeVertexMixing mu (r • direction) left right=
      (r:ℂ)*sourceRestGaugeVertexMixing mu direction left right := by
  have matrix : sourceGaugeVertexMatrix mu (r • direction)=(r:ℂ) • sourceGaugeVertexMatrix mu direction := by
    ext row column
    exact gauge_matrix_scale mu direction r row column
  simp only [sourceRestGaugeVertexMixing,matrix,Matrix.smul_mulVec,Pi.smul_apply,smul_eq_mul]
  have term (i : Source.Index) :
      star (sourceRestStateValues left i)*((r:ℂ)*(sourceGaugeVertexMatrix mu direction*ᵥsourceRestStateValues right) i)=
        (r:ℂ)*(star (sourceRestStateValues left i)*(sourceGaugeVertexMatrix mu direction*ᵥsourceRestStateValues right) i) := by ring
  simp_rw [term]
  rw [←Finset.mul_sum]
  ring

private theorem gauge_mixing_neg (mu : Fin 4) (direction : P286LieBlockData) (left right : RestStateIndex) :
    sourceRestGaugeVertexMixing mu (-direction) left right= -sourceRestGaugeVertexMixing mu direction left right := by
  have negative : (-1:ℝ) • direction= -direction := neg_one_smul ℝ direction
  simpa only [negative,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using
    gauge_mixing_scale mu direction (-1) left right

private theorem gauge_mixing_zero (mu : Fin 4) (left right : RestStateIndex) :
    sourceRestGaugeVertexMixing mu 0 left right=0 := by
  have matrix : sourceGaugeVertexMatrix mu 0=0 := by
    ext row column
    simp [sourceGaugeVertexMatrix]
  simp only [sourceRestGaugeVertexMixing,matrix,Matrix.zero_mulVec,Pi.zero_apply,mul_zero,Finset.sum_const_zero]

private theorem gauge_matrix_color (mu : Fin 4) (g : Fin 3) (row column : Source.Index) :
    sourceGaugeVertexMatrix mu (sourceColorP286Generator g) row column=
      sourceGaugeDensityWeight mu*(-((diracGammaZero*diracGamma mu) row.1 column.1))*Complex.I*
        sourceColorPauli g row.2 column.2 := by
  unfold sourceGaugeVertexMatrix
  rw [sourceColorP286Generator_topLeft,sourceColorP286Generator_hypercharge_zero]
  simp

/-- This full-eight matrix includes the opposite side and all singlet/triplet transitions. -/
def sourceNativeOriginTransition (left right : RestStateIndex) : ℂ :=
  if left.1=right.1 then
    (if left.1=0 then (2:ℂ)*Complex.I*(lapse:ℂ) else -((2:ℂ)*Complex.I*(lapse:ℂ)))*
      ((if left.2=0 ∧ right.2=2 then 1 else 0)-(if left.2=2 ∧ right.2=0 then 1 else 0)) else 0

private theorem color_source_matrix :
    sourceGaugeVertexMatrix 1 (sourceColorP286Generator 1)-sourceGaugeVertexMatrix 2 (sourceColorP286Generator 0)=
      (Complex.I*(lapse:ℂ)) •
        (Matrix.single (0,1) (1,0) 1-Matrix.single (1,0) (0,1) 1-
          Matrix.single (2,1) (3,0) 1+Matrix.single (3,0) (2,1) 1) := by
  ext row column
  rcases row with ⟨spinL,colorL⟩
  rcases column with ⟨spinR,colorR⟩
  fin_cases spinL <;> fin_cases colorL <;> fin_cases spinR <;> fin_cases colorR <;>
    norm_num [Matrix.sub_apply,gauge_matrix_color,sourceGaugeDensityWeight,sourceColorPauli,
      diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,Matrix.mul_apply,Fin.sum_univ_four,
      Matrix.single_apply,Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,Fin.ext_iff]
  all_goals (ring_nf; simp only [Complex.I_pow_three]; ring)

private theorem rest_values (state : RestStateIndex) (index : Source.Index) :
    sourceRestStateValues state index=
      if state.1=0 then
        if index.1=0 then (if index.2=0 then sourceRestStateCoefficients state.2 0 else sourceRestStateCoefficients state.2 1)
        else if index.1=1 then (if index.2=0 then sourceRestStateCoefficients state.2 2 else sourceRestStateCoefficients state.2 3) else 0
      else
        if index.1=2 then (if index.2=0 then sourceRestStateCoefficients state.2 0 else sourceRestStateCoefficients state.2 1)
        else if index.1=3 then (if index.2=0 then sourceRestStateCoefficients state.2 2 else sourceRestStateCoefficients state.2 3) else 0 := by
  rcases state with ⟨side,state⟩
  rcases index with ⟨spin,color⟩
  fin_cases side <;> fin_cases state <;> fin_cases spin <;> fin_cases color <;> rfl

private theorem rest_coefficients (state index : Fin 4) :
    sourceRestStateCoefficients state index=
      if state=0 then (if index=1 then 1 else if index=2 then -1 else 0)
      else if state=1 then (if index=0 then (spinScale:ℂ) else 0)
      else if state=2 then (if index=1 ∨ index=2 then 1 else 0)
      else (if index=3 then (spinScale:ℂ) else 0) := by
  fin_cases state <;> fin_cases index <;> rfl

private theorem color_transition (left right : RestStateIndex) :
    (2:ℂ)*(sourceRestGaugeVertexMixing 1 (sourceColorP286Generator 1) left right-
      sourceRestGaugeVertexMixing 2 (sourceColorP286Generator 0) left right)=sourceNativeOriginTransition left right := by
  unfold sourceRestGaugeVertexMixing
  have scalar (a b : ℂ) : (2:ℂ)*((1/2)*a-(1/2)*b)=a-b := by ring
  rw [scalar,←Finset.sum_sub_distrib]
  simp_rw [←mul_sub]
  have difference (i : Source.Index) :
      (sourceGaugeVertexMatrix 1 (sourceColorP286Generator 1)*ᵥsourceRestStateValues right) i-
        (sourceGaugeVertexMatrix 2 (sourceColorP286Generator 0)*ᵥsourceRestStateValues right) i=
      ((sourceGaugeVertexMatrix 1 (sourceColorP286Generator 1)-sourceGaugeVertexMatrix 2 (sourceColorP286Generator 0))*ᵥ
        sourceRestStateValues right) i := by rw [Matrix.sub_mulVec];rfl
  simp_rw [difference]
  rw [color_source_matrix,Matrix.smul_mulVec]
  have scalarTerm (i : Source.Index) :
      star (sourceRestStateValues left i)*
        ((Complex.I*(lapse:ℂ)) •
          ((Matrix.single (0,1) (1,0) 1-Matrix.single (1,0) (0,1) 1-
            Matrix.single (2,1) (3,0) 1+Matrix.single (3,0) (2,1) 1)*ᵥsourceRestStateValues right)) i=
      (Complex.I*(lapse:ℂ))*(star (sourceRestStateValues left i)*
        (((Matrix.single (0,1) (1,0) 1-Matrix.single (1,0) (0,1) 1-
          Matrix.single (2,1) (3,0) 1+Matrix.single (3,0) (2,1) 1)*ᵥsourceRestStateValues right) i)) := by
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  simp_rw [scalarTerm]
  rw [←Finset.mul_sum]
  simp only [Matrix.add_mulVec,Matrix.sub_mulVec,Pi.add_apply,Pi.sub_apply,mul_add,mul_sub,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have single (a b : Source.Index) :
      (∑i : Source.Index,star (sourceRestStateValues left i)*
        (Matrix.single a b 1*ᵥsourceRestStateValues right) i)=
      star (sourceRestStateValues left a)*sourceRestStateValues right b := by
    rw [Matrix.single_mulVec]
    simp [Function.update_apply,mul_ite]
  rw [single,single,single,single]
  clear scalar difference scalarTerm single
  rcases left with ⟨sideL,stateL⟩
  rcases right with ⟨sideR,stateR⟩
  fin_cases sideL <;> fin_cases sideR <;> fin_cases stateL <;> fin_cases stateR <;>
    simp only [rest_values,rest_coefficients,sourceNativeOriginTransition]
  all_goals norm_num [Fin.ext_iff]
  all_goals ring

/-- The endpoint's original two spatial generators generate the complete current matrix; no scalar electromagnetic charge is supplied. -/
theorem sourceNativeOriginRestMixing_generated (branch : Fin 2) (left right : RestStateIndex) :
    sourceNativeOriginRestMixing branch left right=
      if branch=0 then (sourceNativeOriginGaugeWeight:ℂ)*sourceNativeOriginTransition left right else 0 := by
  unfold sourceNativeOriginRestMixing
  simp only [Matrix.sum_apply]
  simp_rw [sourceNativeOriginReal_gauge]
  by_cases active : branch=0
  · simp only [if_pos active]
    simp only [Fin.sum_univ_four]
    simp only [Fin.reduceEq,if_false,if_true,sub_zero,zero_sub,sub_self,smul_zero,map_zero,map_smul,map_neg]
    rw [sourceNativeOrigin_unit_zero,sourceNativeOrigin_unit_one]
    simp only [gauge_mixing_neg,gauge_mixing_scale,gauge_mixing_zero,add_zero,zero_add]
    rw [←color_transition left right]
    push_cast
    ring
  · simp only [if_neg active,map_zero,gauge_mixing_zero,Finset.sum_const_zero]

/-- Rest 1/3 cancellation is a theorem about these original makers; the full filtered packet is still read by the complete operator. -/
theorem sourceNativeOriginRestMixing_charged (branch : Fin 2) (left : RestStateIndex) (side edge : Fin 2) :
    sourceNativeOriginRestMixing branch left
      (PreparationVacuumPhysicalQuantumLockedCharge.sourceChargedRestIndex side edge)=0 := by
  rw [sourceNativeOriginRestMixing_generated]
  fin_cases edge <;> simp [sourceNativeOriginTransition,
    PreparationVacuumPhysicalQuantumLockedCharge.sourceChargedRestIndex]

/-- The current pole's charged component uses its generated first jet and actual remainder, while retaining the full other-current contribution. -/
theorem sourceNativePoleCurrent_minus (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) (mu : Fin 4) (point : BasePoint) (side : Fin 2) :
    sourceModeCurrent (sourceNativeFrequencyPolarization branch epsilon s n) mu
      (actualRestStatePreparation (side,1) (actual.matter point))=
      ((epsilon:ℂ)^2*sourceChargedCoefficient (sourcePoleJetField branch epsilon s n) mu+
        sourceChargedCoefficient (sourcePoleFrameResidual branch epsilon s n) mu) •
          currentAction mu HyperchargeResponse.chargeDirection
            (actualRestStatePreparation (side,1) (actual.matter point))+
      sourceModeCurrent (sourceChargedFieldRemainder (sourceNativeFrequencyPolarization branch epsilon s n)) mu
        (actualRestStatePreparation (side,1) (actual.matter point)) := by
  rw [sourceChargedCurrent_minus,sourceNativeFrequencyPolarization_charge branch epsilon s n nonzero]

theorem sourceNativePoleCurrent_plus (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) (mu : Fin 4) (point : BasePoint) (side : Fin 2) :
    sourceModeCurrent (sourceNativeFrequencyPolarization branch epsilon s n) mu
      (actualRestStatePreparation (side,3) (actual.matter point))=
      -(((epsilon:ℂ)^2*sourceChargedCoefficient (sourcePoleJetField branch epsilon s n) mu+
        sourceChargedCoefficient (sourcePoleFrameResidual branch epsilon s n) mu) •
          currentAction mu HyperchargeResponse.chargeDirection
            (actualRestStatePreparation (side,3) (actual.matter point)))+
      sourceModeCurrent (sourceChargedFieldRemainder (sourceNativeFrequencyPolarization branch epsilon s n)) mu
        (actualRestStatePreparation (side,3) (actual.matter point)) := by
  rw [sourceChargedCurrent_plus,sourceNativeFrequencyPolarization_charge branch epsilon s n nonzero]

/-- The filtered observable uses this exact original canonical density action, with both actual preparation maps. -/
def sourceNativeOriginCanonicalFiber (branch : Fin 2) : FiberOperators :=
  operator (phaseInverse.comp (sourceNativeOriginDensityAction branch))

def sourceNativeOriginPoleCurrent (branch : Fin 2) (sideL edgeL sideR edgeR : Fin 2) (k : Position) : ℂ :=
  ∑left : RestStateIndex,∑right : RestStateIndex,
    star (sourceActualPreparedPoleWeight sideL edgeL k left)*sourceActualPreparedPoleWeight sideR edgeR k right*
      inner ℂ (naturalCoordinates (embed (sourceMovingPoleValues (physicalMomentum k) left)))
        (sourceNativeOriginCanonicalFiber branch
          (naturalCoordinates (embed (sourceMovingPoleValues (physicalMomentum k) right))))

private theorem filtered_pole_current (branch : Fin 2) (sideL edgeL sideR edgeR : Fin 2) :
    (fun k=>inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
      (fourier ((sourceNativeOriginCanonicalFiber branch).compLpL 2 volume
        (sourceChargedFilteredPacket sideR edgeR)) k))=ᵐ[volume]
      sourceNativeOriginPoleCurrent branch sideL edgeL sideR edgeR := by
  rw [GaugeGreen.constant_fourier]
  filter_upwards [sourceActualFilteredPacket_poles sideL edgeL,sourceActualFilteredPacket_poles sideR edgeR,
    (sourceNativeOriginCanonicalFiber branch).coeFn_compLpL (fourier (sourceChargedFilteredPacket sideR edgeR))]
    with k left right acted
  rw [acted,left,right]
  simp only [map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    starRingEnd_apply,sourceNativeOriginPoleCurrent,mul_assoc,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro leftState _
  apply Finset.sum_congr rfl
  intro rightState _
  ring

/-- The aggregate eight-by-eight expression is integrable for the same full filtered states. -/
theorem sourceNativeOriginPoleCurrent_integrable (branch : Fin 2) (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (sourceNativeOriginPoleCurrent branch sideL edgeL sideR edgeR) volume :=
  (L2.integrable_inner (𝕜:=ℂ) _ _).congr (filtered_pole_current branch sideL edgeL sideR edgeR)

/-- The same Phi read keeps the full source spectra and every cross term; the rest-state cancellation is not imposed on the prepared packet. -/
theorem sourceNativeOriginFilteredRead_poles (branch : Fin 2) (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedQuantumRead sideL edgeL sideR edgeR
      ((sourceNativeOriginCanonicalFiber branch).compLpL 2 volume)=
        ∫k,sourceNativeOriginPoleCurrent branch sideL edgeL sideR edgeR k := by
  rw [sourceChargedQuantumRead_generated,←fourier.inner_map_map,L2.inner_def]
  exact integral_congr_ae (filtered_pole_current branch sideL edgeL sideR edgeR)

/-- The physical Noether current uses the original density reader and original four-spin coefficient on the actual filtered legs. -/
def sourceNativeOriginFilteredCurrent (branch : Fin 2) (sideL edgeL sideR edgeR : Fin 2) (x : Position) : ℂ :=
  (4*(spinScale:ℂ))*inner ℂ (sourceChargedFilteredPacket sideL edgeL x)
    (CanonicalPacket.densityReader (sourceNativeOriginDensityAction branch)
      (sourceChargedFilteredPacket sideR edgeR x))

/-- The action-unit factor is returned by the original phaseMomentum source identity, not supplied as a field normalization. -/
theorem sourceNativeOriginFilteredCurrent_quantum (branch : Fin 2) (sideL edgeL sideR edgeR : Fin 2) :
    (∫x,sourceNativeOriginFilteredCurrent branch sideL edgeL sideR edgeR x)=
      (ActionNormalization.phaseMomentum:ℂ)*sourceChargedQuantumRead sideL edgeL sideR edgeR
        ((sourceNativeOriginCanonicalFiber branch).compLpL 2 volume) := by
  rw [sourceChargedQuantumRead_generated,L2.inner_def]
  simp only [sourceNativeOriginFilteredCurrent,ActionNormalization.phaseMomentum_source,
    Complex.ofReal_mul,Complex.ofReal_ofNat,integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [(sourceNativeOriginCanonicalFiber branch).coeFn_compLpL
    (sourceChargedFilteredPacket sideR edgeR)] with x actual
  rw [actual]
  rfl

theorem sourceNativeOriginFilteredCurrent_poles (branch : Fin 2) (sideL edgeL sideR edgeR : Fin 2) :
    (∫x,sourceNativeOriginFilteredCurrent branch sideL edgeL sideR edgeR x)=
      (ActionNormalization.phaseMomentum:ℂ)*∫k,sourceNativeOriginPoleCurrent branch sideL edgeL sideR edgeR k := by
  rw [sourceNativeOriginFilteredCurrent_quantum,sourceNativeOriginFilteredRead_poles]

end LowEnergy.PreparationPhysicalNativePoleChargeReturn
