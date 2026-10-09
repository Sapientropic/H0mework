import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstGaugeRepresentation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstPoleGaugeVertex
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalNormalizedFullField PreparationPhysicalPoleChargeMatrix PreparationPhysicalCurvatureSheetLimit
open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationPhysicalPhaseGaugeRealization PreparationPhysicalActualGaussChargeCurrent
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumPhysicalFeedback PreparationVacuumSourceFieldFamily
open PreparationVacuumGaugeSourceInjection PreparationVacuumLowerClassical PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic PreparationVacuumElectromagneticIdentity
open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor
open SourceQuantumScalarChart GaussNativeMatter GaussHistoryHilbert
open FullQuantum.CoframeResponse FullQuantum.StateGreen CanonicalGradedSpatialSource
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineHolonomicField StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair
open Stage9C.Dynamics.Homogeneous DiracCliffordRepresentation DiracExteriorMatterAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory YangMills.FullPairing Electromagnetic.CanonicalCoframe
open PointwiseLorentzianCoframeJet PointwiseDiracSpinConnectionLift
open Filter Set
open scoped Matrix BigOperators Topology InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
local instance : DecidableEq Quantum.Index:=Classical.decEq _

/-- The energy action is the negative of the original density-to-canonical current action on each actual gauge axis. -/
def sourceFirstEnergyAction (k : Fin 4) : Mother :=
  -(∑mu : Fin 4,sourceGaugeCanonicalAction mu (p286CoordinateEquiv.symm (sourceFirstGaugeConnection k mu)))

def sourceFirstEnergyAxisEight (k : Fin 4) : Matrix Stage9DEF.Source.Index Stage9DEF.Source.Index ℂ :=
  -(∑mu : Fin 4,sourceGaugeVertexMatrix mu (p286CoordinateEquiv.symm (sourceFirstGaugeConnection k mu)))

def sourceFirstEnergyEight (v : Fin 4→ℂ) : Matrix Stage9DEF.Source.Index Stage9DEF.Source.Index ℂ :=
  ∑k : Fin 4,v k • sourceFirstEnergyAxisEight k

private theorem operatorMatrix_neg (A : Mother) :
    Quantum.operatorMatrix (-A)= -Quantum.operatorMatrix A := by
  ext i j
  simp only [Quantum.operatorMatrix,LinearMap.toMatrixAlgEquiv_apply,LinearMap.neg_apply,
    map_neg,Finsupp.neg_apply,Matrix.neg_apply]

private theorem canonical_matrix (mu : Fin 4) (a : NativeLie) :
    Quantum.operatorMatrix (sourceGaugeCanonicalAction mu (p286CoordinateEquiv.symm a))=
      -((lapse:ℂ)*Complex.I) •
        ((spinCoordinates diracGammaZero*
          spinCoordinates (inverseCoframeDiracGamma {coframe:=homogeneousCoframe lapse,derivative:=0} mu))*
            nativePrimal a) := by
  change Quantum.operatorMatrix ((-(diracMatrixMatterAction diracGammaZero)).comp
    (((lapse:ℂ)*Complex.I) • (diracMatrixMatterAction
      (inverseCoframeDiracGamma {coframe:=homogeneousCoframe lapse,derivative:=0} mu)).comp
        (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm a)))))=_
  rw [LinearMap.comp_smul,map_smul,Quantum.matrix_composition,operatorMatrix_neg,Quantum.matrix_composition]
  change ((lapse:ℂ)*Complex.I) •
    (-(spinCoordinates diracGammaZero)*(spinCoordinates
      (inverseCoframeDiracGamma {coframe:=homogeneousCoframe lapse,derivative:=0} mu)*nativePrimal a))=_
  simp only [neg_mul,smul_neg,neg_smul,mul_assoc]

private theorem principal_inverse :
    Ring.inverse (principalMatrix (Stage9C.Material.SpinPair.actual.coframe 0))=
      (Complex.I*(lapse:ℂ)) • spinCoordinates diracGammaZero := by
  rw [principal_inverse_original _ (FullQuantum.actual_noncharacteristic 0),actual_coframe,
    InducedQuantum.lapse_temporal_inverse lapse lapse_pos.ne',map_smul]
  rfl

/-- The sign and physical lapse follow from the actual principal inverse; they are not assigned to the vertex. -/
theorem sourceFirstEnergyAction_matrix (k : Fin 4) :
    Quantum.operatorMatrix (sourceFirstEnergyAction k)=
      (-Complex.I) • (Ring.inverse (principalMatrix (Stage9C.Material.SpinPair.actual.coframe 0))*
        (∑mu : Fin 4,coefficientMatrix mu (Stage9C.Material.SpinPair.actual.coframe 0)*
          nativePrimal (sourceFirstGaugeConnection k mu))) := by
  simp only [sourceFirstEnergyAction,operatorMatrix_neg,map_sum,canonical_matrix,neg_smul,Finset.sum_neg_distrib,neg_neg]
  rw [principal_inverse]
  simp only [coefficientMatrix,actual_coframe,Finset.mul_sum,mul_smul_comm,smul_mul_assoc,smul_smul,Finset.smul_sum]
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro mu _
  simp only [mul_assoc,←neg_smul]
  congr 1
  calc
    (lapse:ℂ)*Complex.I= -(Complex.I*Complex.I)*(lapse:ℂ)*Complex.I := by
      rw [Complex.I_mul_I]
      ring
    _= -(Complex.I*(Complex.I*(Complex.I*(lapse:ℂ)))) := by ring

/-- The original all-eight action is consumed before taking any four-state restriction. -/
theorem sourceFirstEnergyAction_coordinates (k : Fin 4) (values : Stage9DEF.Source.Index→ℂ)
    (row : Stage9DEF.Source.Index) :
    Stage9DEF.Compatibility.coordinates (sourceFirstEnergyAction k (Stage9DEF.Compatibility.embed values)) row=
      (sourceFirstEnergyAxisEight k*ᵥvalues) row := by
  simp only [sourceFirstEnergyAction,LinearMap.neg_apply,LinearMap.sum_apply,map_neg,map_sum,
    Pi.neg_apply,Finset.sum_apply,sourceGaugeCanonicalAction_coordinates,sourceFirstEnergyAxisEight,
    Matrix.neg_mulVec,Matrix.sum_mulVec]

/-- Every temporal, spatial and transverse coefficient is retained in the actual eight-state matrix. -/
theorem sourceFirstEnergyAxisEight_generated (k : Fin 4) (row column : Stage9DEF.Source.Index) :
    sourceFirstEnergyAxisEight k row column=
      -(∑mu : Fin 4,sourceGaugeDensityWeight mu*(-((diracGammaZero*diracGamma mu) row.1 column.1))*Complex.I*
        sourceFirstGaugeDoublet k mu row.2 column.2) := by
  simp only [sourceFirstEnergyAxisEight,Matrix.neg_apply,Matrix.sum_apply,sourceGaugeVertexMatrix,
    sourceFirstGaugeDoublet_generated]

theorem sourceFirstLiteralEnergy_generated (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    sourceLiteralEnergyWeight p (sourceState sourcePoint.val) v 1=
      ∑k : Fin 4,v k • SourceRealScalarFock.branches (Quantum.operatorMatrix (sourceFirstEnergyAction k)) := by
  rw [sourceLiteralEnergyWeight_axes]
  apply Finset.sum_congr rfl
  intro k _
  rw [sourceLiteralEnergyWeight_axis p _ (PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint),
    sourceFirstGauge_axis_energy,sourceState_event,←sourceFirstEnergyAction_matrix]

private theorem eight_operator_entry (A : Mother) (i j : Stage9DEF.Source.Index) :
    Quantum.operatorMatrix A (sourceFirstEightIndex i) (sourceFirstEightIndex j)=
      Stage9DEF.Compatibility.coordinates (A (Stage9DEF.Compatibility.embed (Pi.single j 1))) i := by
  rw [Quantum.operatorMatrix,LinearMap.toMatrixAlgEquiv_apply,sourceFirstEightBasis]
  simp only [Quantum.wholeBasis,Pi.basis_repr,Quantum.internalBasis,Module.Basis.prod_repr_inl,Module.Basis.prod_repr_inr,
    sourceFirstEightIndex,Stage9DEF.Compatibility.coordinates,sourceColorDoubletDual]
  rfl

/-- Both endpoints are the actual four Gauss/fullCAR columns, with their paid source normalization. -/
def sourceFirstEnergyFour (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    Matrix ActualPreparedIndex ActualPreparedIndex ℂ :=
  fun i j=>sourceLiteralEnergyCoefficient epsilon precision p (sourceState sourcePoint.val) v 1 i.1 i.2 j.1 j.2

theorem sourceFirstEnergyFour_generated (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum) (v : Fin 4→ℂ)
    (i j : ActualPreparedIndex) :
    sourceFirstEnergyFour epsilon precision p v i j=
      sourceFirstEnergyEight v (sourceChargedBasisIndex i.1 i.2) (sourceChargedBasisIndex j.1 j.2) := by
  simp only [sourceFirstEnergyFour,sourceLiteralEnergyCoefficient,sourceChargedEnergyRead_entry,
    sourceFirstLiteralEnergy_generated,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  change (∑k : Fin 4,v k*Quantum.operatorMatrix (sourceFirstEnergyAction k)
    (sourceFirstEightIndex (sourceChargedBasisIndex i.1 i.2))
    (sourceFirstEightIndex (sourceChargedBasisIndex j.1 j.2)))=_
  simp only [eight_operator_entry,sourceFirstEnergyAction_coordinates,Matrix.mulVec_single_one,
    Matrix.col_apply,sourceFirstEnergyEight,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]

/-- This coefficient retains the neutral spatial response instead of assigning a charge label to the whole vertex. -/
def sourceFirstPreparedCoefficient (v : Fin 4→ℂ) (i : ActualPreparedIndex) : ℂ :=
  v 0*(sourceActualPhaseCharge i.2:ℂ)-
    (lapse:ℂ)*v 3*(if i.1=i.2 then 1 else -1)*(if i.2=0 then (61/67:ℂ) else -6/67)

theorem sourceFirstEnergyFour_value (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    sourceFirstEnergyFour epsilon precision p v=Matrix.diagonal (sourceFirstPreparedCoefficient v) := by
  ext i j
  rw [sourceFirstEnergyFour_generated]
  rcases i with ⟨side,edge⟩
  rcases j with ⟨other,opposite⟩
  simp only [sourceFirstEnergyEight,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,sourceFirstEnergyAxisEight_generated]
  fin_cases side <;> fin_cases edge <;> fin_cases other <;> fin_cases opposite <;>
    norm_num only [Fin.sum_univ_four,sourceGaugeDensityWeight,sourceFirstGaugeDoublet,
      sourceFirstGaugeCoefficients,sourceFirstTemporalCoefficients,sourceFirstSpatialCoefficients,
      sourceFirstLongitudinalCoefficients,sourceChargedBasisIndex,sourceFirstPreparedCoefficient,
      sourceActualPhaseCharge,Matrix.diagonal_apply,Prod.mk.injEq,Pi.add_apply,Pi.single_apply,
      ite_apply,Pi.zero_apply,Fin.ext_iff] <;>
    norm_num [Matrix.mul_apply,Fin.sum_univ_four,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,Matrix.cons_val,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

/-- The actual temporal vertex consumes the original absolute phase charge on the same Gauss preparation. -/
theorem sourceFirstTemporal_absolute (q : PhysicalResponsePoint) (p : PhysicalMomentum) :
    (Stage10.ActionNormalization.phaseMomentum:ℂ) • sourceFirstEnergyFour q.epsilon q.precision p (Pi.single 0 1)=
      sourcePreparedCurrentMatrix q sourceAbsoluteCharge := by
  rw [sourceFirstEnergyFour_value,sourcePreparedChargeUnit_generated]
  congr 1
  ext i j
  simp only [sourcePreparedChargeUnitMatrix,Matrix.diagonal_apply,sourceFirstPreparedCoefficient,Pi.single_eq_same]
  norm_num [Pi.single_apply,show (3:Fin 4)≠0 by decide]

/-- The temporal agreement does not erase the complete source-generated spatial matrix difference. -/
theorem sourceFirstEnergyFour_charge_difference (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    sourceFirstEnergyFour epsilon precision p v-v 0 • sourcePreparedChargeUnitMatrix=
      Matrix.diagonal (fun i=> -(lapse:ℂ)*v 3*(if i.1=i.2 then 1 else -1)*(if i.2=0 then (61/67:ℂ) else -6/67)) := by
  rw [sourceFirstEnergyFour_value]
  ext i j
  simp only [Matrix.sub_apply,sourcePreparedChargeUnitMatrix,Matrix.smul_apply,Matrix.diagonal_apply,
    sourceFirstPreparedCoefficient,smul_eq_mul]
  split_ifs <;> ring

private theorem first_jet_read (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (v : Fin 4→ℂ) (a : ℂ) (i j : ActualPreparedIndex) :
    sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
      (sourceChargedNativeFrameJet v*ᵥPi.single (1:Fin 289) a)=
      a*sourceFirstEnergyFour epsilon precision p v i j := by
  simp only [sourceFullEnergyRead,sourceFirstEnergyFour,sourceLiteralEnergyCoefficient,sourceChargedEnergyRead_entry]
  rw [sourceLiteralEnergyWeight_generated]
  simp only [sourceFullEnergyMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.mulVec_single,
    op_smul_eq_smul,Pi.smul_apply,Matrix.col_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have column : (⟨(1:Fin 3).val,by decide⟩:Fin 289)=(1:Fin 289) := by decide
  rw [column]
  ring

/-- The same branch0 full field consumes its actual moving cofactor, fast and residual prices; the actual origin remains explicit. -/
theorem sourceFirstPoleEnergy_limit (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (i j : ActualPreparedIndex) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet 0 n unit e.val:ℂ))*
      (sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourceNativeFrequencyPolarization 0 e.val (sourceSheet 0 n unit e.val) n)-
       sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourcePoleOriginField 0 e.val (sourceSheet 0 n unit e.val) n))/(e.val:ℂ)^2)
      scaleApproach (𝓝 ((softCoefficient 0:ℂ)*
        Matrix.diagonal (sourceFirstPreparedCoefficient (physicalFrequencyMomentum (sourceSpeed 0) n)) i j)) := by
  have original:=sourcePoleEnergy_first_limit epsilon precision p i j 0 n unit
  change Tendsto _ _ (𝓝 (sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
    (sourceChargedNativeFrameJet (physicalFrequencyMomentum (sourceSpeed 0) n)*ᵥ
      Pi.single (1:Fin 289) (softCoefficient 0:ℂ)))) at original
  simpa only [first_jet_read,sourceFirstEnergyFour_value] using original

private theorem energy_read_smul (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (i j : ActualPreparedIndex) (z : ℂ) (V : Fin 289→ℂ) :
    sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2 (z • V)=
      z*sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2 V := by
  simp only [sourceFullEnergyRead,sourceChargedEnergyRead_entry,sourceFullEnergyMatrix,
    Matrix.sum_apply,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The physical first-pole field emitted by the original full current directly consumes this complete energy/charge matrix. -/
theorem sourceFirstPoleCurrent_energy (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (pL pR : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum) (i j : ActualPreparedIndex) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet 0 n unit e.val:ℂ))*
      (sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourcePhaseGaugePhotonField q sL eL sR eR pL pR lambda T e.val (sourceSheet 0 n unit e.val) n)-
       sourcePhotonLeftReader 0 e.val (sourceSheet 0 n unit e.val) n
         (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T)*
       sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourcePoleOriginField 0 e.val (sourceSheet 0 n unit e.val) n)))
      scaleApproach (𝓝 (sourceCurvatureEmitterInput
        (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T) (residueIndex 0)*
        ((softCoefficient 0:ℂ)*Matrix.diagonal
          (sourceFirstPreparedCoefficient (physicalFrequencyMomentum (sourceSpeed 0) n)) i j))) := by
  have left:=sourcePhotonLeftReader_sheet 0 n unit (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T)
  have right:=sourceFirstPoleEnergy_limit epsilon precision p i j n unit
  have generated:=left.mul right
  apply generated.congr'
  filter_upwards [sourcePhaseGaugePhotonField_factor q sL eL sR eR pL pR lambda T 0 n unit] with e factor
  rw [factor,energy_read_smul]
  have nonzero : (e.val:ℂ)≠0:=Complex.ofReal_ne_zero.mpr e.property.1.ne'
  field_simp [nonzero]

end LowEnergy.PreparationPhysicalFirstPoleGaugeVertex
