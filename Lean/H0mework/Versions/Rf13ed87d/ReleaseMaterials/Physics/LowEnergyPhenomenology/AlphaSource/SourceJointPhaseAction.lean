import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceDressedPhotonCoupling
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhaseGaugeGenerator
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeVertexCore

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalJointEMCouplingUnitReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalDressedSpinChargeReturn PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalNativePhaseChargeInventory PreparationVacuumNativeFieldInjection
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice
open DiracExteriorMatterAction StageNineHolonomicField StageNineDynamicBreakingVacuum
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open StageNineExteriorMotherLieRepresentation StageNineP286GaugeConnectionVariation
open GaussComposite Electromagnetic.Identification GaussNativeMatter
open GaussFockLift GaussCoreHilbert GaussCoreDifferential CanonicalGradedCharge GaussQuantumMultiplier
open CanonicalGradedCurrent GaussDensityCore GaussComposite.SourceGraph
open PreparationVacuumFullFieldRiesz PreparationVacuumFieldCovector PreparationVacuumSourcePreparedResponse
open CanonicalGradedSpatialSource CanonicalPhysicalYResolvent
open scoped BigOperators Matrix ContDiff InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ FiberOp:=NormedAlgebra.restrictScalars ℝ ℂ _

/-- The generator is the already-generated original phase-gauge direction. -/
def sourceJointMother : SU7MotherLieMatrix:=nativeMother sourcePhaseGaugeLie

def sourceJointExteriorWeight {degree : ℕ} (i : ExteriorBasisIndex degree) : ℚ :=
  -sourceExteriorWeight i-(exteriorHyperchargeWeight i:ℚ)/2

private def originalCoordinates : NativeLie→ₗ[ℝ]P286CoordinateCarrier where
  toFun a:=a
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

private def originalDecoder : NativeLie→ₗ[ℝ]P286LieBlockData :=
  p286CoordinateEquiv.symm.toLinearMap.comp originalCoordinates

private theorem mother_split : sourceJointMother=
    (-1:ℝ) • p286LieBlockEmbed (Stage9C.Material.SpinPair.sourceColorP286Generator 2)+
      (-1/2:ℝ) • p286LieBlockEmbed Stage10.HyperchargeResponse.chargeDirection := by
  change p286LieBlockEmbed (originalDecoder (-SourceQuantumResidualGaugeSlice.colorGenerator 2-
    (1/2:ℝ) • GaussComposite.nativeY))=_
  rw [originalDecoder.map_sub,originalDecoder.map_neg,originalDecoder.map_smul]
  have color : originalDecoder (SourceQuantumResidualGaugeSlice.colorGenerator 2)=
      Stage9C.Material.SpinPair.sourceColorP286Generator 2 := p286CoordinateEquiv.symm_apply_apply _
  have hyper : originalDecoder GaussComposite.nativeY=Stage10.HyperchargeResponse.chargeDirection :=
    p286CoordinateEquiv.symm_apply_apply _
  rw [color,hyper,p286LieBlockEmbed_sub,p286LieBlockEmbed_neg,
    StageNineP286GaugeConnectionVariation.p286LieBlockEmbed_real_smul]
  module

/-- All exterior sectors are retained; the scalar and matter restrictions are later consumers. -/
theorem sourceJoint_exterior (degree : ℕ) (i : ExteriorBasisIndex degree) :
    exteriorMotherLieAction degree sourceJointMother (su7ExteriorBasis degree i)=
      ((sourceJointExteriorWeight i:ℂ)*Complex.I) • su7ExteriorBasis degree i := by
  rw [mother_split,StageNineP286GaugeConnectionVariation.exteriorMotherLieAction_add,
    StageNineP286GaugeConnectionVariation.exteriorMotherLieAction_real_smul,
    StageNineP286GaugeConnectionVariation.exteriorMotherLieAction_real_smul]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,sourceExteriorWeight_action,
    Stage10.HyperchargeResponse.exterior_charge_basis,smul_smul,sourceJointExteriorWeight,
    Rat.cast_sub,Rat.cast_neg,Rat.cast_div,Rat.cast_intCast]
  norm_num
  module

def sourceJointInternalWeight : Quantum.InternalIndex→ℚ
  | .inl i=>sourceJointExteriorWeight i
  | .inr (.inl i)=>sourceJointExteriorWeight i
  | .inr (.inr i)=>sourceJointExteriorWeight i

def sourceJointWholeWeight (i : Quantum.Index) : ℚ:=sourceJointInternalWeight i.2

def sourceJointGenerator : YangMills.FullPairing.Mother:=diracExteriorMotherLieAction sourceJointMother

theorem sourceJoint_basis (i : Quantum.Index) :
    sourceJointGenerator (Quantum.wholeBasis i)=
      ((sourceJointWholeWeight i:ℂ)*Complex.I) • Quantum.wholeBasis i := by
  rcases i with ⟨spin,i|i|i⟩
  all_goals
    funext s
    simp only [sourceJointGenerator,diracExteriorMotherLieAction,internalMatterLinearAction,
      Quantum.wholeBasis,Pi.basis_apply,Pi.smul_apply]
    by_cases h:s=spin
    · subst s
      simp [Quantum.internalBasis,Module.Basis.prod_apply,exteriorSpinorMotherLieAction,
        sourceJoint_exterior,sourceJointWholeWeight,sourceJointInternalWeight]
    · simp [h,exteriorSpinorMotherLieAction]

theorem sourceJoint_matrix :
    Quantum.operatorMatrix sourceJointGenerator=Matrix.diagonal (fun i=>(sourceJointWholeWeight i:ℂ)*Complex.I) := by
  ext i j
  rw [Quantum.operatorMatrix,LinearMap.toMatrixAlgEquiv_apply,sourceJoint_basis,map_smul,Module.Basis.repr_self]
  simp [Matrix.diagonal_apply,Finsupp.single_apply]
  split_ifs <;> simp_all

theorem sourceJoint_native : nativePrimal sourcePhaseGaugeLie=Quantum.operatorMatrix sourceJointGenerator :=rfl

/-- The original exterior subsets calculate a common total weight, before either spin is selected. -/
theorem sourceJoint_weight (channel : Fin 2) (color : Fin 3) :
    sourceJointExteriorWeight (Composite.scalarBasis channel color)+
      sourceJointExteriorWeight (Composite.matterBasis color)=-1/2 := by
  exact (show ∀a : Fin 2,∀c : Fin 3,
    sourceJointExteriorWeight (Composite.scalarBasis a c)+
      sourceJointExteriorWeight (Composite.matterBasis c)=-1/2 from by decide +kernel) channel color

theorem sourceJoint_scalar (channel : Fin 2) (color : Fin 3) (phi : Scalar) :
    scalarCoefficient channel color (scalarMotherLieAction sourceJointMother phi)=
      ((sourceJointExteriorWeight (Composite.scalarBasis channel color):ℂ)*Complex.I)*
        scalarCoefficient channel color phi := by
  have diagonal : (su7ExteriorBasis 4).coord (Composite.scalarBasis channel color)
      (exteriorMotherLieAction 4 sourceJointMother (scalarCoordinateEquiv.symm phi))=
      ((sourceJointExteriorWeight (Composite.scalarBasis channel color):ℂ)*Complex.I)*
        (su7ExteriorBasis 4).coord (Composite.scalarBasis channel color) (scalarCoordinateEquiv.symm phi) := by
    rw [←(su7ExteriorBasis 4).sum_repr (scalarCoordinateEquiv.symm phi)]
    simp only [map_sum,map_smul,sourceJoint_exterior,Module.Basis.coord_apply,
      Module.Basis.repr_self,Finsupp.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,if_true]
    ring
  change (if color=1 then (-1:ℂ) else 1) •
    (su7ExteriorBasis 4).coord (Composite.scalarBasis channel color)
      (scalarCoordinateEquiv.symm (scalarMotherLieAction sourceJointMother phi))=_
  rw [scalarMotherLieAction,LinearEquiv.symm_apply_apply,diagonal]
  simp only [scalarCoefficient,LinearMap.smul_apply,LinearMap.comp_apply,smul_eq_mul]
  change (if color=1 then (-1:ℂ) else 1)*
      (((sourceJointExteriorWeight (Composite.scalarBasis channel color):ℂ)*Complex.I)*
        (su7ExteriorBasis 4).coord (Composite.scalarBasis channel color) (scalarCoordinateEquiv.symm phi))=
    ((sourceJointExteriorWeight (Composite.scalarBasis channel color):ℂ)*Complex.I)*
      ((if color=1 then (-1:ℂ) else 1)*
        (su7ExteriorBasis 4).coord (Composite.scalarBasis channel color) (scalarCoordinateEquiv.symm phi))
  ring

theorem sourceJoint_matter (spin : Fin 2) (color : Fin 3) (psi : DiracExteriorMatterCarrier) :
    Quantum.coordinates (sourceJointGenerator psi)
      ⟨spin.castLE (by decide),Sum.inr (Sum.inl (Composite.matterBasis color))⟩=
      ((sourceJointExteriorWeight (Composite.matterBasis color):ℂ)*Complex.I)*
        Quantum.coordinates psi ⟨spin.castLE (by decide),Sum.inr (Sum.inl (Composite.matterBasis color))⟩ := by
  rw [←Quantum.matrix_action,sourceJoint_matrix,Matrix.mulVec_diagonal]
  rfl

/-- Both elementary variations are present; the shared factor is generated from the full scalar and mother actions. -/
theorem sourceJoint_read (channel spin : Fin 2) (phi : Scalar) (psi : DiracExteriorMatterCarrier) :
    originalRead channel spin (scalarMotherLieAction sourceJointMother phi) psi+
      originalRead channel spin phi (sourceJointGenerator psi)=
      ((-1/2:ℂ)*Complex.I)*originalRead channel spin phi psi := by
  simp only [originalRead,←original_mode_read,sourceJoint_scalar,sourceJoint_matter,
    ←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  have weight : (sourceJointExteriorWeight (Composite.scalarBasis channel c):ℂ)+
      (sourceJointExteriorWeight (Composite.matterBasis c):ℂ)=(-1/2:ℂ) := by
    have cast:=congrArg (fun q : ℚ=>(q:ℂ)) (sourceJoint_weight channel c)
    norm_num only [Rat.cast_add,Rat.cast_div,Rat.cast_neg] at cast
    simpa only [neg_div] using cast
  linear_combination (Complex.I*scalarCoefficient channel c phi*
    Quantum.coordinates psi ⟨spin.castLE (by decide),Sum.inr (Sum.inl (Composite.matterBasis c))⟩)*weight

/-- The second endpoint remains an independent dual, with its original negative composition action. -/
def sourceJointDualRead (channel spin : Fin 2) (phi : Scalar)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) : ℂ :=
  ∑c : Fin 3,star (scalarCoefficient channel c phi)*
    dual (Quantum.wholeBasis ⟨spin.castLE (by decide),Sum.inr (Sum.inl (Composite.matterBasis c))⟩)

theorem sourceJoint_dual (channel spin : Fin 2) (phi : Scalar)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) :
    sourceJointDualRead channel spin (scalarMotherLieAction sourceJointMother phi) dual+
      sourceJointDualRead channel spin phi (-dual.comp sourceJointGenerator)=
      (-((-1/2:ℂ)*Complex.I))*sourceJointDualRead channel spin phi dual := by
  simp only [sourceJointDualRead,sourceJoint_scalar,LinearMap.neg_apply,LinearMap.comp_apply,
    sourceJoint_basis,sourceJointWholeWeight,sourceJointInternalWeight,map_smul,
    ←Finset.sum_add_distrib,Finset.mul_sum,map_mul,Complex.star_def,Complex.conj_I,
    map_ratCast,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro c _
  have weight : (sourceJointExteriorWeight (Composite.scalarBasis channel c):ℂ)+
      (sourceJointExteriorWeight (Composite.matterBasis c):ℂ)=(-1/2:ℂ) := by
    have cast:=congrArg (fun q : ℚ=>(q:ℂ)) (sourceJoint_weight channel c)
    norm_num only [Rat.cast_add,Rat.cast_div,Rat.cast_neg] at cast
    simpa only [neg_div] using cast
  simp only [starRingEnd_apply]
  linear_combination (-Complex.I*star (scalarCoefficient channel c phi)*
    dual (Quantum.wholeBasis ⟨spin.castLE (by decide),Sum.inr (Sum.inl (Composite.matterBasis c))⟩))*weight


theorem sourceJointScalar_original (phi : Scalar) :
    scalarMotherLieAction sourceJointMother phi=action phi sourcePhaseGaugeLie := by
  apply scalarCoordinateEquiv.symm.injective
  rw [scalarMotherLieAction,LinearEquiv.symm_apply_apply]
  exact (scalarAction_mother sourcePhaseGaugeLie phi).symm

private def jointWeight : Mode→ℂ
  | .inl i=>(sourceJointWholeWeight i:ℂ)*Complex.I
  | .inr i=> -(sourceJointWholeWeight i:ℂ)*Complex.I

theorem sourceJoint_full : nativeFull sourcePhaseGaugeLie=Matrix.diagonal jointWeight := by
  change Matrix.fromBlocks (nativePrimal sourcePhaseGaugeLie) 0 0
    ((nativePrimal sourcePhaseGaugeLie).map (starRingEnd ℂ))=Matrix.diagonal jointWeight
  rw [sourceJoint_native,sourceJoint_matrix]
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.diagonal_apply,jointWeight]

private theorem joint_create (spin : Fin 2) (c : Fin 3) :
    quantized (nativeFull sourcePhaseGaugeLie)*GaussCARHistory.createFiber (mode spin c)-
      GaussCARHistory.createFiber (mode spin c)*quantized (nativeFull sourcePhaseGaugeLie)=
    ((sourceJointExteriorWeight (Composite.matterBasis c):ℂ)*Complex.I) •
      GaussCARHistory.createFiber (mode spin c) := by
  rw [quantized_creation_column,sourceJoint_full]
  unfold creationColumn
  rw [Finset.sum_eq_single (mode spin c)]
  · rw [Matrix.diagonal_apply,if_pos rfl]
    rfl
  · intro j _ different
    rw [Matrix.diagonal_apply,if_neg different]
    exact _root_.zero_smul ℂ (GaussCARHistory.createFiber j)
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

private theorem joint_annihilate (spin : Fin 2) (c : Fin 3) :
    quantized (nativeFull sourcePhaseGaugeLie)*GaussCARHistory.annihilateFiber (mode spin c)-
      GaussCARHistory.annihilateFiber (mode spin c)*quantized (nativeFull sourcePhaseGaugeLie)=
    -(((sourceJointExteriorWeight (Composite.matterBasis c):ℂ)*Complex.I) •
      GaussCARHistory.annihilateFiber (mode spin c)) := by
  rw [quantized_annihilation_row,sourceJoint_full]
  unfold annihilationRow
  rw [Finset.sum_eq_single (mode spin c)]
  · rw [Matrix.diagonal_apply,if_pos rfl]
    rfl
  · intro j _ different
    rw [Matrix.diagonal_apply,if_neg (Ne.symm different)]
    exact _root_.zero_smul ℂ (GaussCARHistory.annihilateFiber j)
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

private theorem weight_complex (a : Fin 2) (c : Fin 3) :
    (sourceJointExteriorWeight (Composite.scalarBasis a c):ℂ)+
      (sourceJointExteriorWeight (Composite.matterBasis c):ℂ)=(-1/2:ℂ) := by
  have h:=congrArg (fun q : ℚ=>(q:ℂ)) (sourceJoint_weight a c)
  norm_num only [Rat.cast_add,Rat.cast_div,Rat.cast_neg] at h
  simpa only [neg_div] using h

/-- The material commutator is subtracted from the scalar variation, without changing the input state. -/
theorem sourceJoint_creation (a s : Fin 2) (phi : Scalar) :
    fiberCreation a s (scalarMotherLieAction sourceJointMother phi)-
      (quantized (nativeFull sourcePhaseGaugeLie)*fiberCreation a s phi-
        fiberCreation a s phi*quantized (nativeFull sourcePhaseGaugeLie))=
      (-((-1/2:ℂ)*Complex.I)) • fiberCreation a s phi := by
  simp only [fiberCreation,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    ←Finset.sum_sub_distrib,sourceJoint_scalar,map_mul,
    Complex.star_def,Complex.conj_I,map_ratCast,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro c _
  rw [←_root_.smul_sub ((starRingEnd ℂ) (scalarCoefficient a c phi))
    (quantized (nativeFull sourcePhaseGaugeLie)*GaussCARHistory.createFiber (mode s c))
    (GaussCARHistory.createFiber (mode s c)*quantized (nativeFull sourcePhaseGaugeLie)),joint_create,
    smul_smul]
  rw [←_root_.sub_smul _ _ (GaussCARHistory.createFiber (mode s c))]
  congr 1
  linear_combination (-Complex.I*(starRingEnd ℂ) (scalarCoefficient a c phi))*weight_complex a c

theorem sourceJoint_annihilation (a s : Fin 2) (phi : Scalar) :
    fiberAnnihilation a s (scalarMotherLieAction sourceJointMother phi)-
      (quantized (nativeFull sourcePhaseGaugeLie)*fiberAnnihilation a s phi-
        fiberAnnihilation a s phi*quantized (nativeFull sourcePhaseGaugeLie))=
      ((-1/2:ℂ)*Complex.I) • fiberAnnihilation a s phi := by
  simp only [fiberAnnihilation,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    ←Finset.sum_sub_distrib,sourceJoint_scalar,
    Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro c _
  rw [←_root_.smul_sub (scalarCoefficient a c phi)
    (quantized (nativeFull sourcePhaseGaugeLie)*GaussCARHistory.annihilateFiber (mode s c))
    (GaussCARHistory.annihilateFiber (mode s c)*quantized (nativeFull sourcePhaseGaugeLie)),joint_annihilate,
    smul_neg,smul_smul,sub_neg_eq_add]
  rw [←_root_.add_smul _ _ (GaussCARHistory.annihilateFiber (mode s c))]
  congr 1
  linear_combination (Complex.I*scalarCoefficient a c phi)*weight_complex a c


private theorem actual_charge_quantized : quantized (chargeMatrix sourcePhaseGaugeLie)=
    Complex.I • quantized (nativeFull sourcePhaseGaugeLie) :=
  quantizer.map_smul Complex.I (nativeFull sourcePhaseGaugeLie)

/-- The real charge correction includes the scalar orbit, with the original opposite CAR signs. -/
theorem sourceJoint_creation_charge (a s : Fin 2) (phi : Scalar) :
    quantized (chargeMatrix sourcePhaseGaugeLie)*fiberCreation a s phi-
      fiberCreation a s phi*quantized (chargeMatrix sourcePhaseGaugeLie)-
      Complex.I • fiberCreation a s (action phi sourcePhaseGaugeLie)=
      (1/2:ℂ) • fiberCreation a s phi := by
  calc
    _= -Complex.I • (fiberCreation a s (scalarMotherLieAction sourceJointMother phi)-
        (quantized (nativeFull sourcePhaseGaugeLie)*fiberCreation a s phi-
          fiberCreation a s phi*quantized (nativeFull sourcePhaseGaugeLie))) := by
      rw [sourceJointScalar_original]
      simp only [actual_charge_quantized,smul_mul_assoc,mul_smul_comm,smul_sub]
      module
    _= -Complex.I • ((-((-1/2:ℂ)*Complex.I)) • fiberCreation a s phi) :=
      congrArg (fun A : FiberOp=>-Complex.I • A) (sourceJoint_creation a s phi)
    _=_ := by
      rw [smul_smul]
      congr 1
      ring_nf
      norm_num [Complex.I_sq]

theorem sourceJoint_annihilation_charge (a s : Fin 2) (phi : Scalar) :
    quantized (chargeMatrix sourcePhaseGaugeLie)*fiberAnnihilation a s phi-
      fiberAnnihilation a s phi*quantized (chargeMatrix sourcePhaseGaugeLie)-
      Complex.I • fiberAnnihilation a s (action phi sourcePhaseGaugeLie)=
      (-1/2:ℂ) • fiberAnnihilation a s phi := by
  calc
    _= -Complex.I • (fiberAnnihilation a s (scalarMotherLieAction sourceJointMother phi)-
        (quantized (nativeFull sourcePhaseGaugeLie)*fiberAnnihilation a s phi-
          fiberAnnihilation a s phi*quantized (nativeFull sourcePhaseGaugeLie))) := by
      rw [sourceJointScalar_original]
      simp only [actual_charge_quantized,smul_mul_assoc,mul_smul_comm,smul_sub]
      module
    _= -Complex.I • (((-1/2:ℂ)*Complex.I) • fiberAnnihilation a s phi) :=
      congrArg (fun A : FiberOp=>-Complex.I • A) (sourceJoint_annihilation a s phi)
    _=_ := by
      rw [smul_smul]
      congr 1
      ring_nf
      norm_num [Complex.I_sq]

end LowEnergy.PreparationPhysicalJointEMCouplingUnitReturn
