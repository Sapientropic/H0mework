import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointPhaseAction

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalJointEMCouplingUnitReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalPhaseGaugeRealization PreparationPhysicalDressedPhotonCouplingReturn
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoreHilbert GaussCoreDifferential GaussFockLift GaussQuantumMultiplier GaussDensityCore
open CanonicalGradedCharge CanonicalGradedCurrent CanonicalGradedSpatialSource CanonicalPhysicalYResolvent
open GaussComposite GaussComposite.SourceGraph Electromagnetic.Identification
open PreparationVacuumFieldCovector PreparationVacuumFullFieldRiesz PreparationVacuumSourcePreparedResponse
open PreparationVacuumFieldConstraintResponse PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumSourceActionJets PreparationPhysicalNativePhotonFluxReturn
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationPhysicalNativePolarizationEmitter
open GaussHistoryHilbert (physicalChart)
open GaussUnitaryHistory (Index)
open Filter Set
open scoped BigOperators InnerProductSpace ContDiff Topology Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ FiberOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _

/-- This is the source-generated joint increment, not a charge assigned to the seed. -/
def sourceJointIncrement (addition : Bool) : ℂ:=if addition then 1/2 else -1/2

private theorem scalar_creation_smooth (a s : Fin 2) :
    ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>fiberCreation a s
      (action (GaussNativePotential.scalarField z) sourcePhaseGaugeLie)) := by
  simp only [←sourceJointScalar_original,fiberCreation,sourceJoint_scalar]
  apply ContDiff.sum
  intro c _
  have smooth : ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>
      star (((sourceJointExteriorWeight (Composite.scalarBasis a c):ℂ)*Complex.I)*
        scalarCoefficient a c (GaussNativePotential.scalarField z))) :=
    ((RCLike.conjCLE : ℂ≃L[ℝ]ℂ).toContinuousLinearMap.contDiff).comp
      (contDiff_const.mul (coefficient_smooth a c))
  exact smooth.smul (contDiff_const (c:=GaussCARHistory.createFiber (mode s c)))

private theorem scalar_annihilation_smooth (a s : Fin 2) :
    ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>fiberAnnihilation a s
      (action (GaussNativePotential.scalarField z) sourcePhaseGaugeLie)) := by
  simp only [←sourceJointScalar_original,fiberAnnihilation,sourceJoint_scalar]
  apply ContDiff.sum
  intro c _
  have smooth : ContDiff ℝ ∞ (fun z : SourceCoordinateSlice=>
      ((sourceJointExteriorWeight (Composite.scalarBasis a c):ℂ)*Complex.I)*
        scalarCoefficient a c (GaussNativePotential.scalarField z)) :=
    contDiff_const.mul (coefficient_smooth a c)
  exact smooth.smul (contDiff_const (c:=GaussCARHistory.annihilateFiber (mode s c)))

/-- The scalar correction carries the original number-dependent half-density factors. -/
def sourceJointScalarTest (addition : Bool) (a s : Fin 2) : QuantumTest→ₗ[ℂ]QuantumTest :=
  if addition then
    localMultiplier (fun z=>(rootVolume z:ℂ)⁻¹ • fiberCreation a s (action (GaussNativePotential.scalarField z) sourcePhaseGaugeLie))
      (fun z=>((root_volume_complex_smooth z).inv (Complex.ofReal_ne_zero.mpr (root_volume_pos z).ne')).smul
        (scalar_creation_smooth a s).contDiffAt)
  else
    localMultiplier (fun z=>(rootVolume z:ℂ) • fiberAnnihilation a s (action (GaussNativePotential.scalarField z) sourcePhaseGaugeLie))
      (fun z=>(root_volume_complex_smooth z).smul (scalar_annihilation_smooth a s).contDiffAt)

theorem sourceJointTest_charge (addition : Bool) (a s : Fin 2) (f : QuantumTest) :
    chargeAction sourcePhaseGaugeLie ((if addition then creationTest a s else annihilationTest a s) f)-
      (if addition then creationTest a s else annihilationTest a s) (chargeAction sourcePhaseGaugeLie f)-
      Complex.I • sourceJointScalarTest addition a s f=
      sourceJointIncrement addition • (if addition then creationTest a s else annihilationTest a s) f := by
  apply DFunLike.ext
  intro z
  cases addition
  · have paid:=congrArg (fun A : FiberOp=>(rootVolume z:ℂ) • (A (f z)))
      (sourceJoint_annihilation_charge a s (GaussNativePotential.scalarField z))
    change quantized (chargeMatrix sourcePhaseGaugeLie)
      ((rootVolume z:ℂ) • (fiberAnnihilation a s (GaussNativePotential.scalarField z) (f z)))-
      (rootVolume z:ℂ) • (fiberAnnihilation a s (GaussNativePotential.scalarField z)
        (quantized (chargeMatrix sourcePhaseGaugeLie) (f z)))-
      Complex.I • ((rootVolume z:ℂ) • (fiberAnnihilation a s
        (action (GaussNativePotential.scalarField z) sourcePhaseGaugeLie) (f z)))=
      (-1/2:ℂ) • ((rootVolume z:ℂ) • (fiberAnnihilation a s (GaussNativePotential.scalarField z) (f z)))
    simp only [sub_apply,mul_apply_eq_comp,smul_apply,map_smul,smul_sub,smul_smul] at paid ⊢
    convert paid using 1 <;> module
  · have paid:=congrArg (fun A : FiberOp=>(rootVolume z:ℂ)⁻¹ • (A (f z)))
      (sourceJoint_creation_charge a s (GaussNativePotential.scalarField z))
    change quantized (chargeMatrix sourcePhaseGaugeLie)
      ((rootVolume z:ℂ)⁻¹ • (fiberCreation a s (GaussNativePotential.scalarField z) (f z)))-
      (rootVolume z:ℂ)⁻¹ • (fiberCreation a s (GaussNativePotential.scalarField z)
        (quantized (chargeMatrix sourcePhaseGaugeLie) (f z)))-
      Complex.I • ((rootVolume z:ℂ)⁻¹ • (fiberCreation a s
        (action (GaussNativePotential.scalarField z) sourcePhaseGaugeLie) (f z)))=
      (1/2:ℂ) • ((rootVolume z:ℂ)⁻¹ • (fiberCreation a s (GaussNativePotential.scalarField z) (f z)))
    simp only [sub_apply,mul_apply_eq_comp,smul_apply,map_smul,smul_sub,smul_smul] at paid ⊢
    convert paid using 1 <;> module

/-- The literal input charge and scalar response are applied to the actual seed section. -/
def sourceJointInputCore (addition : Bool) (a s : Fin 2) : ScalarTest→ₗ[ℂ]H :=
  (leg addition a s).comp ((chargeAction sourcePhaseGaugeLie).comp seedSection)+
    Complex.I • embed.comp ((sourceJointScalarTest addition a s).comp seedSection)

theorem sourceJointInputCore_generated (addition : Bool) (a s : Fin 2) (f : ScalarTest) :
    chargeReader sourcePhaseGaugeLie (legCore addition a s f)=
      sourceJointIncrement addition • legCore addition a s f+sourceJointInputCore addition a s f := by
  have paid:=congrArg embed (sourceJointTest_charge addition a s (seedSection f))
  simp only [map_sub,map_smul] at paid
  cases addition
  · simp only [Bool.false_eq_true,if_false,embed_annihilation_test,←chargeReader_core] at paid
    change chargeReader sourcePhaseGaugeLie (annihilationSource a s (seedSection f))=
      sourceJointIncrement false • annihilationSource a s (seedSection f)+
        (annihilationSource a s (chargeAction sourcePhaseGaugeLie (seedSection f))+
          Complex.I • embed (sourceJointScalarTest false a s (seedSection f)))
    have returned:=sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp paid)
    exact returned.trans (by abel)
  · simp only [if_true,embed_creation_test,←chargeReader_core] at paid
    change chargeReader sourcePhaseGaugeLie (creationSource a s (seedSection f))=
      sourceJointIncrement true • creationSource a s (seedSection f)+
        (creationSource a s (chargeAction sourcePhaseGaugeLie (seedSection f))+
          Complex.I • embed (sourceJointScalarTest true a s (seedSection f)))
    have returned:=sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp paid)
    exact returned.trans (by abel)

private theorem input_bound (addition : Bool) (a s : Fin 2) (f : ScalarTest) :
    ‖sourceJointInputCore addition a s f‖≤
      ((‖chargeReader sourcePhaseGaugeLie‖+‖sourceJointIncrement addition‖)*legBound)*‖core f‖ := by
  have generated:=sourceJointInputCore_generated addition a s f
  have same : sourceJointInputCore addition a s f=chargeReader sourcePhaseGaugeLie (legCore addition a s f)-
      sourceJointIncrement addition • legCore addition a s f := by
    rw [generated]
    abel
  rw [same]
  calc
    _≤‖chargeReader sourcePhaseGaugeLie (legCore addition a s f)‖+
        ‖sourceJointIncrement addition • legCore addition a s f‖ := norm_sub_le _ _
    _≤‖chargeReader sourcePhaseGaugeLie‖*‖legCore addition a s f‖+
        ‖sourceJointIncrement addition‖*‖legCore addition a s f‖ :=
      add_le_add (ContinuousLinearMap.le_opNorm _ _) (le_of_eq (norm_smul _ _))
    _=(‖chargeReader sourcePhaseGaugeLie‖+‖sourceJointIncrement addition‖)*‖legCore addition a s f‖ := by ring
    _≤_ := by
      exact (mul_le_mul_of_nonneg_left (legCore_bound addition a s f) (by positivity)).trans_eq (mul_assoc _ _ _).symm

/-- Completion is generated from the original input-plus-scalar core, with its actual bound. -/
def sourceJointInputCompleted (addition : Bool) (a s : Fin 2) : Profile→L[ℂ]H :=
  (sourceJointInputCore addition a s).extendOfNorm core

theorem sourceJointInputCompleted_core (addition : Bool) (a s : Fin 2) (f : ScalarTest) :
    sourceJointInputCompleted addition a s (core f)=sourceJointInputCore addition a s f :=
  LinearMap.extendOfNorm_eq core_dense ⟨_,input_bound addition a s⟩ f

theorem sourceJointCompleted_charge (addition : Bool) (a s : Fin 2) (f : Profile) :
    chargeReader sourcePhaseGaugeLie (completedLeg addition a s f)=
      sourceJointIncrement addition • completedLeg addition a s f+sourceJointInputCompleted addition a s f := by
  have equality : sourceJointInputCompleted addition a s=
      (chargeReader sourcePhaseGaugeLie).comp (completedLeg addition a s)-
        sourceJointIncrement addition • completedLeg addition a s := by
    apply LinearMap.extendOfNorm_unique core_dense _ (input_bound addition a s)
    apply LinearMap.ext
    intro g
    simp only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,sub_apply,ContinuousLinearMap.comp_apply,
      smul_apply,completedLeg_core]
    change chargeReader sourcePhaseGaugeLie (legCore addition a s g)-
      sourceJointIncrement addition • legCore addition a s g=sourceJointInputCore addition a s g
    rw [sourceJointInputCore_generated]
    abel
  have value:=congrArg (fun T : Profile→L[ℂ]H=>T f) equality
  simp only [sub_apply,ContinuousLinearMap.comp_apply,smul_apply] at value
  calc
    _=sourceJointIncrement addition • completedLeg addition a s f+
        (chargeReader sourcePhaseGaugeLie (completedLeg addition a s f)-
          sourceJointIncrement addition • completedLeg addition a s f) := by abel
    _=_ := congrArg (fun v : H=>sourceJointIncrement addition • completedLeg addition a s f+v) value.symm

attribute [local irreducible] chargeReader completedLeg sourceProfile finiteFull currentVertex sourceJointInputCompleted

private theorem increment_real (addition : Bool) : star (sourceJointIncrement addition)=sourceJointIncrement addition := by
  cases addition <;> norm_num [sourceJointIncrement]

/-- Both detector endpoints keep their literal input/scalar remainders at the same original profile. -/
theorem sourceJointPrepared_charge (eps : ℝ) (prec : 0<eps) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) (i : Fin 289) :
    inner ℂ (chargeReader sourcePhaseGaugeLie (completedLeg left a s (sourceProfile eps prec)))
      (currentVertex (fieldBasis i) p k F cut z w (completedLeg right b t (sourceProfile eps prec)))+
    inner ℂ (completedLeg left a s (sourceProfile eps prec))
      (currentVertex (fieldBasis i) p k F cut z w
        (chargeReader sourcePhaseGaugeLie (completedLeg right b t (sourceProfile eps prec))))=
      (sourceJointIncrement left+sourceJointIncrement right)*preparedCovector eps prec p k F cut z w left right a s b t i+
      inner ℂ (sourceJointInputCompleted left a s (sourceProfile eps prec))
        (currentVertex (fieldBasis i) p k F cut z w (completedLeg right b t (sourceProfile eps prec)))+
      inner ℂ (completedLeg left a s (sourceProfile eps prec))
        (currentVertex (fieldBasis i) p k F cut z w (sourceJointInputCompleted right b t (sourceProfile eps prec))) := by
  rw [sourceJointCompleted_charge,sourceJointCompleted_charge]
  simp only [inner_add_left,inner_smul_left,map_add,map_smul,inner_add_right,inner_smul_right,
    starRingEnd_apply,increment_real,preparedCovector,preparedCurrent]
  ring

/-- The original source current with actual charge action at both composite endpoints. -/
def sourceJointChargedCurrent (eps : ℝ) (prec : 0<eps) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) : Fin 289→ℂ :=
  fun i=>inner ℂ (chargeReader sourcePhaseGaugeLie (completedLeg left a s (sourceProfile eps prec)))
    (currentVertex (fieldBasis i) p k F cut z w (completedLeg right b t (sourceProfile eps prec)))+
  inner ℂ (completedLeg left a s (sourceProfile eps prec))
    (currentVertex (fieldBasis i) p k F cut z w
      (chargeReader sourcePhaseGaugeLie (completedLeg right b t (sourceProfile eps prec))))

def sourceJointInputCurrent (eps : ℝ) (prec : 0<eps) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) : Fin 289→ℂ :=
  fun i=>inner ℂ (sourceJointInputCompleted left a s (sourceProfile eps prec))
    (currentVertex (fieldBasis i) p k F cut z w (completedLeg right b t (sourceProfile eps prec)))+
  inner ℂ (completedLeg left a s (sourceProfile eps prec))
    (currentVertex (fieldBasis i) p k F cut z w (sourceJointInputCompleted right b t (sourceProfile eps prec)))

theorem sourceJointChargedCurrent_generated (eps : ℝ) (prec : 0<eps) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    sourceJointChargedCurrent eps prec p k F cut z w left right a s b t=
      (sourceJointIncrement left+sourceJointIncrement right) • preparedCovector eps prec p k F cut z w left right a s b t+
      sourceJointInputCurrent eps prec p k F cut z w left right a s b t := by
  funext i
  exact (sourceJointPrepared_charge eps prec p k F cut z w left right a s b t i).trans (add_assoc _ _ _)

open PreparationVacuumNativePoleTensor in
private theorem emitter_linear (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (c : ℂ) (V W : Fin 289→ℂ) :
    sourcePhotonLeftReader branch epsilon s n (c • V+W)=
      c*sourcePhotonLeftReader branch epsilon s n V+sourcePhotonLeftReader branch epsilon s n W := by
  have forcing : nativeModeForcing epsilon s n (c • V+W)=
      c • nativeModeForcing epsilon s n V+nativeModeForcing epsilon s n W := by
    funext i
    simp only [nativeModeForcing,activeForcing,Matrix.mulVec_add,Matrix.mulVec_smul,Pi.add_apply,Pi.smul_apply]
  simp only [sourcePhotonLeftReader,forcing,sourceNativePoleCoefficient,Matrix.mulVec_add,Matrix.mulVec_smul,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_div,mul_div_assoc]

/-- The emitting pole retains its real input/scalar remainder; the relative charge is not substituted for beta. -/
theorem sourceJointPhotonEmitter_generated (eps : ℝ) (prec : 0<eps) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2)
    (branch : Fin 2) (epsilon sheet : ℝ) (n : PhysicalMomentum) :
    sourcePhotonLeftReader branch epsilon sheet n (sourceJointChargedCurrent eps prec p k F cut z w left right a s b t)=
      (sourceJointIncrement left+sourceJointIncrement right)*
        sourcePhotonLeftReader branch epsilon sheet n (preparedCovector eps prec p k F cut z w left right a s b t)+
      sourcePhotonLeftReader branch epsilon sheet n (sourceJointInputCurrent eps prec p k F cut z w left right a s b t) := by
  rw [sourceJointChargedCurrent_generated,emitter_linear]

theorem sourceJointPhotonField_generated (eps : ℝ) (prec : 0<eps) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
        sourceJointChargedCurrent eps prec p k F cut z w left right a s b t=
      ((sourceJointIncrement left+sourceJointIncrement right)*
        sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
          (preparedCovector eps prec p k F cut z w left right a s b t)+
        sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
          (sourceJointInputCurrent eps prec p k F cut z w left right a s b t)) •
      sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  rw [sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,factor,sourceJointPhotonEmitter_generated,
    sourceNativeFrequencyPolarization,smul_comm]

private theorem pair_factor (p k : PhysicalMomentum) (F : Index) (cut : ℕ) (z w : ℂ) (x y : H)
    (Js : Fin 289→ℂ) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      (∑i,inner ℂ x (currentVertex (fieldBasis i) p k F cut z w y)*
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥJs) i)/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)=
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n Js/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)*
      sourcePhotonWholePair branch e.val (sourceSheet branch n unit e.val) n p k F cut z w x y := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  have frequency : sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥJs=
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n Js •
        sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n := by
    rw [sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,factor,sourceNativeFrequencyPolarization,smul_comm]
  have whole:=sourcePhotonWholeConfiguration_generated branch e.val (sourceSheet branch n unit e.val) n p e.property.1.ne'
    (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint x)) (sourceTestApprox F (finiteFull p F cut w y))
  rw [frequency]
  simp only [Pi.smul_apply,smul_eq_mul]
  have read : (∑i,inner ℂ x (currentVertex (fieldBasis i) p k F cut z w y)*
      (sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n Js*
      sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n i))=
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n Js*
      sourcePhotonConfigurationRead p (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint x))
        (sourceTestApprox F (finiteFull p F cut w y))
        (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) := by
    change
      (∑i : Fin 289, inner ℂ x (currentVertex (fieldBasis i) p k F cut z w y) *
        (sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n Js *
          sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n i))=
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n Js *
        (∑i : Fin 289, sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n i *
          (fieldJets (fieldBasis i) p
            (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint x))
            (sourceTestApprox F (finiteFull p F cut w y))).first 0)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [currentVertex_original_pair]
    ring
  rw [read,whole]
  unfold sourcePhotonWholePair
  ring

/-- The right endpoint is an actual charge insertion, not the sum of two relative characters. -/
theorem sourceJointPhotonRightCoupling_generated
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
    (∑i,inner ℂ (completedLeg lD aD sD (sourceProfile epsD precD))
      (currentVertex (fieldBasis i) pD kD FD cutD zD wD
        (chargeReader sourcePhaseGaugeLie (completedLeg rD bD tD (sourceProfile epsD precD))))*
      (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
        preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i)/
      ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)=
    sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
      (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)/
      ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)*
    (sourceJointIncrement rD*
      sourcePhotonWholePair branch e.val (sourceSheet branch n unit e.val) n pD kD FD cutD zD wD
        (completedLeg lD aD sD (sourceProfile epsD precD)) (completedLeg rD bD tD (sourceProfile epsD precD))+
      sourcePhotonWholePair branch e.val (sourceSheet branch n unit e.val) n pD kD FD cutD zD wD
        (completedLeg lD aD sD (sourceProfile epsD precD)) (sourceJointInputCompleted rD bD tD (sourceProfile epsD precD))) := by
  filter_upwards [sourceDressedPhotonInteraction_generated epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
      epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS branch n unit,
    pair_factor pD kD FD cutD zD wD (completedLeg lD aD sD (sourceProfile epsD precD))
      (sourceJointInputCompleted rD bD tD (sourceProfile epsD precD))
      (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) branch n unit] with e ordinary right
  simp only [sourceJointCompleted_charge,map_add,map_smul,inner_add_right,inner_smul_right,
    add_mul,Finset.sum_add_distrib,add_div]
  have qfactor :
      (∑i : Fin 289, sourceJointIncrement rD *
        inner ℂ (completedLeg lD aD sD (sourceProfile epsD precD))
          (currentVertex (fieldBasis i) pD kD FD cutD zD wD
            (completedLeg rD bD tD (sourceProfile epsD precD))) *
          (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
            preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i) /
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) =
      sourceJointIncrement rD *
        ((∑i : Fin 289,
          inner ℂ (completedLeg lD aD sD (sourceProfile epsD precD))
            (currentVertex (fieldBasis i) pD kD FD cutD zD wD
              (completedLeg rD bD tD (sourceProfile epsD precD))) *
            (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
              preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i) /
          ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring
  rw [qfactor]
  have ordinary_inner :
      (∑i : Fin 289,
          inner ℂ (completedLeg lD aD sD (sourceProfile epsD precD))
            (currentVertex (fieldBasis i) pD kD FD cutD zD wD
              (completedLeg rD bD tD (sourceProfile epsD precD))) *
            (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
              preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i) /
          ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) =
      (∑i : Fin 289,
          preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i *
            (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
              preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i) /
          ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) := by
    rfl
  rw [ordinary_inner,ordinary,right]
  ring

/-- The actual source Noether charge resolves the ordinary full-photon coupling, preserving the non-eigen seed and scalar action. -/
theorem sourceJointPhotonCoupling_generated
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
    (∑i,(inner ℂ (chargeReader sourcePhaseGaugeLie (completedLeg lD aD sD (sourceProfile epsD precD)))
        (currentVertex (fieldBasis i) pD kD FD cutD zD wD (completedLeg rD bD tD (sourceProfile epsD precD)))+
      inner ℂ (completedLeg lD aD sD (sourceProfile epsD precD))
        (currentVertex (fieldBasis i) pD kD FD cutD zD wD
          (chargeReader sourcePhaseGaugeLie (completedLeg rD bD tD (sourceProfile epsD precD)))))*
      (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
        preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i)/
      ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)=
    sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
      (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)/
      ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)*
    ((sourceJointIncrement lD+sourceJointIncrement rD)*
      sourcePhotonWholePair branch e.val (sourceSheet branch n unit e.val) n pD kD FD cutD zD wD
        (completedLeg lD aD sD (sourceProfile epsD precD)) (completedLeg rD bD tD (sourceProfile epsD precD))+
      sourcePhotonWholePair branch e.val (sourceSheet branch n unit e.val) n pD kD FD cutD zD wD
        (sourceJointInputCompleted lD aD sD (sourceProfile epsD precD)) (completedLeg rD bD tD (sourceProfile epsD precD))+
      sourcePhotonWholePair branch e.val (sourceSheet branch n unit e.val) n pD kD FD cutD zD wD
        (completedLeg lD aD sD (sourceProfile epsD precD)) (sourceJointInputCompleted rD bD tD (sourceProfile epsD precD))) := by
  filter_upwards [sourceDressedPhotonInteraction_generated epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
      epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS branch n unit,
    pair_factor pD kD FD cutD zD wD (sourceJointInputCompleted lD aD sD (sourceProfile epsD precD))
      (completedLeg rD bD tD (sourceProfile epsD precD))
      (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) branch n unit,
    pair_factor pD kD FD cutD zD wD (completedLeg lD aD sD (sourceProfile epsD precD))
      (sourceJointInputCompleted rD bD tD (sourceProfile epsD precD))
      (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) branch n unit] with e ordinary left right
  simp only [sourceJointPrepared_charge,add_mul,Finset.sum_add_distrib,
    add_div]
  have qfactorL :
      (∑i : Fin 289, sourceJointIncrement lD *
        preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i *
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
          preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i) /
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) =
      sourceJointIncrement lD *
        ((∑i : Fin 289, preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i *
          (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
            preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i) /
          ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring
  have qfactorR :
      (∑i : Fin 289, sourceJointIncrement rD *
        preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i *
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
          preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i) /
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) =
      sourceJointIncrement rD *
        ((∑i : Fin 289, preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i *
          (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
            preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i) /
          ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring
  rw [qfactorL,qfactorR,ordinary,left,right]
  ring

end LowEnergy.PreparationPhysicalJointEMCouplingUnitReturn
