import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceVoltageQuantumDensity
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.PreparedCharge

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalVoltageNoether
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField ProofFreeRicherAnholonomicSource Stage10 Stage10.TemporalGauge
open StageNineCurrentCoframeMatterTemporalPrincipal
open Stage9C.Material.SpinPair DiracExteriorMatterAction FullQuantum.StateGreen FullQuantum.CoframeResponse
open PreparationVacuumStaticVoltageSource PreparationVacuumPhysicalQuantumLockedCharge
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve
open PreparationVacuumActualFieldQuantization PreparationVacuumOriginalDensity
open PreparationVacuumPhysicalModeChargeRead PreparationVacuumNativeFieldInjection
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussQuantumMultiplier
open GaussCoreHilbert GaussFockLift CanonicalGradedSpatialSource CanonicalGradedCharge GaussComposite
open SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert
open Stage10.CanonicalMatter Stage9DEF Stage9DEF.Compatibility Electromagnetic.ExternalState
open PreparationVacuumElectromagneticIdentity PreparationVacuumMovingPoleGaussReturn
open scoped BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace Topology ContDiff
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
attribute [local irreducible] sourceSymbol sourceModeGaussReader

def sourceVoltageHamiltonianMatrix (value slope : ℝ) (s : ActionState) : SourceMatrix :=
  (-Complex.I) • (Ring.inverse (principalMatrix s.1)*sourceVoltageLowerInput value slope s)

def sourceVoltageScalarHamiltonian (s : ActionState) : SourceMatrix :=
  (-Complex.I) • (Ring.inverse (principalMatrix s.1)*sourceVoltageYukawaMatrix)

attribute [local irreducible] sourceVoltageHamiltonianMatrix sourceVoltageScalarHamiltonian
  sourceChargedCoordinates sourceChargedRestriction sourceChargedFiber sourceChargedGaussPrepared

theorem sourceVoltageHamiltonian_split (s : ActionState)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (value slope : ℝ) :
    sourceVoltageHamiltonianMatrix value slope s=
      value • ((-Complex.I) • GaussNativeMatter.nativePrimal nativeY)+
      slope • sourceVoltageScalarHamiltonian s := by
  unfold sourceVoltageHamiltonianMatrix sourceVoltageLowerInput sourceVoltageScalarHamiltonian
  rw [mul_add,mul_smul_comm,mul_smul_comm,←principalMatrix_coefficient,
    ←mul_assoc,Ring.inverse_mul_cancel _ (principalMatrix_regular s.1 regular),one_mul,
    smul_add,smul_comm (-Complex.I) value,smul_comm (-Complex.I) slope]

theorem sourceVoltageHamiltonian_affine (s : ActionState) (value slope a : ℝ) (k : Fin 4) :
    stateHamiltonian (s+a • sourceVoltageStateDirection value slope) k=
      stateHamiltonian s k+a • (if k=0 then sourceVoltageHamiltonianMatrix value slope s else 0) := by
  have coframe : (s+a • sourceVoltageStateDirection value slope).1=s.1 := by
    simp [sourceVoltageStateDirection]
  have lower : stateLower (s+a • sourceVoltageStateDirection value slope)=
      stateLower s+a • sourceVoltageLowerInput value slope s := by
    simp only [stateLower,sourceVoltageStateDirection,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_zero,add_zero,
      mul_add,mul_smul_comm,smul_ite,mul_ite,mul_zero,Finset.sum_add_distrib,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true,sourceVoltageLowerInput,smul_add,smul_smul]
    abel_nf
  unfold stateHamiltonian
  rw [coframe]
  cases k using Fin.cases with
  | zero=>
    simp only [Fin.cases_zero,ite_true,timeSymbol,lower,mul_add,mul_smul_comm,smul_add,
      sourceVoltageHamiltonianMatrix,smul_comm (-Complex.I) a]
  | succ j=>simp only [Fin.cases_succ,Fin.succ_ne_zero,ite_false,smul_zero,add_zero]

theorem sourceVoltageSymbol_affine (p : PhysicalMomentum) (s : ActionState) (value slope a : ℝ) :
    sourceSymbol p (s+a • sourceVoltageStateDirection value slope)=sourceSymbol p s+
      a • SourceRealScalarFock.branches (sourceVoltageHamiltonianMatrix value slope s) := by
  have h := funext (sourceVoltageHamiltonian_affine s value slope a)
  have temporal : fourierLinear p (fun k=>if k=0 then sourceVoltageHamiltonianMatrix value slope s else 0)=
      SourceRealScalarFock.branches (sourceVoltageHamiltonianMatrix value slope s) := by
    change realFourierMatrix (fun k=>if k=0 then sourceVoltageHamiltonianMatrix value slope s else 0) p=_
    simp [realFourierMatrix,affineMatrix,SourceRealScalarFock.branches]
  unfold sourceSymbol
  rw [h]
  change fourierLinear p (stateHamiltonian s+a •
    (fun k=>if k=0 then sourceVoltageHamiltonianMatrix value slope s else 0))=_
  rw [map_add,map_smul,temporal]

/-- The old Hamiltonian itself, including its spatial symbol, generates the voltage derivative. -/
theorem sourceVoltageSymbol_generated (p : PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) (value slope : ℝ) :
    HasDerivAt (fun a : ℝ=>sourceSymbol p (s+a • sourceVoltageStateDirection value slope))
      (SourceRealScalarFock.branches (sourceVoltageHamiltonianMatrix value slope s)) 0 := by
  have generated:=symbol_first_generated p s (sourceVoltageStateDirection value slope) valid
  have affine:=((hasDerivAt_id (0:ℝ)).smul_const
    (SourceRealScalarFock.branches (sourceVoltageHamiltonianMatrix value slope s))).const_add (sourceSymbol p s)
  have expected : HasDerivAt (fun a : ℝ=>sourceSymbol p (s+a • sourceVoltageStateDirection value slope))
      (SourceRealScalarFock.branches (sourceVoltageHamiltonianMatrix value slope s)) 0 := by
    simpa only [sourceVoltageSymbol_affine,one_smul,id_eq] using affine
  rw [generated.unique expected] at generated
  exact generated

theorem sourceVoltageSymbol_first (p : PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) (value slope : ℝ) :
    symbolFirst p s (sourceVoltageStateDirection value slope)=
      SourceRealScalarFock.branches (sourceVoltageHamiltonianMatrix value slope s) :=
  (symbol_first_generated p s _ valid).unique (sourceVoltageSymbol_generated p s valid value slope)

/-- The original source image fixes the full native-Y action, without assigning degenerate pole labels. -/
theorem sourceVoltage_charged_nativeY (side edge : Fin 2) :
    GaussNativeMatter.nativePrimal nativeY*ᵥQuantum.coordinates (sourceChargedRestriction side edge)=
      Complex.I • Quantum.coordinates (sourceChargedRestriction side edge) := by
  have eigen : diracExteriorMotherLieAction
      (SU7MotherLieAlgebra.p286LieBlockEmbed HyperchargeResponse.chargeDirection)
      (sourceChargedRestriction side edge)=Complex.I • sourceChargedRestriction side edge := by
    unfold sourceChargedRestriction
    rw [actualRestState_source,actualRestStateCoordinates]
    exact GaussComposite.source_embedding_charge _
  have h:=congrArg Quantum.coordinates eigen
  rw [←Quantum.matrix_action,map_smul] at h
  change Quantum.operatorMatrix (diracExteriorMotherLieAction
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm nativeY)))*ᵥ
    Quantum.coordinates (sourceChargedRestriction side edge)=_
  simpa only [nativeY,p286CoordinateEquiv.symm_apply_apply] using h

theorem sourceVoltage_charged_Hamiltonian (s : ActionState)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (value slope : ℝ) (side edge : Fin 2) :
    sourceVoltageHamiltonianMatrix value slope s*ᵥQuantum.coordinates (sourceChargedRestriction side edge)=
      value • Quantum.coordinates (sourceChargedRestriction side edge)+
      slope • (sourceVoltageScalarHamiltonian s*ᵥQuantum.coordinates (sourceChargedRestriction side edge)) := by
  rw [sourceVoltageHamiltonian_split s regular,Matrix.add_mulVec,Matrix.smul_mulVec,
    Matrix.smul_mulVec,sourceVoltage_charged_nativeY,smul_smul]
  simp only [neg_mul,Complex.I_mul_I,neg_neg,one_smul,Matrix.smul_mulVec]

/-- Full CAR precedes restriction to the same actual Gauss charged source. -/
theorem sourceVoltage_charged_fullCAR (s : ActionState)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (value slope : ℝ) (side edge : Fin 2) :
    quantized (SourceRealScalarFock.branches (sourceVoltageHamiltonianMatrix value slope s))
      (sourceChargedFiber side edge)=value • sourceChargedFiber side edge+
        slope • quantized (SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian s))
          (sourceChargedFiber side edge) := by
  unfold sourceChargedFiber
  rw [quantized_oneParticle,quantized_oneParticle]
  have matrix : SourceRealScalarFock.branches (sourceVoltageHamiltonianMatrix value slope s)*ᵥ
      sourceChargedCoordinates side edge=value • sourceChargedCoordinates side edge+
        slope • (SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian s)*ᵥsourceChargedCoordinates side edge) := by
    simp only [SourceRealScalarFock.branches,sourceChargedCoordinates,Matrix.fromBlocks_mulVec,
      Matrix.zero_mulVec,add_zero,zero_add]
    ext i
    cases i with
    | inl i=>exact congrFun (sourceVoltage_charged_Hamiltonian s regular value slope side edge) i
    | inr i=>
      simp only [Sum.elim_inr,Function.comp_def,Pi.add_apply,Pi.smul_apply,smul_zero,zero_add]
      change (_*ᵥ(0 : Quantum.Index→ℂ)) i=slope • (_*ᵥ(0 : Quantum.Index→ℂ)) i
      simp only [Matrix.mulVec_zero,Pi.zero_apply,smul_zero]
  rw [matrix]
  unfold oneParticleFiber
  change fiberCoordinates.symm (LowEnergy.Fermion.oneParticleLinear
    (value • sourceChargedCoordinates side edge+slope •
      (SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian s)*ᵥsourceChargedCoordinates side edge)))=
    value • fiberCoordinates.symm (LowEnergy.Fermion.oneParticleLinear (sourceChargedCoordinates side edge))+
      slope • fiberCoordinates.symm (LowEnergy.Fermion.oneParticleLinear
        (SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian s)*ᵥsourceChargedCoordinates side edge))
  simp only [map_add,LinearMap.map_smul_of_tower]
  have realMap (r : ℝ) (w : QuantizationCheck.Fermion.Fock Mode) :
      fiberCoordinates.symm (r • w)=r • fiberCoordinates.symm w :=
    (fiberCoordinates.symm.restrictScalars ℝ).map_smul r w
  rw [realMap,realMap]

theorem sourceVoltage_charged_Gauss (epsilon : ℝ) (precision : 0<epsilon)
    (s : ActionState) (regular : coframeTemporalPrincipalScalar s.1≠0)
    (value slope : ℝ) (side edge : Fin 2) :
    lift (quantized (SourceRealScalarFock.branches (sourceVoltageHamiltonianMatrix value slope s)))
      (sourceChargedGaussPrepared epsilon precision side edge)=
        value • sourceChargedGaussPrepared epsilon precision side edge+
        slope • lift (quantized (SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian s)))
          (sourceChargedGaussPrepared epsilon precision side edge) := by
  apply GaussHalfDensity.fockHalfDensityEquiv.injective
  rw [map_add,LinearMapClass.map_smul_of_tower,LinearMapClass.map_smul_of_tower]
  apply PiLp.ext
  intro word
  change GaussHalfDensity.fockHalfDensityEquiv
    (lift (quantized (SourceRealScalarFock.branches (sourceVoltageHamiltonianMatrix value slope s)))
      (sourceChargedGaussPrepared epsilon precision side edge)) word=
    value • GaussHalfDensity.fockHalfDensityEquiv (sourceChargedGaussPrepared epsilon precision side edge) word+
      slope • GaussHalfDensity.fockHalfDensityEquiv
        (lift (quantized (SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian s)))
          (sourceChargedGaussPrepared epsilon precision side edge)) word
  rw [sourceChargedGauss_action_coordinates,sourceChargedGaussPrepared_coordinates,
    sourceChargedGauss_action_coordinates,sourceVoltage_charged_fullCAR s regular]
  simp only [PiLp.add_apply,PiLp.smul_apply,add_smul,smul_assoc]

end LowEnergy.PreparationPhysicalVoltageNoether
