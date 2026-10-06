import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationMixedFieldReturn

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumActualFieldQuantization
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField DiracExteriorMatterAction
open SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open Electromagnetic.CanonicalCoframe
open PreparationVacuumMixedFieldReturn
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open CanonicalGradedSpatialSource
open scoped BigOperators Matrix
local instance : DecidableEq Quantum.Index := Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

-- The common carrier is the source affine operator-valued symbol.
def affineMatrix (A : Fin 4 → SourceMatrix) (p : PhysicalMomentum) : SourceMatrix :=
  A 0+∑ j : Fin 3,(p j:ℂ) • A j.succ

def realFourierMatrix (A : Fin 4 → SourceMatrix) (p : PhysicalMomentum) : Matrix Mode Mode ℂ :=
  Matrix.fromBlocks (affineMatrix A p) 0 0 (-(affineMatrix A (-p)).map star)

def realFourierCoefficient (A : Fin 4 → SourceMatrix) (i : Fin 4) : Matrix Mode Mode ℂ :=
  Matrix.fromBlocks (A i) 0 0 (if i=0 then -(A i).map star else (A i).map star)

theorem realFourier_affine (A : Fin 4 → SourceMatrix) (p : PhysicalMomentum) :
    realFourierMatrix A p=realFourierCoefficient A 0+
      ∑ j : Fin 3,(p j:ℂ) • realFourierCoefficient A j.succ := by
  ext u v
  cases u <;> cases v <;>
    simp [realFourierMatrix,realFourierCoefficient,affineMatrix,Matrix.map_apply,
      Matrix.smul_apply,Matrix.sum_apply,Pi.neg_apply,Matrix.fromBlocks]
  abel

theorem realFourier_zero (A : Fin 4 → SourceMatrix) :
    realFourierMatrix A 0=SourceRealScalarFock.branches (A 0) := by
  simp [realFourierMatrix,affineMatrix,SourceRealScalarFock.branches]

def readerCoefficient (f : Field289) (i : Fin 4) : SourceMatrix :=
  sourcePhaseMatrix*fieldDensityCoefficients (sourceField f) i

def readerSymbol (f : Field289) (p : PhysicalMomentum) : SourceMatrix := affineMatrix (readerCoefficient f) p

def readerMother (f : Field289) (p : PhysicalMomentum) : YangMills.FullPairing.Mother :=
  Quantum.operatorMatrix.toLinearEquiv.symm (readerSymbol f p)

def fullFieldSymbol (f : Field289) (p : PhysicalMomentum) : Matrix Mode Mode ℂ :=
  realFourierMatrix (readerCoefficient f) p

theorem reader_coefficient_forcing (f : Field289) (i : Fin 4) :
    readerCoefficient f i= -fieldHamiltonianCoefficients (sourceField f) i := by
  rw [actual_forcing_reader,neg_neg]
  rfl

theorem reader_symbol_forcing (f : Field289) (p : PhysicalMomentum) :
    readerSymbol f p= -affineMatrix (fieldHamiltonianCoefficients (sourceField f)) p := by
  simp only [readerSymbol,affineMatrix,reader_coefficient_forcing,smul_neg,Finset.sum_neg_distrib,neg_add]

theorem reader_coefficient_native (f : Field289) (i : Fin 4) :
    Quantum.operatorMatrix.toLinearEquiv.symm (readerCoefficient f i)=
      Stage10.CanonicalMatter.phaseInverse.comp (sourceDensityMother f i) := by
  apply Quantum.operatorMatrix.toLinearEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  change readerCoefficient f i=Quantum.operatorMatrix _
  rw [Quantum.matrix_composition]
  simp only [sourceDensityMother,readerCoefficient,sourcePhaseMatrix]
  congr 1
  exact (Quantum.operatorMatrix.toLinearEquiv.apply_symm_apply _).symm

theorem native_packet_reader (f : Field289) (p : PhysicalMomentum) :
    affine (fieldCoefficients (sourceField f)) p=YangMills.FullPairing.operator (readerMother f p) := by
  have same : readerSymbol f p=sourcePhaseMatrix*affineMatrix (fieldDensityCoefficients (sourceField f)) p := by
    simp only [readerSymbol,affineMatrix,readerCoefficient,mul_add,Finset.mul_sum,mul_smul_comm]
  simp only [affine,fieldCoefficients,←map_smul,←map_sum,←map_add]
  change canonicalMatrixRead (affineMatrix (fieldDensityCoefficients (sourceField f)) p)=_
  rw [readerMother,same]
  apply congrArg YangMills.FullPairing.operator
  apply Quantum.operatorMatrix.injective
  change Quantum.operatorMatrix (Stage10.CanonicalMatter.phaseInverse.comp
    (Quantum.operatorMatrix.toLinearEquiv.symm (affineMatrix (fieldDensityCoefficients (sourceField f)) p)))=_
  rw [Quantum.matrix_composition]
  have inverse (M : SourceMatrix) : Quantum.operatorMatrix (Quantum.operatorMatrix.toLinearEquiv.symm M)=M :=
    Quantum.operatorMatrix.toLinearEquiv.apply_symm_apply M
  rw [inverse,inverse]
  rfl

theorem fullField_plus_restriction (f : Field289) (p : PhysicalMomentum) :
    (fullFieldSymbol f p).submatrix Sum.inl Sum.inl=readerSymbol f p := rfl

theorem fullField_dual_restriction (f : Field289) (p : PhysicalMomentum) :
    (fullFieldSymbol f p).submatrix Sum.inr Sum.inr= -(readerSymbol f (-p)).map star := rfl

theorem fullField_plus_wave (f : Field289) (p : PhysicalMomentum) (u : DiracExteriorMatterCarrier) :
    fullFieldSymbol f p *ᵥ SourceRealScalarFock.plusWave (Quantum.coordinates u)=
      SourceRealScalarFock.plusWave (Quantum.coordinates (readerMother f p u)) := by
  rw [fullFieldSymbol,realFourierMatrix,Matrix.fromBlocks_mulVec]
  simp only [SourceRealScalarFock.plusWave,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    Matrix.zero_mulVec,Matrix.mulVec_zero,add_zero]
  have read := Quantum.matrix_action (readerMother f p) u
  have inverse : Quantum.operatorMatrix (readerMother f p)=readerSymbol f p :=
    Quantum.operatorMatrix.toLinearEquiv.apply_symm_apply _
  rw [inverse] at read
  exact congrArg (fun v : Quantum.Index → ℂ=>Sum.elim v (0:Quantum.Index→ℂ)) read

theorem fullField_original_real (f : Field289) (pi psi : Quantum.Index → ℂ) :
    (∑ i : Mode,∑ j : Mode,SourceRealScalarFock.normalizedMomentum pi i*
      fullFieldSymbol f 0 i j*SourceRealScalarFock.normalizedPrimal psi j)=
      ((SourceRealScalarFock.complexBilinear (readerCoefficient f 0) pi psi).re:ℂ) := by
  rw [fullFieldSymbol,realFourier_zero]
  exact SourceRealScalarFock.branches_original_real_bilinear _ _ _

end LowEnergy.PreparationVacuumActualFieldQuantization
