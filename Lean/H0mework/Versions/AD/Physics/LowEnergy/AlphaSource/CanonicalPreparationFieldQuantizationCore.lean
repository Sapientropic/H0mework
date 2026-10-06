import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldQuantizationSymbols
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalGradedCharge
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumActualFieldQuantization
open SaturationMonoid.PhysicsCore
open SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussQuantumMultiplier GaussCoreHilbert GaussCoreDifferential
open CanonicalGradedCurrent CanonicalGradedCharge
open scoped BigOperators Matrix ContDiff InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

abbrev FullMatrix := Matrix Mode Mode ℂ
local instance : FiniteDimensional ℂ FullMatrix := Matrix.finiteDimensional

def fieldFiber (f : Field289) (p : PhysicalMomentum) : FockFiber →L[ℂ] FockFiber :=
  quantized (fullFieldSymbol f p)

def fieldCore (f : Field289) (p : PhysicalMomentum) : QuantumTest →ₗ[ℂ] QuantumTest :=
  action (fun _=>fullFieldSymbol f p) (fun _=>contDiffAt_const)

def fieldGauss (f : Field289) (p : PhysicalMomentum) : H →L[ℂ] H := boundedMatrix (fullFieldSymbol f p)

theorem fieldGauss_core (f : Field289) (p : PhysicalMomentum) (test : QuantumTest) :
    fieldGauss f p (embed test)=embed (fieldCore f p test) := boundedMatrix_core _ _

theorem fieldCore_value (f : Field289) (p : PhysicalMomentum) (test : QuantumTest)
    (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) :
    fieldCore f p test z=fieldFiber f p (test z) := rfl

theorem fieldFiber_native_restriction (f : Field289) (p : PhysicalMomentum)
    (v : DiracExteriorMatterCarrier) :
    fieldFiber f p (oneParticleFiber (SourceRealScalarFock.plusWave (Quantum.coordinates v)))=
      oneParticleFiber (SourceRealScalarFock.plusWave (Quantum.coordinates (readerMother f p v))) := by
  rw [fieldFiber,quantized_oneParticle,fullField_plus_wave]

theorem fieldFiber_number (f : Field289) (p : PhysicalMomentum) :
    Commute SourceQuantumFockGauge.fiberNumber (fieldFiber f p) := number_commute _

theorem fieldFiber_halfDensity (f : Field289) (p : PhysicalMomentum)
    (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) :
    Commute (GaussBoundedMultiplier.halfWeight (fun N=>GaussDensityCore.density N z)) (fieldFiber f p) :=
  weight_commute _ _

-- The whole Fock action retains the normal-ordered four-leg term, including N2.
def fieldNormalProduct (f g : Field289) (p q : PhysicalMomentum) :=
  Fermion.normalProduct (fullFieldSymbol f p) (fullFieldSymbol g q)

theorem fieldFiber_normal_order (f g : Field289) (p q : PhysicalMomentum) (v : FockFiber) :
    fiberCoordinates (fieldFiber f p (fieldFiber g q v))=
      Fermion.quantize (fullFieldSymbol f p*fullFieldSymbol g q) (fiberCoordinates v)+
        fieldNormalProduct f g p q (fiberCoordinates v) := by
  have original:=LinearMap.congr_fun
    (Fermion.quantize_normal_order (fullFieldSymbol f p) (fullFieldSymbol g q)) (fiberCoordinates v)
  change fiberCoordinates (fiberCoordinates.symm (Fermion.quantize (fullFieldSymbol f p)
    (fiberCoordinates (fiberCoordinates.symm (Fermion.quantize (fullFieldSymbol g q) (fiberCoordinates v))))))=_
  simpa only [LinearEquiv.apply_symm_apply,Module.End.mul_apply,LinearMap.add_apply,fieldNormalProduct] using original

private theorem boundedMatrix_add (A B : FullMatrix) : boundedMatrix (A+B)=boundedMatrix A+boundedMatrix B := by
  apply GaussYukawaGrade.core_ext
  intro f
  rw [add_apply,boundedMatrix_core,boundedMatrix_core,boundedMatrix_core,←embed.map_add]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change quantizer (A+B) (f z)=quantizer A (f z)+quantizer B (f z)
  rw [map_add,add_apply]

private theorem boundedMatrix_smul (c : ℂ) (A : FullMatrix) : boundedMatrix (c • A)=c • boundedMatrix A := by
  apply GaussYukawaGrade.core_ext
  intro f
  rw [smul_apply,boundedMatrix_core,boundedMatrix_core,←embed.map_smul]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change quantizer (c • A) (f z)=c • quantizer A (f z)
  rw [map_smul,smul_apply]

def gaussQuantizer : FullMatrix →L[ℂ] H →L[ℂ] H :=
  ({toFun:=boundedMatrix,map_add':=boundedMatrix_add,map_smul':=boundedMatrix_smul} :
    FullMatrix →ₗ[ℂ] H →L[ℂ] H).toContinuousLinearMap

theorem fieldGauss_affine (f : Field289) (p : PhysicalMomentum) :
    fieldGauss f p=gaussQuantizer (realFourierCoefficient (readerCoefficient f) 0)+
      ∑ j : Fin 3,(p j:ℂ) • gaussQuantizer (realFourierCoefficient (readerCoefficient f) j.succ) := by
  change gaussQuantizer (realFourierMatrix (readerCoefficient f) p)=_
  rw [realFourier_affine,map_add,map_sum]
  simp only [map_smul]

def fieldGraphBound (f : Field289) (p : PhysicalMomentum) : ℝ :=
  ‖gaussQuantizer (realFourierCoefficient (readerCoefficient f) 0)‖+
    ∑ j : Fin 3,|p j| *‖gaussQuantizer (realFourierCoefficient (readerCoefficient f) j.succ)‖

theorem fieldGauss_graph_bound (f : Field289) (p : PhysicalMomentum) :
    ‖fieldGauss f p‖≤fieldGraphBound f p := by
  rw [fieldGauss_affine]
  apply (norm_add_le _ _).trans
  unfold fieldGraphBound
  apply add_le_add_right
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,le_refl]

end LowEnergy.PreparationVacuumActualFieldQuantization
