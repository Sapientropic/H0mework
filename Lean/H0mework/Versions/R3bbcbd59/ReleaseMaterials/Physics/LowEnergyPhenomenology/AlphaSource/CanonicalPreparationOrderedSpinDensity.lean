import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalSpinCurrent
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalRawActionDensity
import H0mework.Physics.LowEnergyFermion.NormalOrder

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumCoframeQuantumCurrent
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction StageNineGlobalIntegratedAction
open PreparationVacuumGravityLegendreSource PreparationVacuumCoframeLegendreSource
open PreparationVacuumJointFieldResponse PreparationVacuumSourceFieldFamily PreparationVacuumOriginalDensity
open SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert SourceQuantumFockGauge GaussQuantumMultiplier
open SourceQuantumConfigurationHilbert PreparationVacuumMixedFieldReturn
open scoped Topology BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _

-- The real source density fixes both branches before any operator product.
def sourceSpinMatrix (u : JointParameter) (s : ActionState) (i : LorentzIndex) :
    Matrix Quantum.Index Quantum.Index ℂ:=
  (generatedVolumeDensity (sourceSpinField u s.1):ℂ) • Quantum.operatorMatrix (sourceSpinMomentumMother s i)

theorem sourceSpinMatrix_independent (u : JointParameter) (s : ActionState) (i : LorentzIndex) :
    SourceRealScalarFock.complexBilinear (sourceSpinMatrix u s i)
      (Quantum.dualCoordinates (sourceSpinMomentum u s))
      (Quantum.coordinates (sourceSpinField u s.1).matter)=
      (generatedVolumeDensity (sourceSpinField u s.1):ℂ)*
        sourceSpinMomentum u s (sourceSpinMomentumMother s i (sourceSpinField u s.1).matter):=by
  rw [Quantum.full_response]
  simp only [sourceSpinMatrix,SourceRealScalarFock.complexBilinear,Matrix.smul_apply,
    Matrix.mulVec,dotProduct,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

def sourceSpinFullMatrix (u : JointParameter) (s : ActionState) (i : LorentzIndex) : Matrix Mode Mode ℂ:=
  SourceRealScalarFock.branches (sourceSpinMatrix u s i)

theorem sourceSpinFullMatrix_source (f : Field289) (z : physicalChart) (i : LorentzIndex) :
    (∑a : Mode,∑b : Mode,
      SourceRealScalarFock.normalizedMomentum (Quantum.dualCoordinates
        (sourceSpinMomentum (f,z.val) (sourceState z.val))) a*
      sourceSpinFullMatrix (f,z.val) (sourceState z.val) i a b*
      SourceRealScalarFock.normalizedPrimal (Quantum.coordinates
        (sourceSpinField (f,z.val) (sourceState z.val).1).matter) b)=
      (sourceLorentzSpinLoad (f,z.val) (sourceState z.val).1 i:ℂ):=by
  rw [sourceSpinFullMatrix,SourceRealScalarFock.branches_original_real_bilinear,
    sourceSpinMatrix_independent,sourceSpinLoad_sourceMomentum]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.ofReal_mul]

def sourceSpinRawDensity (u : JointParameter) (s : ActionState) (i : LorentzIndex) : FockEnd:=
  rawPairDensity (sourceSpinMatrix u s i) (-sourceSpinMatrix u s i)

set_option backward.isDefEq.respectTransparency true in
theorem sourceSpinRawDensity_half (u : JointParameter) (s : ActionState) (i : LorentzIndex) :
    sourceSpinRawDensity u s i=(1/2:ℂ) •
      (plusDensity (sourceSpinMatrix u s i)+oppositeDensity (sourceSpinMatrix u s i)):=by
  have negRead (W : Matrix Quantum.Index Quantum.Index ℂ) : oppositeDensity (-W)= -oppositeDensity W:=by
    simp only [oppositeDensity,Matrix.neg_apply,star_neg]
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _
    exact neg_smul (star (W a b))
      (SourceRealScalarFock.rawMomentumConjugate a*SourceRealScalarFock.rawPrimalConjugate b)
  simp only [sourceSpinRawDensity,rawPairDensity,negRead,sub_neg_eq_add]

theorem sourceSpinRawDensity_full (u : JointParameter) (s : ActionState) (i : LorentzIndex) :
    sourceSpinRawDensity u s i=Fermion.quantize (sourceSpinFullMatrix u s i):=by
  rw [sourceSpinRawDensity,rawPairDensity_quantize]
  congr 1


def sourceSpinFiber (u : JointParameter) (s : ActionState) (i : LorentzIndex) : FockFiber→L[ℂ] FockFiber:=
  quantized (sourceSpinFullMatrix u s i)

theorem sourceSpinFiber_raw (u : JointParameter) (s : ActionState) (i : LorentzIndex) (v : FockFiber) :
    fiberCoordinates (sourceSpinFiber u s i v)=sourceSpinRawDensity u s i (fiberCoordinates v):=by
  rw [sourceSpinRawDensity_full]
  change fiberCoordinates (fiberCoordinates.symm (Fermion.quantize _ (fiberCoordinates v)))=_
  exact LinearEquiv.apply_symm_apply _ _

def sourceSpinNormalFiber (u : JointParameter) (s : ActionState) (i j : LorentzIndex) : FockFiber→L[ℂ] FockFiber:=
  (fiberCoordinates.symm.toLinearMap.comp
    ((Fermion.normalProduct (sourceSpinFullMatrix u s i) (sourceSpinFullMatrix u s j)).comp
      fiberCoordinates.toLinearMap)).toContinuousLinearMap

theorem sourceSpinFiber_ordered (u : JointParameter) (s : ActionState) (i j : LorentzIndex) :
    sourceSpinFiber u s i*sourceSpinFiber u s j=
      quantized (sourceSpinFullMatrix u s i*sourceSpinFullMatrix u s j)+sourceSpinNormalFiber u s i j:=by
  apply ContinuousLinearMap.ext
  intro v
  apply fiberCoordinates.injective
  change Fermion.quantize (sourceSpinFullMatrix u s i)
      (Fermion.quantize (sourceSpinFullMatrix u s j) (fiberCoordinates v))=
    Fermion.quantize (sourceSpinFullMatrix u s i*sourceSpinFullMatrix u s j) (fiberCoordinates v)+
      Fermion.normalProduct (sourceSpinFullMatrix u s i) (sourceSpinFullMatrix u s j) (fiberCoordinates v)
  exact LinearMap.congr_fun (Fermion.quantize_normal_order _ _) (fiberCoordinates v)

end LowEnergy.PreparationVacuumCoframeQuantumCurrent
