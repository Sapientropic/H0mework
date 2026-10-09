import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOrderedSpinDensity

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumCoframeQuantumCurrent
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumGravityLegendreSource PreparationVacuumCoframeLegendreSource
open PreparationVacuumJointFieldResponse PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussHistoryHilbert GaussQuantumMultiplier
open scoped Topology BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=Classical.decEq _

abbrev FiberEnd:=FockFiber→L[ℂ] FockFiber

def sourceSpinLoadRead (f : Field289) (z : SourceCoordinateSlice) (i : LorentzIndex) : ℂ:=
  ∑a : Mode,∑b : Mode,
    SourceRealScalarFock.normalizedMomentum (Quantum.dualCoordinates
      (sourceSpinMomentum (f,z) (sourceState z))) a*
    sourceSpinFullMatrix (f,z) (sourceState z) i a b*
    SourceRealScalarFock.normalizedPrimal (Quantum.coordinates
      (sourceSpinField (f,z) (sourceState z).1).matter) b

def sourceTotalLoadRead (f : Field289) (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) (i : LorentzIndex) : ℂ:=
  (sourceLorentzGeometryLoad (sourceGaussCoframe z) de i:ℂ)+sourceSpinLoadRead f z i

theorem sourceTotalLoadRead_original (f : Field289) (z : physicalChart)
    (de : Fin 4→LorentzianCoframe) (i : LorentzIndex) :
    sourceTotalLoadRead f z.val de i=(sourceLorentzOriginalLoad (f,z.val) (sourceGaussCoframe z.val) de i:ℂ):=by
  rw [sourceTotalLoadRead,sourceSpinLoadRead,sourceSpinFullMatrix_source]
  simp only [sourceLorentzOriginalLoad,Pi.add_apply,Complex.ofReal_add]
  rfl

def sourceOrderedLoadFiber (f : Field289) (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) (i : LorentzIndex) : FiberEnd:=
  (sourceLorentzGeometryLoad (sourceGaussCoframe z) de i:ℂ) • (1:FiberEnd)+
    sourceSpinFiber (f,z) (sourceState z) i

def sourceShiftWeight (z : SourceCoordinateSlice) : Matrix (Fin 6) LorentzIndex ℝ:=
  -(sourceGaussVelocityMatrix z).transpose*sourceLorentzInverse (sourceGaussCoframe z)

def sourceGaussShiftRead (f : Field289) (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) (j : Fin 6) : ℂ:=
  ∑i : LorentzIndex,(sourceShiftWeight z j i:ℂ)*sourceTotalLoadRead f z de i

theorem sourceGaussShiftRead_original (f : Field289) (z : physicalChart)
    (de : Fin 4→LorentzianCoframe) (j : Fin 6) :
    sourceGaussShiftRead f z.val de j=(sourceGaussMomentumShift (f,z.val) z.val de j:ℂ):=by
  simp only [sourceGaussShiftRead,sourceTotalLoadRead_original,sourceGaussMomentumShift,
    sourceShiftWeight,Matrix.mulVec,dotProduct,Complex.ofReal_sum,Complex.ofReal_mul]

def sourceGaussShiftFiber (f : Field289) (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) (j : Fin 6) : FiberEnd:=
  ∑i : LorentzIndex,(sourceShiftWeight z j i:ℂ) • sourceOrderedLoadFiber f z de i

def sourceGaussConstantRead (f : Field289) (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) : ℂ:=
  -(1/2:ℂ)*∑i : LorentzIndex,∑j : LorentzIndex,
    (sourceLorentzInverse (sourceGaussCoframe z) i j:ℂ)*
      sourceTotalLoadRead f z de i*sourceTotalLoadRead f z de j-
    3*(sourceGaussCoframe z).det

theorem sourceGaussConstantRead_original (f : Field289) (z : physicalChart)
    (de : Fin 4→LorentzianCoframe) :
    sourceGaussConstantRead f z.val de=(sourceGaussActionConstant (f,z.val) z.val de:ℂ):=by
  simp only [sourceGaussConstantRead,sourceTotalLoadRead_original,sourceGaussActionConstant,
    dotProduct,Matrix.mulVec,Finset.mul_sum,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_neg,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  congr 1
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  ring

def sourcePotentialWeight (z : SourceCoordinateSlice) (i j : LorentzIndex) : ℂ:=
  -(1/2:ℂ)*(sourceLorentzInverse (sourceGaussCoframe z) i j:ℂ)

def sourceGaussOrderedConstant (f : Field289) (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) : FiberEnd:=
  (∑i : LorentzIndex,∑j : LorentzIndex,sourcePotentialWeight z i j •
    (sourceOrderedLoadFiber f z de i*sourceOrderedLoadFiber f z de j))-
      (3*(sourceGaussCoframe z).det:ℂ) • (1:FiberEnd)

def sourceGaussGeometryConstant (z : SourceCoordinateSlice) (de : Fin 4→LorentzianCoframe) : ℂ:=
  (∑i : LorentzIndex,∑j : LorentzIndex,sourcePotentialWeight z i j*
    (sourceLorentzGeometryLoad (sourceGaussCoframe z) de i:ℂ)*
    (sourceLorentzGeometryLoad (sourceGaussCoframe z) de j:ℂ))-
      3*(sourceGaussCoframe z).det

def sourceGaussMixedSpin (f : Field289) (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) : FiberEnd:=
  ∑i : LorentzIndex,∑j : LorentzIndex,sourcePotentialWeight z i j •
    ((sourceLorentzGeometryLoad (sourceGaussCoframe z) de i:ℂ) • sourceSpinFiber (f,z) (sourceState z) j+
      (sourceLorentzGeometryLoad (sourceGaussCoframe z) de j:ℂ) • sourceSpinFiber (f,z) (sourceState z) i)

def sourceGaussOneBodyMatrix (f : Field289) (z : SourceCoordinateSlice) : Matrix Mode Mode ℂ:=
  ∑i : LorentzIndex,∑j : LorentzIndex,sourcePotentialWeight z i j •
    (sourceSpinFullMatrix (f,z) (sourceState z) i*sourceSpinFullMatrix (f,z) (sourceState z) j)

def sourceGaussFourBody (f : Field289) (z : SourceCoordinateSlice) : FiberEnd:=
  ∑i : LorentzIndex,∑j : LorentzIndex,sourcePotentialWeight z i j •
    sourceSpinNormalFiber (f,z) (sourceState z) i j

private theorem sourceLoadProduct (r s : ℂ) (A B : FiberEnd) :
    (r • (1:FiberEnd)+A)*(s • (1:FiberEnd)+B)=
      (r*s) • (1:FiberEnd)+(r • B+s • A)+A*B:=by
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,smul_add,smul_smul,mul_comm]
  abel

set_option backward.isDefEq.respectTransparency true in
theorem sourceGaussOrderedConstant_generated (f : Field289) (z : SourceCoordinateSlice)
    (de : Fin 4→LorentzianCoframe) :
    sourceGaussOrderedConstant f z de=
      sourceGaussGeometryConstant z de • (1:FiberEnd)+sourceGaussMixedSpin f z de+
        quantized (sourceGaussOneBodyMatrix f z)+sourceGaussFourBody f z:=by
  simp only [sourceGaussOrderedConstant,sourceOrderedLoadFiber,sourceLoadProduct,
    sourceSpinFiber_ordered,smul_add,Finset.sum_add_distrib]
  have oneBody : (∑i : LorentzIndex,∑j : LorentzIndex,sourcePotentialWeight z i j •
      quantized (sourceSpinFullMatrix (f,z) (sourceState z) i*sourceSpinFullMatrix (f,z) (sourceState z) j))=
      quantized (sourceGaussOneBodyMatrix f z):=by
    change (∑i : LorentzIndex,∑j : LorentzIndex,sourcePotentialWeight z i j •
      quantizer (sourceSpinFullMatrix (f,z) (sourceState z) i*sourceSpinFullMatrix (f,z) (sourceState z) j))=
      quantizer (sourceGaussOneBodyMatrix f z)
    simp only [sourceGaussOneBodyMatrix,map_sum,map_smul]
  rw [oneBody]
  simp only [sourceGaussGeometryConstant,sourceGaussMixedSpin,sourceGaussFourBody,
    sub_smul,Finset.sum_smul,smul_smul,smul_add,add_smul,Finset.sum_add_distrib,mul_assoc]
  have scalarSub (a b : ℂ) : (a-b) • (1:FiberEnd)=a • (1:FiberEnd)-b • (1:FiberEnd):=sub_smul a b (1:FiberEnd)
  have scalarAdd (a b : ℂ) : (a+b) • (1:FiberEnd)=a • (1:FiberEnd)+b • (1:FiberEnd):=add_smul a b (1:FiberEnd)
  have scalarSum (c : LorentzIndex→ℂ) : (∑i,c i) • (1:FiberEnd)=∑i,c i • (1:FiberEnd):=Finset.sum_smul (R:=ℂ) (M:=FiberEnd) (f:=c) (s:=Finset.univ) (x:=(1:FiberEnd))
  simp only [scalarSub,scalarAdd,scalarSum]
  abel

end LowEnergy.PreparationVacuumCoframeQuantumCurrent
