import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationPhysicalFullHalfAxis

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumOriginalDensity
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumActualFieldQuantization PreparationVacuumActionFieldLift
open PreparationVacuumGaugeSourceInjection PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse FullQuantum.StateGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open scoped Topology ContDiff BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
abbrev FockEnd:=Module.End ℂ (QuantizationCheck.Fermion.Fock Mode)

def plusDensity (W : SourceMatrix) : FockEnd:=
  ∑i : Quantum.Index,∑j : Quantum.Index,W i j •
    (SourceRealScalarFock.rawMomentumPlus i*SourceRealScalarFock.rawPrimalPlus j)

def oppositeDensity (W : SourceMatrix) : FockEnd:=
  ∑i : Quantum.Index,∑j : Quantum.Index,star (W i j) •
    (SourceRealScalarFock.rawMomentumConjugate i*SourceRealScalarFock.rawPrimalConjugate j)

/-- The original raw density has oppositeDual before quantization. -/
def rawPairDensity (positive negative : SourceMatrix) : FockEnd:=
  (1/2:ℂ) • (plusDensity positive-oppositeDensity negative)

private theorem sqrtTwo_square : (Real.sqrt 2:ℂ)*(Real.sqrt 2:ℂ)=2 :=by
  norm_cast
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

theorem rawPairDensity_quantize (positive negative : SourceMatrix) :
    rawPairDensity positive negative=
      Fermion.quantize (Matrix.fromBlocks positive 0 0 (negative.map star)) :=by
  simp only [rawPairDensity,plusDensity,oppositeDensity,SourceRealScalarFock.rawMomentumPlus,
    SourceRealScalarFock.rawPrimalPlus,SourceRealScalarFock.rawMomentumConjugate,
    SourceRealScalarFock.rawPrimalConjugate,smul_mul_smul,neg_mul,sqrtTwo_square,
    Finset.smul_sum,smul_sub,smul_smul]
  have positiveScale (a : ℂ) : (1/2:ℂ)*(a*2)=a:=by ring
  have negativeScale (a : ℂ) : (1/2:ℂ)*(a*(-2))= -a:=by ring
  simp only [positiveScale,negativeScale,neg_smul,Finset.sum_neg_distrib,sub_neg_eq_add]
  simp [Fermion.quantize,Fintype.sum_sum_type,Matrix.fromBlocks,Matrix.map_apply]

theorem rawFourier_blocks (A : Fin 4→SourceMatrix) (p : PhysicalMomentum) :
    rawFourier p A=Matrix.fromBlocks (affineMatrix A p) 0 0 ((affineMatrix A (-p)).map star) :=by
  change oppositeDual*realFourierMatrix A p=_
  rw [oppositeDual,realFourierMatrix,Matrix.fromBlocks_multiply]
  simp

def actualDensity (reader : Field289) (p : PhysicalMomentum) (s : ActionState) : FockEnd:=
  rawPairDensity (affineMatrix (fun i=>densityActionMatrix*densityVariation reader s i) p)
    (affineMatrix (fun i=>densityActionMatrix*densityVariation reader s i) (-p))

theorem actualDensity_source (reader : Field289) (p : PhysicalMomentum) (s : ActionState) :
    actualDensity reader p s=Fermion.quantize (rawActionSymbol reader p s) :=by
  rw [actualDensity,rawPairDensity_quantize,rawActionSymbol,rawFourier_blocks]

/-- This acts on the whole original Fock fibre, including every Number sector. -/
theorem rawFiber_actualDensity (reader : Field289) (p : PhysicalMomentum) (u : JointParameter)
    (v : FockFiber) :
    fiberCoordinates (rawFiber reader p u v)=actualDensity reader p (ambientState u) (fiberCoordinates v) :=by
  rw [actualDensity_source]
  change fiberCoordinates (fiberCoordinates.symm
    (Fermion.quantize (rawActionSymbol reader p (ambientState u)) (fiberCoordinates v)))=_
  exact LinearEquiv.apply_symm_apply _ _

theorem rawFiber_original_halves (reader : Field289) (p : PhysicalMomentum) (u : JointParameter)
    (v : FockFiber) :
    fiberCoordinates (rawFiber reader p u v)=
      (1/2:ℂ) •
        (plusDensity (affineMatrix (fun i=>densityActionMatrix*densityVariation reader (ambientState u) i) p)
          (fiberCoordinates v)-
        oppositeDensity (affineMatrix (fun i=>densityActionMatrix*densityVariation reader (ambientState u) i) (-p))
          (fiberCoordinates v)) :=by
  rw [rawFiber_actualDensity]
  simp only [actualDensity,rawPairDensity,LinearMap.smul_apply,LinearMap.sub_apply]

def contactDensity (reader force : Field289) (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FockEnd:=
  let A:=fun i=>densityActionMatrix*(densitySecond reader force (sourceState z) i+shellSecond reader force (sourceState z) i)
  rawPairDensity (affineMatrix A p) (affineMatrix A (-p))

theorem rawContact_actualDensity (reader force : Field289) (p : PhysicalMomentum) (z : physicalChart)
    (v : FockFiber) :
    fiberCoordinates (rawContact reader force p (0,z.val) v)=contactDensity reader force p z.val (fiberCoordinates v) :=by
  rw [rawContact_zero,raw_contact_source,contactDensity,rawPairDensity_quantize,←rawFourier_blocks]
  change fiberCoordinates (fiberCoordinates.symm (Fermion.quantize _ (fiberCoordinates v)))=_
  exact LinearEquiv.apply_symm_apply _ _

theorem fourier_independent_pair (A : Fin 4→SourceMatrix) (p : PhysicalMomentum)
    (pi psi : Quantum.Index→ℂ) :
    (∑i : Mode,∑j : Mode,SourceRealScalarFock.normalizedMomentum pi i*
      realFourierMatrix A p i j*SourceRealScalarFock.normalizedPrimal psi j)=
      (1/2:ℂ)*(SourceRealScalarFock.complexBilinear (affineMatrix A p) pi psi+
        SourceRealScalarFock.complexBilinear ((affineMatrix A (-p)).map star)
          (fun i=>star (pi i)) (fun i=>star (psi i))) :=by
  have scale : SourceRealScalarFock.branchScale*SourceRealScalarFock.branchScale=(1/2:ℂ):=by
    unfold SourceRealScalarFock.branchScale
    rw [←mul_inv_rev,sqrtTwo_square]
    norm_num
  simp only [Fintype.sum_sum_type,SourceRealScalarFock.normalizedMomentum,
    SourceRealScalarFock.normalizedPrimal,realFourierMatrix,Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
    Sum.elim_inl,Sum.elim_inr,Matrix.zero_apply,Matrix.neg_apply,Matrix.map_apply,
    mul_zero,zero_mul,Finset.sum_const_zero,add_zero,zero_add,neg_mul_neg]
  have scaled (a b c : ℂ) :
      (SourceRealScalarFock.branchScale*a)*b*(SourceRealScalarFock.branchScale*c)=(1/2:ℂ)*(a*b*c):=by
    calc
      _=(SourceRealScalarFock.branchScale*SourceRealScalarFock.branchScale)*(a*b*c):=by ring
      _=_:=by rw [scale]
  simp_rw [scaled]
  simp only [SourceRealScalarFock.complexBilinear,Matrix.map_apply,mul_add,Finset.mul_sum]

end LowEnergy.PreparationVacuumOriginalDensity
