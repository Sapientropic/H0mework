import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceIndependentPreparedReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFixedMomentumActionReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussQuantumMultiplier
open PreparationVacuumGradedTransport PreparationVacuumFieldConstraintResponse
open PreparationVacuumNoetherChart PreparationVacuumOriginalDensity
open PreparationVacuumSourceFieldFamily PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn
open PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActualFieldQuantization
open PreparationVacuumIndependentMomentumReturn CanonicalGradedSpatialSource
open FullQuantum.StateGreen StageNineHolonomicField
open DiracExteriorMatterAction
open Filter Set
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

private theorem source_map_star_product (A B : SourceMatrix) :
    (A*B).map star=A.map star*B.map star :=by
  ext i j
  simp only [Matrix.map_apply,Matrix.mul_apply,star_sum,star_mul]
  exact Finset.sum_congr rfl (fun _ _=>mul_comm _ _)

private theorem source_matrix_read (A : SourceMatrix) :
    Quantum.operatorMatrix (Quantum.operatorMatrix.toLinearEquiv.symm A)=A:=
  Quantum.operatorMatrix.toLinearEquiv.apply_symm_apply A

private theorem source_raw_fourier_product (G : SourceMatrix) (A : Fin 4→SourceMatrix)
    (p : PhysicalMomentum) :
    rawFourier p (fun i=>G*A i)=SourceRealScalarFock.branches G*fourierLinear p A :=by
  have affine (q : PhysicalMomentum) : affineMatrix (fun i=>G*A i) q=G*affineMatrix A q:=by
    simp only [affineMatrix,mul_add,Finset.mul_sum,mul_smul_comm]
  rw [rawFourier_blocks]
  change Matrix.fromBlocks _ 0 0 _=
    SourceRealScalarFock.branches G*realFourierMatrix A p
  rw [SourceRealScalarFock.branches,realFourierMatrix,Matrix.fromBlocks_multiply,affine,affine]
  simp only [mul_zero,zero_mul,add_zero,zero_add,neg_mul_neg,source_map_star_product]

private theorem source_transported_density (reader : Field289) (base candidate : ActionState) (i : Fin 4) :
    transportedDensity reader base candidate i=rawMomentumMatrix base*(statePhase candidate*densityVariation reader candidate i) :=by
  unfold transportedDensity rawMomentumInverse
  simp only [mul_assoc]
  rw [←mul_assoc densityActionInverse densityActionMatrix,densityAction_two_sided.2,one_mul]

def sourceFixedMomentumAction (p : PhysicalMomentum) (base candidate : ActionState) : FullMatrix:=
  -(4:ℂ) • (sourceActionWeight base*sourceSymbol p candidate)

def sourceFixedMomentumGradient (reader : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) : FullMatrix:=
  -(4:ℂ) • (sourceActionWeight base*symbolFirst p candidate (fieldDirection reader))

def sourceFixedMomentumContact (reader force : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) : FullMatrix:=
  -(4:ℂ) • (sourceActionWeight base*symbolSecond p candidate (fieldDirection reader) (fieldDirection force))

def sourceHamiltonianMother (p : PhysicalMomentum) (candidate : ActionState) : Mother:=
  Quantum.operatorMatrix.toLinearEquiv.symm (affineMatrix (stateHamiltonian candidate) p)

theorem sourceFixedMomentumAction_originalMomentum (p : PhysicalMomentum) (base candidate : ActionState)
    (chi : IndependentDual) (psi : DiracExteriorMatterCarrier) :
    sourceCanonicalMomentum base chi (sourceHamiltonianMother p candidate psi)=
      SourceRealScalarFock.complexBilinear (rawMomentumMatrix base*affineMatrix (stateHamiltonian candidate) p)
        (Quantum.dualCoordinates chi) (Quantum.coordinates psi) :=by
  let original : Mother:=sourceDensityMother.comp ((momentumMother base).comp (sourceHamiltonianMother p candidate))
  change chi (original psi)=_
  have matrix : Quantum.operatorMatrix original=rawMomentumMatrix base*affineMatrix (stateHamiltonian candidate) p:=by
    rw [Quantum.matrix_composition,Quantum.matrix_composition]
    simp only [PreparationVacuumIndependentMomentumReturn.sourceDensityMother,momentumMother,sourceHamiltonianMother,
      source_matrix_read,rawMomentumMatrix,mul_assoc]
  rw [Quantum.full_response,matrix]
  simp only [SourceRealScalarFock.complexBilinear,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]

theorem sourceFixedMomentumAction_original (p : PhysicalMomentum) (base candidate : ActionState) :
    sourceFixedMomentumAction p base candidate=
      -rawFourier p (fun i=>rawMomentumMatrix base*stateHamiltonian candidate i) :=by
  rw [sourceFixedMomentumAction,source_raw_fourier_product,rawMomentum_source_weight,smul_mul_assoc]
  simp only [sourceSymbol,neg_smul]

theorem sourceFixedMomentumAction_originalHalves (p : PhysicalMomentum) (base candidate : ActionState) :
    Fermion.quantize (sourceFixedMomentumAction p base candidate)=
      rawPairDensity
        (affineMatrix (fun i=> -(rawMomentumMatrix base*stateHamiltonian candidate i)) p)
        (affineMatrix (fun i=> -(rawMomentumMatrix base*stateHamiltonian candidate i)) (-p)) :=by
  have negative : (fun i=> -(rawMomentumMatrix base*stateHamiltonian candidate i))=
      -(fun i=>rawMomentumMatrix base*stateHamiltonian candidate i):=rfl
  rw [rawPairDensity_quantize,sourceFixedMomentumAction_original,negative,←rawFourier_blocks,map_neg]

theorem sourceFixedMomentumGradient_raw (reader : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) (valid : candidate∈validStates) :
    sourceFixedMomentumGradient reader p base candidate=transportedRawSymbol reader base candidate p :=by
  have density : transportedDensity reader base candidate=
      fun i=>rawMomentumMatrix base*(statePhase candidate*densityVariation reader candidate i):=
    funext (source_transported_density reader base candidate)
  rw [transportedRawSymbol,density,source_raw_fourier_product,rawMomentum_source_weight]
  rw [sourceFixedMomentumGradient,symbolFirst_field reader p candidate valid,smul_mul_assoc,mul_neg]
  simp only [neg_smul,smul_neg,neg_neg]

theorem sourceFixedMomentumAction_generated (reader : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) (valid : candidate∈validStates) :
    HasDerivAt (fun r : ℝ=>sourceFixedMomentumAction p base (candidate+r • fieldDirection reader))
      (transportedRawSymbol reader base candidate p) 0 :=by
  have actual:=((symbol_first_generated p candidate (fieldDirection reader) valid).const_mul
    (sourceActionWeight base)).const_smul (-(4:ℂ))
  rw [←sourceFixedMomentumGradient_raw reader p base candidate valid]
  exact actual

theorem sourceFixedMomentumGradient_generated (reader force : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) (valid : candidate∈validStates) :
    HasDerivAt (fun r : ℝ=>sourceFixedMomentumGradient reader p base (candidate+r • fieldDirection force))
      (sourceFixedMomentumContact reader force p base candidate) 0 :=
  ((symbol_second_generated p candidate (fieldDirection reader) (fieldDirection force) valid).const_mul
    (sourceActionWeight base)).const_smul (-(4:ℂ))

theorem sourceFixedMomentumContact_noether (reader force : Field289) (p : PhysicalMomentum)
    (z : physicalChart) :
    sourceFixedMomentumContact reader force p (sourceState z.val) (sourceState z.val)=
      noetherContactSymbol reader force (sourceState z.val) p :=by
  let s:=sourceState z.val
  have valid : s∈validStates:=sourceState_valid z.val z.property
  have nearby : ∀ᶠr : ℝ in 𝓝 0,s+r • fieldDirection force∈validStates:=
    (state_line s (fieldDirection force)).continuousAt.preimage_mem_nhds
      (by simpa only [zero_smul,add_zero] using validStates_open.mem_nhds valid)
  have same : (fun r : ℝ=>sourceFixedMomentumGradient reader p s (s+r • fieldDirection force))=ᶠ[𝓝 0]
      (fun r : ℝ=>transportedRawSymbol reader s (s+r • fieldDirection force) p):=
    nearby.mono (fun r hr=>sourceFixedMomentumGradient_raw reader p s _ hr)
  exact ((sourceFixedMomentumGradient_generated reader force p s s valid).congr_of_eventuallyEq same.symm).unique
    (noetherContactSymbol_generated reader force z p)

theorem sourceFixedMomentumGradient_independentDual (reader : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) (valid : candidate∈validStates) :
    Fermion.quantize (sourceFixedMomentumGradient reader p base candidate)=
      rawPairDensity
        (Quantum.operatorMatrix (sourceMovingDensityMother reader p base candidate))
        (Quantum.operatorMatrix (sourceMovingDensityMother reader (-p) base candidate)) :=by
  rw [sourceFixedMomentumGradient_raw reader p base candidate valid,sourceIndependentDensity_fullCAR]

theorem sourceFixedMomentumContact_fullCAR (reader force : Field289) (p : PhysicalMomentum)
    (z : physicalChart) (v : FockFiber) :
    fiberCoordinates (quantizer (sourceFixedMomentumContact reader force p (sourceState z.val) (sourceState z.val)) v)=
      fiberCoordinates (rawContactFiber reader force p z.val v)-
        Fermion.quantize (fullMomentumConnection force (sourceState z.val))
          (Fermion.quantize (rawActionSymbol reader p (sourceState z.val)) (fiberCoordinates v))+
        Fermion.normalProduct (fullMomentumConnection force (sourceState z.val))
          (rawActionSymbol reader p (sourceState z.val)) (fiberCoordinates v) :=by
  rw [sourceFixedMomentumContact_noether]
  exact noetherContact_fullCAR reader force z p v

end LowEnergy.PreparationVacuumFixedMomentumActionReturn
