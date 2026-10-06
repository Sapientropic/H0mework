import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationCommonCarrier
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationPreparedTimeReturn

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationCommonMomentum
open GaussCoreHilbert GaussCoreDifferential GaussFockPair CanonicalGradedSpatialSource
open CanonicalPhysicalSpatial PreparationVacuumGradedTransport PreparationVacuumYukawaTransport
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse PreparationVacuumGradedTransport
open GaussQuantumMultiplier SourceQuantumFockGauge
open NativeHistoryGrade (Label projection)
open PreparationVacuumPhysicalHalfAxis
open Filter Set
open scoped Topology BigOperators InnerProductSpace
local instance : Fintype Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] GaussCoreHilbert.coreEquiv GaussDiagonalHistory.diagonalAction
  GaussCoreHilbert.embed physicalBasis physicalFrame bareTest gradedTest

theorem momentumAction_add (p k : PhysicalMomentum) :
    momentumAction (p+k)=momentumAction p+momentumAction k:=by
  apply LinearMap.ext
  intro a
  apply DFunLike.ext
  intro z
  change quantizer (momentumMatrix z (p+k)) (a z)=
    quantizer (momentumMatrix z p) (a z)+quantizer (momentumMatrix z k) (a z)
  rw [momentumMatrix_add,map_add,add_apply]

theorem momentumAction_smul (r : ℝ) (p : PhysicalMomentum) :
    momentumAction (r • p)=r • momentumAction p:=by
  apply LinearMap.ext
  intro a
  apply DFunLike.ext
  intro z
  change quantizer (momentumMatrix z (r • p)) (a z)=r • quantizer (momentumMatrix z p) (a z)
  rw [momentumMatrix_smul,map_smul,smul_apply]
  rfl

theorem physicalAction_affine (p k : PhysicalMomentum) :
    physicalAction (p+k)=physicalAction p+physicalAction k-physicalAction 0:=by
  rw [physicalAction_zero]
  simp only [physicalAction,momentumAction_add]
  abel

theorem compression_common_pair (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (compression p F y)=
      ∑g : Label,sourcePair (gradedTest 0 F g x) (physicalAction p (gradedTest 0 F g y)):=by
  rw [←gradedForm_zero (0:Field289) p F]
  have actual:=(gradedForm_pair (0:Field289) p F x y).self_of_nhds
  dsimp only at actual
  rw [actual]
  simp only [physicalForm_source,gradedTest_common]

theorem compression_affine (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    compression (p+k) F=compression p F+compression k F-compression 0 F:=by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  simp only [add_apply,sub_apply,inner_add_right,inner_sub_right,compression_common_pair,
    physicalAction_affine,LinearMap.add_apply,LinearMap.sub_apply,sourcePair,map_add,map_sub,
    inner_add_right,inner_sub_right,Finset.sum_add_distrib,Finset.sum_sub_distrib]

def momentumCompression (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ] H:=
  compression p F-compression 0 F

theorem momentumCompression_pair (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (momentumCompression p F y)=
      ∑g : Label,sourcePair (gradedTest 0 F g x) (momentumAction p (gradedTest 0 F g y)):=by
  simp only [momentumCompression,sub_apply,inner_sub_right,compression_common_pair,
    physicalAction_zero,physicalAction,LinearMap.add_apply,sourcePair,map_add,inner_add_right,
    Finset.sum_add_distrib,momentumAction_zero,LinearMap.zero_apply,map_zero,inner_zero_right,Finset.sum_const_zero]
  abel

theorem momentumCompression_add (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    momentumCompression (p+k) F=momentumCompression p F+momentumCompression k F:=by
  unfold momentumCompression
  rw [compression_affine]
  abel

theorem momentumCompression_smul (r : ℝ) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    momentumCompression (r • p) F=r • momentumCompression p F:=by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) r (momentumCompression p F)]
  simp only [smul_apply,inner_smul_right,momentumCompression_pair,momentumAction_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) r (momentumAction p),LinearMap.smul_apply]
  simp only [sourcePair,map_smul,inner_smul_right]

def momentumCompressionMap (F : GaussUnitaryHistory.Index) : PhysicalMomentum→L[ℝ] (H→L[ℂ] H):=
  (show PhysicalMomentum→ₗ[ℝ] (H→L[ℂ] H) from
    {toFun:=fun p=>momentumCompression p F
     map_add':=fun p k=>momentumCompression_add p k F
     map_smul':=fun r p=>momentumCompression_smul r p F}).toContinuousLinearMap

theorem compression_source_continuous (F : GaussUnitaryHistory.Index) :
    Continuous (fun p : PhysicalMomentum=>compression p F):=by
  have constant : Continuous (fun _ : PhysicalMomentum=>compression 0 F):=continuous_const
  have actual:=(momentumCompressionMap F).continuous.add constant
  convert! actual using 1
  funext p
  exact (sub_add_cancel (compression p F) (compression 0 F)).symm

/-- The original uncut term is the same occurrence at every momentum. -/
theorem jointY_common (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    jointY (finiteRetainer p F) h=jointY (finiteRetainer 0 F) h:=by
  rw [finiteRetainer_common]

theorem actualA_common (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    actualA p F=actualA 0 F:=by
  unfold actualA
  rw [finiteRetainer_common]

theorem jointGenerator_base (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointGenerator p F z 0=compression p F+actualA 0 F-z • 1:=by
  have shift : jointGenerator p F z 0=jointGenerator p F 0 0-z • 1:=by
    apply ContinuousLinearMap.ext
    intro x
    simp only [jointGenerator,sub_apply,smul_apply,one_apply_eq_self,zero_smul,sub_zero]
  have actual : jointGenerator p F 0 0=compression p F+actualA p F:=actualGenerator_source p F
  have common : actualA p F=actualA 0 F:=actualA_common p F
  exact shift.trans (congrArg (fun A : H→L[ℂ] H=>A-z • 1)
    (actual.trans (congrArg (fun A : H→L[ℂ] H=>compression p F+A) common)))

theorem jointGenerator_base_affine (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointGenerator (p+k) F z 0=
      jointGenerator p F z 0+jointGenerator k F z 0-jointGenerator 0 F z 0:=by
  simp only [jointGenerator_base,compression_affine]
  abel

theorem jointGenerator_base_continuous (F : GaussUnitaryHistory.Index) (z : ℂ) :
    Continuous (fun p : PhysicalMomentum=>jointGenerator p F z 0):=by
  have cA : Continuous (fun _ : PhysicalMomentum=>actualA 0 F):=continuous_const
  have cz : Continuous (fun _ : PhysicalMomentum=>z • (1:H→L[ℂ] H)):=continuous_const
  have actual:=((compression_source_continuous F).add cA).sub cz
  convert! actual using 1
  funext p
  exact jointGenerator_base p F z

theorem jointGenerator_momentum_difference (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointGenerator (p+k) F z 0-jointGenerator p F z 0=momentumCompressionMap F k:=by
  change _=momentumCompression k F
  simp only [jointGenerator_base,compression_affine,momentumCompression]
  abel

theorem jointGenerator_momentum_bound (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z : ℂ) :
    ‖jointGenerator (p+k) F z 0-jointGenerator p F z 0‖≤‖momentumCompressionMap F‖*‖k‖:=by
  rw [jointGenerator_momentum_difference]
  exact (momentumCompressionMap F).le_opNorm k

theorem jointGenerator_momentum_derivative (F : GaussUnitaryHistory.Index) (z : ℂ) (p : PhysicalMomentum) :
    HasFDerivAt (fun k : PhysicalMomentum=>jointGenerator k F z 0) (momentumCompressionMap F) p:=by
  have actual:=((momentumCompressionMap F).hasFDerivAt (x:=p)).const_add (jointGenerator 0 F z 0)
  refine actual.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun k=>?_))
  change jointGenerator k F z 0=jointGenerator 0 F z 0+momentumCompression k F
  simp only [jointGenerator_base,momentumCompression]
  abel


end LowEnergy.SourcePropagationCommonMomentum
