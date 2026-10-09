import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePinnedLeadingInverse

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumObservedPoleTensor
open GaussCoreHilbert GaussUnitaryHistory GaussDiagonalHistory
open SourceRetardedIncrement SourceJointResidualEnergy SourceFiniteResolventEnergy
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalSlowBlock
open PreparationVacuumPhysicalPinnedVelocity PreparationVacuumSharedPoleCarrier
open CanonicalGradedSpatialSource NativeHistoryGrade
open scoped BigOperators InnerProductSpace Topology
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : Fintype Label:=Fintype.ofFinite _
attribute [local irreducible] actualC sourceVelocityLinear sourcePinnedVelocity

set_option maxHeartbeats 10000 in
private theorem compression_mem_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E→ₗ.[ℂ] E) (F : Finset T.domain) (x : E) :
    FiniteCoreEvolution.compression T F x∈FiniteCoreEvolution.coreSpan T F :=
  (FiniteCoreEvolution.finiteAction T F ((FiniteCoreEvolution.coreSpan T F).orthogonalProjectionOnto x)).property

/-- All momentum compressions have the same source finite support. -/
theorem sourceMomentum_support (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (x : H) :
    actualC p F x∈supportSpan F := by
  rw [actualC,CanonicalPhysicalSpatial.compression_apply]
  apply Submodule.sum_mem
  intro g _
  apply projection_mem_support F g
  have same : FiniteCoreEvolution.coreSpan (CanonicalPhysicalSpatial.physical p) F=
      FiniteCoreEvolution.coreSpan diagonal F := by
    change Submodule.span ℂ ((fun y : diagonal.domain=>(y:H)) '' (F : Set diagonal.domain))=
      Submodule.span ℂ ((fun y : diagonal.domain=>(y:H)) '' (F : Set diagonal.domain))
    rfl
  rw [←same]
  exact compression_mem_span (CanonicalPhysicalSpatial.physical p) F (projection g x)

theorem sourceVelocity_support (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (x : H) :
    sourceVelocityLinear F n x∈supportSpan F := by
  have difference : sourceVelocityLinear F n=actualC n F-actualC 0 F := by
    rw [actualC_affine];abel
  rw [difference,sub_apply]
  exact (supportSpan F).sub_mem (sourceMomentum_support n F x) (sourceMomentum_support 0 F x)

private theorem escape_supported_zero (F : GaussUnitaryHistory.Index) (x : H) (inside : x∈supportSpan F) : escapeProjection F x=0 := by
  change x-(supportSpan F).starProjection x=0
  rw [Submodule.starProjection_eq_self_iff.mpr inside,sub_self]

theorem sourcePinnedVelocity_support (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (x : H) :
    sourcePinnedVelocity F n x∈supportSpan F := by
  rw [sourcePinnedVelocity_generated]
  simp only [sum_apply]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  by_cases same : channelValue F i=channelValue F j
  · rw [if_pos same]
    cases i with
    | none =>
      change escapeProjection F (sourceVelocityLinear F n (sourceChannelOp F j x))∈supportSpan F
      rw [escape_supported_zero F _ (sourceVelocity_support F n _)]
      exact (supportSpan F).zero_mem
    | some i =>
      change inner ℂ ((sourceBasis F) i : H) (sourceVelocityLinear F n (sourceChannelOp F j x)) •
        ((sourceBasis F) i : H)∈supportSpan F
      exact (supportSpan F).smul_mem _ ((sourceBasis F) i).property
  · rw [if_neg same,zero_apply]
    exact (supportSpan F).zero_mem

theorem sourcePinnedVelocity_escape (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (x : H) :
    sourcePinnedVelocity F n (escapeProjection F x)=0 := by
  apply ext_inner_right ℂ
  intro y
  rw [inner_zero_left]
  have symmetric:=(sourcePinnedVelocity_selfAdjoint F n).isSymmetric (escapeProjection F x) y
  exact symmetric.trans ((supportSpan F).starProjection_inner_eq_zero x _ (sourcePinnedVelocity_support F n y))

def sourcePinnedSupportAction (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) : supportSpan F→L[ℂ]supportSpan F :=
  ((sourcePinnedVelocity F n).codRestrict (supportSpan F) (sourcePinnedVelocity_support F n)).comp (supportSpan F).subtypeL

theorem sourcePinnedSupport_selfAdjoint (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    IsSelfAdjoint (sourcePinnedSupportAction F n) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro x y
  exact (sourcePinnedVelocity_selfAdjoint F n).isSymmetric (x:H) (y:H)

def sourcePinnedBasis (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) : OrthonormalBasis (SpectralIndex F) ℂ (supportSpan F) :=
  SourceFiniteResolventEnergy.basis (sourcePinnedSupportAction F n) (sourcePinnedSupport_selfAdjoint F n)

def sourcePinnedValue (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) : Channel F→ℝ
  | none=>0
  | some i=>SourceFiniteResolventEnergy.eigenvalue (sourcePinnedSupportAction F n) (sourcePinnedSupport_selfAdjoint F n) i

def sourcePinnedChannel (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) : Channel F→SourceOp
  | none=>escapeProjection F
  | some i=>InnerProductSpace.rankOne ℂ ((sourcePinnedBasis F n) i : H) ((sourcePinnedBasis F n) i : H)

theorem sourcePinnedChannel_resolution (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    ∑i : Channel F,sourcePinnedChannel F n i=1 := by
  classical
  rw [Fintype.sum_option]
  change escapeProjection F+(∑i : SpectralIndex F,InnerProductSpace.rankOne ℂ
    ((sourcePinnedBasis F n) i:H) ((sourcePinnedBasis F n) i:H))=1
  rw [←(sourcePinnedBasis F n).starProjection_eq_sum_rankOne]
  change (1-(supportSpan F).starProjection)+(supportSpan F).starProjection=1
  abel

theorem sourcePinnedChannel_eigen (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (i : Channel F) :
    sourcePinnedVelocity F n*sourcePinnedChannel F n i=(sourcePinnedValue F n i:ℂ) • sourcePinnedChannel F n i := by
  apply ContinuousLinearMap.ext
  intro x
  cases i with
  | none =>
    change sourcePinnedVelocity F n (escapeProjection F x)=(0:ℂ) • escapeProjection F x
    rw [sourcePinnedVelocity_escape,zero_smul]
  | some i =>
    have eigen:=(sourcePinnedSupport_selfAdjoint F n).isSymmetric.apply_eigenvectorBasis rfl i
    have actual:=congrArg (fun y : supportSpan F=>(y:H)) eigen
    change sourcePinnedVelocity F n ((sourcePinnedBasis F n) i:H)=
      (sourcePinnedValue F n (some i):ℂ) • ((sourcePinnedBasis F n) i:H) at actual
    change sourcePinnedVelocity F n (inner ℂ ((sourcePinnedBasis F n) i:H) x • ((sourcePinnedBasis F n) i:H))=_
    rw [map_smul,actual]
    change _=(sourcePinnedValue F n (some i):ℂ) • (inner ℂ ((sourcePinnedBasis F n) i:H) x • ((sourcePinnedBasis F n) i:H))
    exact smul_comm _ _ _

theorem sourcePinnedChannel_price (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (i : Channel F) :
    ‖sourcePinnedChannel F n i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  cases i with
  | none =>
    change ‖(1-(supportSpan F).starProjection) x‖ ≤ 1*‖x‖
    rw [←Submodule.starProjection_orthogonal',one_mul]
    exact (supportSpan F)ᗮ.norm_starProjection_apply_le x
  | some i =>
    have unit : ‖((sourcePinnedBasis F n) i:H)‖=1 := (sourcePinnedBasis F n).orthonormal.norm_eq_one i
    change ‖inner ℂ ((sourcePinnedBasis F n) i:H) x • ((sourcePinnedBasis F n) i:H)‖ ≤ 1*‖x‖
    rw [norm_smul,unit,mul_one]
    simpa only [unit] using norm_inner_le_norm ((sourcePinnedBasis F n) i:H) x

private theorem sourcePinned_denominator (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (i : Channel F) : zeta+Complex.I*(sourcePinnedValue F n i:ℂ)≠0 := by
  intro zero
  have h:=congrArg Complex.re zero
  simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero,Complex.zero_re] at h
  exact positive.ne' h

theorem sourcePinnedPencil_channel (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (i : Channel F) :
    sourcePinnedPencil F n zeta*sourcePinnedChannel F n i=
      (zeta+Complex.I*(sourcePinnedValue F n i:ℂ)) • sourcePinnedChannel F n i := by
  apply ContinuousLinearMap.ext
  intro x
  have eigen:=congrArg (fun A : SourceOp=>A x) (sourcePinnedChannel_eigen F n i)
  change sourcePinnedVelocity F n (sourcePinnedChannel F n i x)=
    (sourcePinnedValue F n i:ℂ) • sourcePinnedChannel F n i x at eigen
  change zeta • sourcePinnedChannel F n i x+Complex.I • sourcePinnedVelocity F n (sourcePinnedChannel F n i x)=_
  rw [eigen,smul_smul]
  exact (add_smul zeta (Complex.I*(sourcePinnedValue F n i:ℂ)) (sourcePinnedChannel F n i x)).symm

theorem sourcePinnedResolvent_channel (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (i : Channel F) :
    sourcePinnedResolvent F n zeta*sourcePinnedChannel F n i=
      (zeta+Complex.I*(sourcePinnedValue F n i:ℂ))⁻¹ • sourcePinnedChannel F n i := by
  apply ContinuousLinearMap.ext
  intro x
  have returned:=congrArg (fun A : SourceOp=>A (sourcePinnedChannel F n i x))
    (sourcePinnedResolvent_left F n zeta positive)
  have pencil:=congrArg (fun A : SourceOp=>A x) (sourcePinnedPencil_channel F n zeta i)
  change sourcePinnedPencil F n zeta (sourcePinnedChannel F n i x)=
    (zeta+Complex.I*(sourcePinnedValue F n i:ℂ)) • sourcePinnedChannel F n i x at pencil
  change sourcePinnedResolvent F n zeta (sourcePinnedPencil F n zeta (sourcePinnedChannel F n i x))=
    sourcePinnedChannel F n i x at returned
  rw [pencil,map_smul] at returned
  have normalized:=congrArg (fun y : H=>(zeta+Complex.I*(sourcePinnedValue F n i:ℂ))⁻¹ • y) returned
  simpa only [mul_apply_eq_comp,smul_apply,smul_smul,inv_mul_cancel₀ (sourcePinned_denominator F n zeta positive i),one_smul] using normalized

/-- The same pinned operator generates its entire source spectrum, including the escaped zero channel. -/
theorem sourcePinnedResolvent_channels (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) :
    sourcePinnedResolvent F n zeta=∑i : Channel F,
      (zeta+Complex.I*(sourcePinnedValue F n i:ℂ))⁻¹ • sourcePinnedChannel F n i := by
  calc
    _=sourcePinnedResolvent F n zeta*(∑i : Channel F,sourcePinnedChannel F n i) := by rw [sourcePinnedChannel_resolution,mul_one]
    _=∑i : Channel F,sourcePinnedResolvent F n zeta*sourcePinnedChannel F n i := Finset.mul_sum _ _ _
    _=_ := Finset.sum_congr rfl (fun i _=>sourcePinnedResolvent_channel F n zeta positive i)

end LowEnergy.PreparationVacuumObservedPoleTensor
