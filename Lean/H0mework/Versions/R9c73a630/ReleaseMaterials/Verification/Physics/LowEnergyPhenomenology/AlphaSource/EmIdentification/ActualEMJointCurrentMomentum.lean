import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedGaugePole

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMJointCurrentMomentum
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussQuantumMultiplier
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumHalfDensityFiber
open PreparationVacuumActualFieldQuantization PreparationVacuumActionFieldLift PreparationVacuumSourceActionJets
open PreparationVacuumActionDecomposition PreparationVacuumGradedTransport PreparationVacuumYukawaTransport
open PreparationVacuumUncutYukawa PreparationVacuumJointFieldResponse PreparationVacuumFullPoleContinuation
open PreparationVacuumSpatialDensityTransport PreparationVacuumFieldConstraintResponse
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open PreparationVacuumFullFieldRiesz
open FullQuantum.StateGreen Filter Set MeasureTheory
open scoped BigOperators Topology ContDiff Matrix
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup (Field289→L[ℝ](H→L[ℂ]H)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Field289→L[ℝ](H→L[ℂ]H)) := ContinuousLinearMap.toNormedSpace
attribute [local irreducible] jointCurrent jointGenerator actualFiber diagonalFiber

private theorem fourier_add (A : Fin 4→SourceMatrix) (p k : PhysicalMomentum) :
    realFourierMatrix A (p+k)=realFourierMatrix A p+realFourierMatrix A k-realFourierMatrix A 0 := by
  simp only [realFourier_affine,Pi.add_apply,Complex.ofReal_add,add_smul,Finset.sum_add_distrib,
    Pi.zero_apply,Complex.ofReal_zero,zero_smul,Finset.sum_const_zero,add_zero]
  abel

private theorem fourier_smul (A : Fin 4→SourceMatrix) (p : PhysicalMomentum) (r : ℝ) :
    realFourierMatrix A (r • p)=(r:ℂ) • realFourierMatrix A p+(1-r:ℂ) • realFourierMatrix A 0 := by
  simp only [realFourier_affine,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,mul_smul,
    Finset.smul_sum,smul_add,Pi.zero_apply,Complex.ofReal_zero,zero_smul,Finset.sum_const_zero,add_zero]
  simp only [sub_smul,one_smul]
  abel

private theorem diagonal_add (p k : PhysicalMomentum) (z : SourceCoordinateSlice) :
    diagonalFiber (p+k) z=diagonalFiber p z+diagonalFiber k z-diagonalFiber 0 z := by
  have h : actualFiber (p+k) z=actualFiber p z+actualFiber k z-actualFiber 0 z := by
    simp only [actualFiber,fourierLinear,LinearMap.coe_mk,AddHom.coe_mk,
      fourier_add,map_sub,map_add]
  simp only [diagonalFiber,h]
  abel

private theorem diagonal_smul (p : PhysicalMomentum) (r : ℝ) (z : SourceCoordinateSlice) :
    diagonalFiber (r • p) z=(r:ℂ) • diagonalFiber p z+(1-r:ℂ) • diagonalFiber 0 z := by
  have h : actualFiber (r • p) z=(r:ℂ) • actualFiber p z+(1-r:ℂ) • actualFiber 0 z := by
    simp only [actualFiber,fourierLinear,LinearMap.coe_mk,AddHom.coe_mk,
      fourier_smul,map_add,map_smul]
  simp only [diagonalFiber,h,smul_sub,sub_smul,one_smul]
  module

private theorem sample_add (f : Field289) (p k : PhysicalMomentum) (a b : QuantumTest) (r : ℝ)
    (z : SourceCoordinateSlice) :
    fixedSample (diagonalFiber (p+k)) f a b (r,z)=fixedSample (diagonalFiber p) f a b (r,z)+
      fixedSample (diagonalFiber k) f a b (r,z)-fixedSample (diagonalFiber 0) f a b (r,z) := by
  simp only [fixedSample,diagonal_add,add_apply,sub_apply]
  rw [sub_eq_add_neg,pairSample_add_right,←neg_one_smul ℂ (diagonalFiber 0 _ (b z)),
    pairSample_smul_right,neg_one_mul,pairSample_add_right]
  rfl

private theorem sample_smul (f : Field289) (p : PhysicalMomentum) (c : ℝ) (a b : QuantumTest)
    (r : ℝ) (z : SourceCoordinateSlice) :
    fixedSample (diagonalFiber (c • p)) f a b (r,z)=(c:ℂ)*fixedSample (diagonalFiber p) f a b (r,z)+
      (1-c:ℂ)*fixedSample (diagonalFiber 0) f a b (r,z) := by
  simp only [fixedSample,diagonal_smul,add_apply,smul_apply,pairSample_add_right,pairSample_smul_right]

private theorem form_add (f : Field289) (p k : PhysicalMomentum) (a b : QuantumTest) :
    fixedDiagonalForm f (p+k) a b=ᶠ[𝓝 (0:ℝ)]
      fun r=>fixedDiagonalForm f p a b r+fixedDiagonalForm f k a b r-fixedDiagonalForm f 0 a b r := by
  have near : ∀ᶠr in 𝓝 (0:ℝ),|r|<fieldRadius f a :=
    (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by simpa using fieldRadius_positive f a))
  filter_upwards [near] with r small
  have hp:=fixedFiber_integrable (diagonalFiber p) (diagonalFiber_smooth p) f a b r small
  have hk:=fixedFiber_integrable (diagonalFiber k) (diagonalFiber_smooth k) f a b r small
  have h0:=fixedFiber_integrable (diagonalFiber 0) (diagonalFiber_smooth 0) f a b r small
  unfold fixedDiagonalForm fixedFiber
  simp only [sample_add]
  have split := integral_sub (hp.add hk) h0
  simp only [Pi.add_apply] at split
  rw [split,integral_add hp hk]
  ring

private theorem form_smul (f : Field289) (p : PhysicalMomentum) (c : ℝ) (a b : QuantumTest) :
    fixedDiagonalForm f (c • p) a b=ᶠ[𝓝 (0:ℝ)]
      fun r=>(c:ℂ)*fixedDiagonalForm f p a b r+(1-c:ℂ)*fixedDiagonalForm f 0 a b r := by
  have near : ∀ᶠr in 𝓝 (0:ℝ),|r|<fieldRadius f a :=
    (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by simpa using fieldRadius_positive f a))
  filter_upwards [near] with r small
  have hp:=fixedFiber_integrable (diagonalFiber p) (diagonalFiber_smooth p) f a b r small
  have h0:=fixedFiber_integrable (diagonalFiber 0) (diagonalFiber_smooth 0) f a b r small
  unfold fixedDiagonalForm fixedFiber
  simp only [sample_smul]
  rw [integral_add (hp.const_mul _) (h0.const_mul _),integral_const_mul,integral_const_mul]
  ring

private theorem entry_add (f : Field289) (p k : PhysicalMomentum) (a b : QuantumTest) :
    fixedCurrentEntry f (p+k) a b=fixedCurrentEntry f p a b+fixedCurrentEntry f k a b-fixedCurrentEntry f 0 a b := by
  have derivative:=((fixedDiagonalJets f p a b).actual.1.add (fixedDiagonalJets f k a b).actual.1).sub
    (fixedDiagonalJets f 0 a b).actual.1
  have same:=(fixedDiagonalJets f (p+k) a b).actual.1.unique
    (derivative.congr_of_eventuallyEq (form_add f p k a b))
  simpa only [fixedCurrentEntry_source] using same

private theorem entry_smul (f : Field289) (p : PhysicalMomentum) (c : ℝ) (a b : QuantumTest) :
    fixedCurrentEntry f (c • p) a b=(c:ℂ)*fixedCurrentEntry f p a b+(1-c:ℂ)*fixedCurrentEntry f 0 a b := by
  have derivative:=((fixedDiagonalJets f p a b).actual.1.const_mul (c:ℂ)).add
    ((fixedDiagonalJets f 0 a b).actual.1.const_mul (1-c:ℂ))
  have same:=(fixedDiagonalJets f (c • p) a b).actual.1.unique
    (derivative.congr_of_eventuallyEq (form_smul f p c a b))
  simpa only [fixedCurrentEntry_source] using same

open NativeHistoryGrade (Label projection)
local instance : Fintype Label := Fintype.ofFinite _
attribute [local irreducible] fixedCurrentEntry sourceYJet sourceAssembly bareTest physicalFrame

private def spanAssembly (P : Submodule ℂ H) [FiniteDimensional ℂ P] (core : P≤Core)
    (entry : QuantumTest→QuantumTest→ℂ) : H→L[ℂ]H :=
  ∑g : Label,∑i : Fin (Module.finrank ℂ P),∑j : Fin (Module.finrank ℂ P),
    entry (coreEquiv.symm ⟨(stdOrthonormalBasis ℂ P i).val,core (stdOrthonormalBasis ℂ P i).property⟩)
      (coreEquiv.symm ⟨(stdOrthonormalBasis ℂ P j).val,core (stdOrthonormalBasis ℂ P j).property⟩) •
      InnerProductSpace.rankOne ℂ (projection g (stdOrthonormalBasis ℂ P i).val)
        (projection g (stdOrthonormalBasis ℂ P j).val)

private theorem span_assembly_congr (P Q : Submodule ℂ H)
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ Q] (hP : P≤Core) (hQ : Q≤Core)
    (same : P=Q) (entry : QuantumTest→QuantumTest→ℂ) :
    spanAssembly P hP entry=spanAssembly Q hQ entry := by
  subst Q
  rfl

private theorem assembly_fixed (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (entry : QuantumTest→QuantumTest→ℂ) :
    sourceAssembly p F (fun i j=>entry (bareTest p F i) (bareTest p F j))=
      sourceAssembly 0 F (fun i j=>entry (bareTest 0 F i) (bareTest 0 F j)) := by
  unfold sourceAssembly bareTest physicalFrame physicalBasis
  exact span_assembly_congr (physicalSpan p F) (physicalSpan 0 F)
    (FiniteCoreEvolution.coreSpan_le (CanonicalPhysicalSpatial.physical p) F)
    (FiniteCoreEvolution.coreSpan_le (CanonicalPhysicalSpatial.physical 0) F)
    (sourcePhysicalSpan_momentum p 0 F) entry

private theorem current_fixed_frame (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointCurrent p F z 0 f =
      sourceAssembly 0 F (fun i j=>fixedCurrentEntry f p (bareTest 0 F i) (bareTest 0 F j))+
      sourceYJet f 0 F none 1 0 := by
  rw [jointCurrent_source,sourceCurrent_fixed]
  unfold fixedSourceCurrent
  rw [assembly_fixed p F (fixedCurrentEntry f p)]
  simp only [sourceYJet,sourceRetainer_momentum p 0 F]


private theorem current_add (f : Field289) (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointCurrent (p+k) F z 0 f = jointCurrent p F z 0 f+jointCurrent k F z 0 f-jointCurrent 0 F z 0 f := by
  simp only [current_fixed_frame,entry_add,sourceAssembly,sub_smul,add_smul,
    Finset.sum_sub_distrib,Finset.sum_add_distrib]
  abel


private theorem current_smul (f : Field289) (p : PhysicalMomentum) (c : ℝ) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointCurrent (c • p) F z 0 f =
      (c:ℂ) • jointCurrent p F z 0 f+(1-c:ℂ) • jointCurrent 0 F z 0 f := by
  simp only [current_fixed_frame,entry_smul,sourceAssembly,add_smul,mul_smul,
    Finset.sum_add_distrib,←Finset.smul_sum]
  simp only [smul_add,sub_smul,one_smul]
  module


private theorem subtract_affine_add {M : Type*} [AddCommGroup M]
    (A B C D : M) (paid : A=B+C-D) : A-D=(B-D)+(C-D) := by
  rw [paid]
  abel

private theorem subtract_affine_smul (A B D : H→L[ℂ]H) (c : ℝ)
    (paid : A=(c:ℂ) • B+(1-c:ℂ) • D) : A-D=c • (B-D) := by
  calc
    A-D=((c:ℂ) • B+(1-c:ℂ) • D)-D := congrArg (fun X : H→L[ℂ]H=>X-D) paid
    _=(c:ℂ) • (B-D) := by
      simp only [smul_sub]
      module
    _=c • (B-D) := (RCLike.real_smul_eq_coe_smul (K:=ℂ) c (B-D)).symm

/-- The original full-field current has an affine momentum dependence on its own fixed source span. -/
def jointCurrentMomentum (F : GaussUnitaryHistory.Index) (z : ℂ) :
    PhysicalMomentum →L[ℝ] (Field289 →L[ℝ] (H →L[ℂ] H)) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p => jointCurrent p F z 0-jointCurrent 0 F z 0
    map_add' := fun p k => by
      apply ContinuousLinearMap.ext
      intro f
      change jointCurrent (p+k) F z 0 f-jointCurrent 0 F z 0 f =
        (jointCurrent p F z 0 f-jointCurrent 0 F z 0 f)+
        (jointCurrent k F z 0 f-jointCurrent 0 F z 0 f)
      exact subtract_affine_add _ _ _ _ (current_add f p k F z)
    map_smul' := fun c p => by
      apply ContinuousLinearMap.ext
      intro f
      change jointCurrent (c • p) F z 0 f-jointCurrent 0 F z 0 f =
        c • (jointCurrent p F z 0 f-jointCurrent 0 F z 0 f)
      exact subtract_affine_smul _ _ _ c (current_smul f p c F z) }

theorem joint_current_affine (F : GaussUnitaryHistory.Index) (z : ℂ) (p : PhysicalMomentum) :
    jointCurrent p F z 0 = jointCurrent 0 F z 0+jointCurrentMomentum F z p := by
  change jointCurrent p F z 0 = jointCurrent 0 F z 0+(jointCurrent p F z 0-jointCurrent 0 F z 0)
  abel

attribute [local irreducible] jointCurrentMomentum

theorem joint_current_momentum_continuous (F : GaussUnitaryHistory.Index) (z : ℂ) :
    Continuous (fun p : PhysicalMomentum => jointCurrent p F z 0) := by
  exact (continuous_const.add (jointCurrentMomentum F z).continuous).congr
    (fun p=>(joint_current_affine F z p).symm)

theorem joint_current_momentum_field_continuous (F : GaussUnitaryHistory.Index) (z : ℂ) :
    Continuous (fun pf : PhysicalMomentum × Field289 => jointCurrent pf.1 F z 0 pf.2) :=
  ((joint_current_momentum_continuous F z).comp continuous_fst).clm_apply continuous_snd


end LowEnergy.GaussComposite.ActualEMJointCurrentMomentum
