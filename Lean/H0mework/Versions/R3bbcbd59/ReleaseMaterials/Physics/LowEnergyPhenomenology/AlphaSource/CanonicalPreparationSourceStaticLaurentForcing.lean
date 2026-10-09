import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticLaurentCurrent

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumStaticSimpleCoupling
open PreparationVacuumObservedPoleTensor PreparationVacuumObservedStaticResidue
open PreparationVacuumNativeSlowCoupling PreparationVacuumFullSlowFieldResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumQuantumSlowResidue PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource PreparationVacuumCausalPoleResponse PreparationVacuumPhysicalPoleSheet
open PreparationVacuumFullOriginResponse
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] fullKernelFrame activeProjection fullInverse originalReadback
  sourceStaticCurrent sourceCurrentSimple sourceFullCurrentResidue sourceOriginCurrentResidue sourceNativeReaderFirst

private theorem linear_power (a : Powers) (degree : a.total=1) (p q : Fin 4→ℂ) (z : ℂ) :
    a.value (p+z • q)=a.value p+z*a.value q := by
  rcases a with ⟨t,x,y,w⟩
  simp only [Powers.total] at degree
  have cases : (t=1∧x=0∧y=0∧w=0)∨(t=0∧x=1∧y=0∧w=0)∨
      (t=0∧x=0∧y=1∧w=0)∨(t=0∧x=0∧y=0∧w=1) := by omega
  rcases cases with h|h|h|h <;> rcases h with ⟨rfl,rfl,rfl,rfl⟩ <;>
    simp [Powers.value]

private theorem linear_matrix (terms : List SourceTerm) (degree : ∀a∈terms,a.powers.total=1)
    (p q : Fin 4→ℂ) (z : ℂ) : sourceMatrix terms (p+z • q)=sourceMatrix terms p+z • sourceMatrix terms q := by
  induction terms with
  | nil=>simp [sourceMatrix]
  | cons a rest ih=>
    have first : a.matrix (p+z • q)=a.matrix p+z • a.matrix q := by
      ext i j
      simp only [SourceTerm.matrix,Matrix.add_apply,Matrix.smul_apply,Matrix.single_apply]
      split_ifs <;> simp only [smul_eq_mul,linear_power a.powers (degree a (by simp)),mul_add] <;> ring
    rw [sourceMatrix_cons,sourceMatrix_cons,sourceMatrix_cons,first,ih (fun b hb=>degree b (by simp [hb]))]
    module

private theorem linear_part (terms : List SourceTerm) (p q : Fin 4→ℂ) (z : ℂ) :
    sourceLinearPart terms (p+z • q)=sourceLinearPart terms p+z • sourceLinearPart terms q := by
  apply linear_matrix
  intro a member
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- The actual source first jet retains both its spatial part and its genuine time derivative. -/
theorem sourceReaderFirst_static_split (n : PhysicalMomentum) (eta : ℂ) :
    sourceNativeReaderFirst (fixedMomentum n eta)=
      sourceNativeReaderFirst (fixedMomentum n 0)+eta • sourceNativeReaderFirst (fixedMomentum 0 1) := by
  have point : fixedMomentum n eta=fixedMomentum n 0+eta • fixedMomentum 0 1 := by
    ext i
    refine Fin.cases ?_ (fun j=>?_) i
    · simp [fixedMomentum,fullMomentum]
    · simp [fixedMomentum,fullMomentum,PreparationVacuumPhysicalFeedback.physicalSpatial]
  rw [point]
  simp only [sourceNativeReaderFirst,linear_part,mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
  module

/-- Gauge B0, both retainer cross-returns, and the time-jet action on B1's double coefficient are generated together. -/
def sourceNativeSimple (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) : Fin 289→ℂ :=
  sourceOriginPair ((3/10:ℂ)*rootTwo*(sourceStaticGaugeCurrent q n l r 1 0-sourceStaticGaugeCurrent q n l r 2 1))+
    sourceNativeReaderFirst (fixedMomentum n 0)*ᵥsourceCurrentSimple q n l r+
    sourceNativeReaderFirst (fixedMomentum 0 1)*ᵥsourceStaticCurrent q n l r

private theorem native_simple_split (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) (eta : ℝ) :
    (eta:ℂ) • (sourceActualNativeResidue q n (eta:ℂ) l r-
      ((eta:ℂ)⁻¹)^2 • sourceStaticNative q n l r)=
    (eta:ℂ) • sourceOriginCurrentResidue q n (eta:ℂ) l r+
      sourceNativeReaderFirst (fixedMomentum n 0)*ᵥ((eta:ℂ) •
        (sourceFullCurrentResidue q n (eta:ℂ) l r-((eta:ℂ)⁻¹)^2 • sourceStaticCurrent q n l r))+
      sourceNativeReaderFirst (fixedMomentum 0 1)*ᵥ(((eta:ℂ)^2) • sourceFullCurrentResidue q n (eta:ℂ) l r) := by
  rw [sourceActualNativeResidue,sourceStaticNative,sourceReaderFirst_static_split n (eta:ℂ)]
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.mulVec_sub,Matrix.mulVec_smul,pow_two]
  module

/-- The complete actual native forcing produces its simple static coefficient after explicit double subtraction. -/
theorem sourceNative_simple_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>(eta:ℂ) • (sourceActualNativeResidue q n (eta:ℂ) l r-
      ((eta:ℂ)⁻¹)^2 • sourceStaticNative q n l r))
      (𝓝[>] 0) (𝓝 (sourceNativeSimple q n l r)) := by
  have spatial:=((continuous_const.matrix_mulVec continuous_id).continuousAt.tendsto.comp
    (sourceCurrent_simple_generated q n l r) :
    Tendsto (fun eta : ℝ=>sourceNativeReaderFirst (fixedMomentum n 0)*ᵥ((eta:ℂ) •
      (sourceFullCurrentResidue q n (eta:ℂ) l r-((eta:ℂ)⁻¹)^2 • sourceStaticCurrent q n l r)))
      (𝓝[>] 0) (𝓝 (sourceNativeReaderFirst (fixedMomentum n 0)*ᵥsourceCurrentSimple q n l r)))
  have temporal:=((continuous_const.matrix_mulVec continuous_id).continuousAt.tendsto.comp
    (sourceStaticCurrent_generated q n l r) :
    Tendsto (fun eta : ℝ=>sourceNativeReaderFirst (fixedMomentum 0 1)*ᵥ
      (((eta:ℂ)^2) • sourceFullCurrentResidue q n (eta:ℂ) l r))
      (𝓝[>] 0) (𝓝 (sourceNativeReaderFirst (fixedMomentum 0 1)*ᵥsourceStaticCurrent q n l r)))
  simpa only [native_simple_split,sourceNativeSimple,Function.comp_def,id_eq] using
    ((sourceStaticOrigin_generated q n l r).add spatial).add temporal

/-- The same full source slow read consumes the new coefficient. -/
theorem sourceSlow_simple_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>(eta:ℂ) • (sourceSlowRead (sourceActualNativeResidue q n (eta:ℂ) l r)-
      ((eta:ℂ)⁻¹)^2 • sourceSlowRead (sourceStaticNative q n l r)))
      (𝓝[>] 0) (𝓝 (sourceSlowRead (sourceNativeSimple q n l r))) := by
  have continuous : Continuous sourceSlowRead := by
    apply continuous_pi
    intro i
    unfold sourceSlowRead
    split_ifs <;> fun_prop
  have h:=continuous.continuousAt.tendsto.comp (sourceNative_simple_generated q n l r)
  apply h.congr
  intro eta
  ext i
  simp only [Function.comp_def,sourceSlowRead,Matrix.mulVec_sub,Matrix.mulVec_smul,Pi.smul_apply,Pi.sub_apply]
  split_ifs <;> simp only [smul_zero,sub_self]

end LowEnergy.PreparationVacuumStaticSimpleCoupling
