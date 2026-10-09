import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePhotonResidueWard

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePolarizationEmitter
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumNativePoleTensor PreparationVacuumOriginalGreenFeedback
open PreparationPhysicalNativePhotonScatteringSheetReturn Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] extendedTensor physicalDeterminant physicalSlope

private theorem kernel_pivot_factor (M : Matrix (Fin 5) (Fin 5) ℂ) (k : Fin 5)
    (zeroDet : M.det=0) (cofactor : M.adjugate k k≠0) (w x : Fin 5→ℂ)
    (wk : w k≠0) (hw : M*ᵥw=0) (hx : M*ᵥx=0) : x=(x k/w k) • w := by
  let B:=M+Matrix.single k k 1
  have update : B=M.updateRow k (M k+Pi.single k 1) := by
    ext i j
    by_cases row : i=k
    · subst i
      simp [B,Matrix.updateRow_apply,Matrix.single_apply,Pi.single_apply,eq_comm]
    · simp [B,Matrix.updateRow_apply,row,Ne.symm row]
  have determinant : B.det=M.adjugate k k := by
    rw [update,Matrix.det_updateRow_add,Matrix.updateRow_eq_self,zeroDet,zero_add,Matrix.adjugate_apply]
  have unit : IsUnit B.det:=isUnit_iff_ne_zero.mpr (determinant ▸ cofactor)
  have return_kernel (v : Fin 5→ℂ) (hv : M*ᵥv=0) : v=(v k) • (B⁻¹*ᵥPi.single k 1) := by
    have applied : B*ᵥv=(v k) • Pi.single k 1 := by
      rw [show B=M+Matrix.single k k 1 from rfl,Matrix.add_mulVec,hv,zero_add,Matrix.single_mulVec_eq,one_mul]
    have returned:=congrArg (fun z=>B⁻¹*ᵥz) applied
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul B unit,Matrix.one_mulVec,Matrix.mulVec_smul] at returned
    exact returned
  calc
    x=(x k) • (B⁻¹*ᵥPi.single k 1):=return_kernel x hx
    _=(x k/w k) • ((w k) • (B⁻¹*ᵥPi.single k 1)) := by
      rw [smul_smul]
      congr 1
      field_simp
    _=(x k/w k) • w := by rw [←return_kernel w hw]

private theorem source_sheet_data (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      (extendedTensor e.val (sourceSheet branch n unit e.val) n).det=0 ∧
      physicalSlope e.val (sourceSheet branch n unit e.val) n≠0 ∧
      (extendedTensor e.val (sourceSheet branch n unit e.val) n).adjugate (residueIndex branch) (residueIndex branch)≠0 := by
  have trajectory : Tendsto (fun e : ℝ=>(e,sourceSheet branch n unit e)) (𝓝 0) (𝓝 (0,sourceSpeed branch)) :=
    tendsto_id.prodMk_nhds (sourceSheet_tendsto branch n unit)
  have tensor := (extendedTensor_smooth (sourceSpeed branch) n).continuousAt.tendsto.comp trajectory
  have adjugate:=continuous_id.matrix_adjugate.continuousAt.tendsto.comp tensor
  have entry:=((continuous_apply (residueIndex branch)).comp (continuous_apply (residueIndex branch))).tendsto _ |>.comp adjugate
  simp only [Function.comp_def,id_eq,extendedTensor_origin] at entry
  have nonzero:=entry.eventually_ne (source_adjugate_nonzero branch n unit)
  filter_upwards [scaleVal_tendsto.eventually (sourceSheet_bounds branch n unit),
    scaleVal_tendsto.eventually (sourceSheet_equation branch n unit),
    scaleVal_tendsto.eventually (sourceSheet_simple branch n unit),scaleVal_tendsto.eventually nonzero]
      with e bounds equation simple pivot
  have inside : |sourceSheet branch n unit e.val|≤1 := by
    apply abs_le.mpr
    split_ifs at bounds <;> constructor <;> linarith
  have actual:=extendedTensor_actual e ⟨sourceSheet branch n unit e.val,inside⟩ n (unit_direction_bound n unit)
  have real:=normalizedEffective_det_real e ⟨sourceSheet branch n unit e.val,inside⟩ n (unit_direction_bound n unit)
  have zero : (extendedTensor e.val (sourceSheet branch n unit e.val) n).det=0 := by
    rw [actual,real,←actual]
    unfold physicalDeterminant at equation
    simp only [equation,Complex.ofReal_zero]
  exact ⟨zero,simple.1,pivot⟩

/-- The pole column is fixed by the original branch cofactor, rather than a supplied mode or normalization. -/
def sourceNativePoleColumn (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 5→ℂ :=
  fun i=>sourceResidue epsilon s n i (residueIndex branch)

def sourceNativePoleCoefficient (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (v : Fin 5→ℂ) : ℂ :=
  (sourceResidue epsilon s n*ᵥv) (residueIndex branch)/
    sourceResidue epsilon s n (residueIndex branch) (residueIndex branch)

/-- The actual simple sheet generates its nonzero pole column and every exact source coefficient on the same carrier. -/
theorem sourceNativePoleColumn_generated (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      sourceNativePoleColumn branch e.val (sourceSheet branch n unit e.val) n≠0 ∧
      extendedTensor e.val (sourceSheet branch n unit e.val) n*ᵥ
        sourceNativePoleColumn branch e.val (sourceSheet branch n unit e.val) n=0 ∧
      ∀v : Fin 5→ℂ,sourceResidue e.val (sourceSheet branch n unit e.val) n*ᵥv=
        sourceNativePoleCoefficient branch e.val (sourceSheet branch n unit e.val) n v •
          sourceNativePoleColumn branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [source_sheet_data branch n unit] with e data
  let s:=sourceSheet branch n unit e.val
  let M:=extendedTensor e.val s n
  let R:=sourceResidue e.val s n
  let k:=residueIndex branch
  have pivot : R k k≠0 := by
    simp only [R,sourceResidue,Matrix.smul_apply,smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr data.2.1)) data.2.2
  have product : M*R=0 := by
    change extendedTensor e.val s n*((physicalSlope e.val s n:ℂ)⁻¹ • (extendedTensor e.val s n).adjugate)=0
    rw [Matrix.mul_smul,Matrix.mul_adjugate,data.1]
    simp
  have column : M*ᵥsourceNativePoleColumn branch e.val s n=0 := by
    funext i
    change (M*R) i k=0
    rw [product]
    rfl
  have columnNonzero : sourceNativePoleColumn branch e.val s n≠0 := by
    intro zero
    exact pivot (congrFun zero k)
  refine ⟨columnNonzero,column,?_⟩
  intro v
  have input : M*ᵥ(R*ᵥv)=0 := by rw [Matrix.mulVec_mulVec,product,Matrix.zero_mulVec]
  exact kernel_pivot_factor M k data.1 data.2.2 (sourceNativePoleColumn branch e.val s n) (R*ᵥv) pivot column input

end LowEnergy.PreparationPhysicalNativePolarizationEmitter
