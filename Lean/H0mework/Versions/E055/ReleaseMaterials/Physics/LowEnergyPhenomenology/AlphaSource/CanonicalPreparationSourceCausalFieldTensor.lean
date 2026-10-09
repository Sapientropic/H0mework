import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActualNativeCoupling

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullSlowFieldResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumNativePoleTensor PreparationVacuumNativeSlowCoupling
open PreparationVacuumCausalPoleResponse PreparationVacuumPhysicalFeedback CanonicalGradedSpatialSource
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] activeKernel fullKernelFrame unrestrictedGreen slowFastFrame

def sourceRawEffective (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fullKernelFrame.transpose*activeKernel p*fullKernelFrame-
    fullKernelFrame.transpose*activeKernel p*unrestrictedGreen p*activeKernel p*fullKernelFrame

theorem sourceRawEffective_actual (p : complementRegular) : sourceRawEffective p.val=effectiveKernel p := by
  simp only [sourceRawEffective,effectiveKernel,unrestrictedGreen,complementGreen]

/-- Single-sided scaling retains the slow-to-fast time-space source entry. -/
def sourceCausalPrincipal (n : PhysicalMomentum) (zeta : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal ![
    rootTwo*rootFifteen*(-(25/18:ℂ)*zeta^2+(25/54:ℂ)*(spatialSquare n:ℂ)),
    rootTwo*rootFifteen*((10/99:ℂ)*zeta^2+(12/335:ℂ)*(spatialSquare n:ℂ)),
    rootTwo*rootFifteen*((20/27:ℂ)*zeta^2+(8/15:ℂ)*(spatialSquare n:ℂ)),0,0]+
  Matrix.single 2 3 (-(40/9:ℂ)*Complex.I*zeta*(n 2:ℂ)-(20/27:ℂ)*rootTwo*rootFifteen*zeta^2)+
  Matrix.single 3 4 (-8*rootTwo*zeta)+Matrix.single 4 3 (8*rootTwo*zeta)

def sourceCausalFast (n : PhysicalMomentum) (zeta : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.single 3 2 (-(40/9:ℂ)*Complex.I*zeta*(n 2:ℂ)-(20/27:ℂ)*rootTwo*rootFifteen*zeta^2)+
  Matrix.single 3 3 (-(4/5:ℂ)*rootTwo*rootFifteen*(spatialSquare n:ℂ)+(40/3:ℂ)*Complex.I*zeta*(n 2:ℂ)+
    (110/81:ℂ)*rootTwo*rootFifteen*zeta^2)+
  Matrix.single 4 4 (-(4/5:ℂ)*rootTwo*rootFifteen*(spatialSquare n:ℂ)+(50/27:ℂ)*rootTwo*rootFifteen*zeta^2)

def sourceCausalNormalized (n : PhysicalMomentum) (zeta : ℂ) (d : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  (wideRayScaling d*(slowFastFrame.transpose*
    sourceRawEffective (fixedMomentum (d • n) ((d:ℂ)*zeta))*slowFastFrame)).submatrix fiveIndex fiveIndex

/-- The complete degree-one and degree-two source tensor generates this complex causal corner. -/
theorem sourceCausalLeading_generated (n : PhysicalMomentum) (zeta : ℂ) (d : ℝ) (nonzero : d≠0) :
    (wideRayScaling d*(slowFastFrame.transpose*
      leadingTensor (fixedMomentum (d • n) ((d:ℂ)*zeta))*slowFastFrame)).submatrix fiveIndex fiveIndex=
      sourceCausalPrincipal n zeta+(d:ℂ) • sourceCausalFast n zeta := by
  rw [slowFastLeading_generated]
  have complexNonzero : (d:ℂ)≠0 := Complex.ofReal_ne_zero.mpr nonzero
  have ray0 : fixedMomentum (d • n) ((d:ℂ)*zeta) 0=(d:ℂ)*zeta := rfl
  have ray1 : fixedMomentum (d • n) ((d:ℂ)*zeta) 1=Complex.I*((d*n 0:ℝ):ℂ) := rfl
  have ray2 : fixedMomentum (d • n) ((d:ℂ)*zeta) 2=Complex.I*((d*n 1:ℝ):ℂ) := rfl
  have ray3 : fixedMomentum (d • n) ((d:ℂ)*zeta) 3=Complex.I*((d*n 2:ℝ):ℂ) := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [wideRayScaling,Matrix.diagonal_mul,Matrix.submatrix_apply,fiveIndex,
      sourceMatrix,slowFastLeadingTerms,SourceTerm.matrix,Powers.value,coefficientValue,
      ray0,ray1,ray2,ray3,sourceCausalPrincipal,sourceCausalFast,spatialSquare,
      Matrix.single_apply,Matrix.diagonal_apply,Matrix.add_apply,Matrix.smul_apply,Pi.smul_apply,
      smul_eq_mul,Fin.ext_iff,mul_pow,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow,Complex.I_sq] <;>
    field_simp [complexNonzero] <;> ring

def sourceCausalErrorBudget (n : PhysicalMomentum) (zeta : ℂ) : ℝ :=
  scaledErrorBudget*(1+‖fixedMomentum n zeta‖)^3

private theorem readerRadius_le (v : Fin 4→ℂ) : sourceReaderRadius v≤ PreparationVacuumFullOriginResponse.sourceRadius := by
  apply (div_le_iff₀ (show 0<1+‖v‖ by positivity)).mpr
  have nonnegative:=PreparationVacuumFullOriginResponse.sourceRadius_pos.le
  nlinarith [norm_nonneg v]

private theorem matrix_entry_price (M : Matrix (Fin 289) (Fin 289) ℂ) (i j : Fin 289) : ‖M i j‖≤‖M‖ := by
  have column:=Matrix.linfty_opNorm_mulVec M (Pi.single j (1:ℂ))
  simp only [Matrix.mulVec_single_one,Pi.norm_single,norm_one,mul_one] at column
  exact (norm_le_pi_norm (M.col j) i).trans column

/-- The original complementary inverse supplies a quantitative full Schur error on a generated radius. -/
theorem sourceCausalNormalized_error (n : PhysicalMomentum) (zeta : ℂ) (d : ℝ) (positive : 0<d)
    (small : d ≤ sourceReaderRadius (fixedMomentum n zeta)) (i j : Fin 5) :
    ‖(sourceCausalNormalized n zeta d-(sourceCausalPrincipal n zeta+(d:ℂ) • sourceCausalFast n zeta)) i j‖≤
      sourceCausalErrorBudget n zeta*d := by
  let v:=fixedMomentum n zeta
  let p:=fixedMomentum (d • n) ((d:ℂ)*zeta)
  let r:=d*(1+‖v‖)
  have smallComplex : ‖(d:ℂ)‖≤ sourceReaderRadius v := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive] using small
  have cap : r≤ PreparationVacuumFullOriginResponse.sourceRadius := by
    simpa only [sourceReaderScale,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive] using sourceReaderScale_bound (d:ℂ) v smallComplex
  have bound : ∀i,‖p i‖≤ r := by
    intro i
    simpa only [p,sourcePhysicalRay_generated,sourceReaderScale,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive] using sourceReader_point_bound (d:ℂ) v i
  have remainder : ‖sourceRawEffective p-leadingTensor p‖≤ effectiveErrorBudget*r^3 := by
    have h:=effectiveKernel_leading_price p r (by dsimp only [r];positivity) cap bound
    simpa only [sourceRawEffective,effectiveKernel,unrestrictedGreen,complementGreen,
      PreparationVacuumFullOriginResponse.controlledPoint] using h
  let scale : scaleDomain:=⟨d,positive,small.trans (readerRadius_le v)⟩
  have D : ‖wideRayScaling d‖≤ d⁻¹^2 := wideRayScaling_price scale
  have controlled : ‖wideRayScaling d*(slowFastFrame.transpose*(sourceRawEffective p-leadingTensor p)*slowFastFrame)‖≤
      sourceCausalErrorBudget n zeta*d := by
    calc
      _≤‖wideRayScaling d‖*(‖slowFastFrame.transpose‖*‖sourceRawEffective p-leadingTensor p‖*‖slowFastFrame‖) := by
        apply (norm_mul_le _ _).trans
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _≤ d⁻¹^2*(‖slowFastFrame.transpose‖*(effectiveErrorBudget*r^3)*‖slowFastFrame‖) := by gcongr
      _=sourceCausalErrorBudget n zeta*d := by
        unfold sourceCausalErrorBudget scaledErrorBudget r v
        field_simp [positive.ne']
  rw [←sourceCausalLeading_generated n zeta d positive.ne']
  have difference : sourceCausalNormalized n zeta d-
      (wideRayScaling d*(slowFastFrame.transpose*leadingTensor p*slowFastFrame)).submatrix fiveIndex fiveIndex=
      (wideRayScaling d*(slowFastFrame.transpose*(sourceRawEffective p-leadingTensor p)*slowFastFrame)).submatrix fiveIndex fiveIndex := by
    simp only [sourceCausalNormalized,p,mul_sub,sub_mul,Matrix.submatrix_sub]
    rfl
  rw [difference]
  exact (matrix_entry_price _ (fiveIndex i) (fiveIndex j)).trans controlled

theorem sourceCausalNormalized_limit (n : PhysicalMomentum) (zeta : ℂ) :
    Tendsto (sourceCausalNormalized n zeta) (𝓝[>] 0) (𝓝 (sourceCausalPrincipal n zeta)) := by
  have near : ∀ᶠ d : ℝ in 𝓝[>] 0,0<d ∧ d≤ sourceReaderRadius (fixedMomentum n zeta) := by
    have small : ∀ᶠ d : ℝ in 𝓝 0,d<sourceReaderRadius (fixedMomentum n zeta) :=
      continuous_id.continuousAt.eventually_lt_const (sourceReaderRadius_positive _)
    filter_upwards [self_mem_nhdsWithin,small.filter_mono nhdsWithin_le_nhds] with d positive smallD
    exact ⟨positive,smallD.le⟩
  have scalar : Tendsto (fun d : ℝ=>(d:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have main:=(tendsto_const_nhds (x:=sourceCausalPrincipal n zeta)).add
    (scalar.smul (tendsto_const_nhds (x:=sourceCausalFast n zeta)))
  simp only [zero_smul,add_zero] at main
  have price : Tendsto (fun d : ℝ=>sourceCausalErrorBudget n zeta*d) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero,id_eq] using (tendsto_const_nhds.mul (tendsto_id : Tendsto (fun d : ℝ=>d) (𝓝 0) (𝓝 0))).mono_left nhdsWithin_le_nhds
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have error : Tendsto (fun d : ℝ=>(sourceCausalNormalized n zeta d-
      (sourceCausalPrincipal n zeta+(d:ℂ) • sourceCausalFast n zeta)) i j) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (near.mono (fun d h=>sourceCausalNormalized_error n zeta d h.1 h.2 i j)) price
  have entry:=(continuous_apply j).continuousAt.tendsto.comp ((continuous_apply i).continuousAt.tendsto.comp main)
  have result:=error.add entry
  simpa only [Function.comp_def,Matrix.sub_apply,sub_add_cancel,zero_add] using result

private theorem sparse_causal_det (a b c d t : ℂ) :
    (Matrix.diagonal (![a,b,c,0,0] : Fin 5→ℂ)+Matrix.single 2 3 t+
      Matrix.single 3 4 d+Matrix.single 4 3 (-d)).det=a*b*c*d^2 := by
  let M : Matrix (Fin 5) (Fin 5) ℂ:=Matrix.diagonal ![a,b,c,0,0]+Matrix.single 2 3 t+
    Matrix.single 3 4 d+Matrix.single 4 3 (-d)
  have shape : M.submatrix id (Equiv.swap (3:Fin 5) 4)=
      Matrix.diagonal ![a,b,c,d,-d]+Matrix.single 2 4 t := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [M,Matrix.submatrix_apply,Matrix.diagonal_apply,Matrix.single_apply,Matrix.add_apply,Equiv.swap_apply_def,Fin.ext_iff]
  have upper : (Matrix.diagonal (![a,b,c,d,-d] : Fin 5→ℂ)+Matrix.single 2 4 t).IsUpperTriangular := by
    intro i j h
    change j < i at h
    have different : i≠j := by omega
    have off : ¬(2=i ∧ 4=j) := by
      rintro ⟨hi,hj⟩
      rw [←hi,←hj] at h
      exact (by decide : ¬((4:Fin 5)<2)) h
    simp [different,off]
  have diag : (fun i : Fin 5=>(show Matrix (Fin 5) (Fin 5) ℂ from Matrix.diagonal ![a,b,c,d,-d]+Matrix.single 2 4 t) i i)=![a,b,c,d,-d] := by
    funext i
    fin_cases i <;> norm_num [Matrix.add_apply,Matrix.diagonal_apply,Matrix.single_apply,Fin.ext_iff]
  have triangular:=Matrix.det_of_isUpperTriangular upper
  rw [diag] at triangular
  have permuted:=Matrix.det_permute' (Equiv.swap (3:Fin 5) 4) M
  rw [shape,triangular] at permuted
  norm_num [Fin.prod_univ_succ,Fin.ext_iff] at permuted
  change M.det=a*b*c*d^2
  calc
    _=a*(b*(c*(d*d))) := permuted.symm
    _=_ := by ring

theorem sourceCausalPrincipal_det (n : PhysicalMomentum) (zeta : ℂ) :
    (sourceCausalPrincipal n zeta).det=128*zeta^2*
      (rootTwo*rootFifteen*(-(25/18:ℂ)*zeta^2+(25/54:ℂ)*(spatialSquare n:ℂ)))*
      (rootTwo*rootFifteen*((10/99:ℂ)*zeta^2+(12/335:ℂ)*(spatialSquare n:ℂ)))*
      (rootTwo*rootFifteen*((20/27:ℂ)*zeta^2+(8/15:ℂ)*(spatialSquare n:ℂ))) := by
  have rootSquare : rootTwo^2=(2:ℂ) := by norm_num [rootTwo,←Complex.ofReal_pow,Real.sq_sqrt]
  unfold sourceCausalPrincipal
  have minus : 8*rootTwo*zeta= -(-8*rootTwo*zeta) := by ring
  rw [minus,sparse_causal_det]
  simp only [mul_pow,rootSquare]
  ring

/-- The admissible corner is generated from the actual full five-channel determinant. -/
def sourceCausalDomain (n : PhysicalMomentum) : Set ℂ :=
  {zeta | 0<zeta.re ∧ (sourceCausalPrincipal n zeta).det≠0}

theorem sourceCausalDomain_one (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    (1:ℂ)∈sourceCausalDomain n := by
  constructor
  · norm_num
  · rw [sourceCausalPrincipal_det,unit]
    have two : rootTwo≠0 := by norm_num [rootTwo,Real.sqrt_ne_zero']
    have fifteen : rootFifteen≠0 := by norm_num [rootFifteen,Real.sqrt_ne_zero']
    norm_num [two,fifteen]

theorem sourceCausalDomain_nonempty (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    (sourceCausalDomain n).Nonempty := ⟨1,sourceCausalDomain_one n unit⟩

/-- The complete Schur tensor, with its original complementary inverse, becomes invertible on this source corner. -/
theorem sourceCausalNormalized_eventually_unit (n : PhysicalMomentum) (zeta : sourceCausalDomain n) :
    ∀ᶠ d : ℝ in 𝓝[>] 0,IsUnit (sourceCausalNormalized n zeta.val d).det := by
  have determinant:=(continuous_id.matrix_det.continuousAt.tendsto).comp (sourceCausalNormalized_limit n zeta.val)
  exact (determinant.eventually_ne zeta.property.2).mono (fun d nonzero=>isUnit_iff_ne_zero.mpr nonzero)

end LowEnergy.PreparationVacuumFullSlowFieldResponse
