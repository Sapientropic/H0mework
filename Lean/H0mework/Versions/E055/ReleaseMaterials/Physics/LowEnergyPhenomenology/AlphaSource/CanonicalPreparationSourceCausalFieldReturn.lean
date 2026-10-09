import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCausalFieldTensor

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
open PreparationVacuumStaticPoleResponse PreparationVacuumWholeOrigin
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] activeKernel fullKernelFrame unrestrictedGreen slowFastFrame

def sourceCausalScale (n : PhysicalMomentum) (zeta : sourceCausalDomain n) : Set ℝ :=
  {d | 0<d ∧ d ≤ sourceReaderRadius (fixedMomentum n zeta.val) ∧
    IsUnit (sourceCausalNormalized n zeta.val d).det}

theorem sourceCausalScale_eventually (n : PhysicalMomentum) (zeta : sourceCausalDomain n) :
    ∀ᶠ d : ℝ in 𝓝[>] 0,d∈sourceCausalScale n zeta := by
  have small : ∀ᶠ d : ℝ in 𝓝 0,d<sourceReaderRadius (fixedMomentum n zeta.val) :=
    continuous_id.continuousAt.eventually_lt_const (sourceReaderRadius_positive _)
  filter_upwards [self_mem_nhdsWithin,small.filter_mono nhdsWithin_le_nhds,
    sourceCausalNormalized_eventually_unit n zeta] with d positive inside regular
  exact ⟨positive,inside.le,regular⟩

theorem sourceCausalScale_nonempty (n : PhysicalMomentum) (zeta : sourceCausalDomain n) :
    (sourceCausalScale n zeta).Nonempty := (sourceCausalScale_eventually n zeta).exists

private theorem radius_le (v : Fin 4→ℂ) : sourceReaderRadius v ≤ PreparationVacuumFullOriginResponse.sourceRadius := by
  apply (div_le_iff₀ (show 0<1+‖v‖ by positivity)).mpr
  have nonnegative:=PreparationVacuumFullOriginResponse.sourceRadius_pos.le
  nlinarith [norm_nonneg v]

def sourceRealScale (n : PhysicalMomentum) (zeta : sourceCausalDomain n) (d : sourceCausalScale n zeta) : scaleDomain :=
  ⟨d.val,d.property.1,d.property.2.1.trans (radius_le _)⟩

theorem sourceCausalComplement_regular (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (d : sourceCausalScale n zeta) : fixedMomentum (d.val • n) ((d.val:ℂ)*zeta.val)∈complementRegular := by
  apply sourceRadius_regular
  intro i
  have small : ‖(d.val:ℂ)‖ ≤ sourceReaderRadius (fixedMomentum n zeta.val) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos d.property.1] using d.property.2.1
  rw [sourcePhysicalRay_generated]
  exact (sourceReader_point_bound _ _ i).trans (sourceReaderScale_bound _ _ small)

def sourceCausalComplement (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (d : sourceCausalScale n zeta) : complementRegular :=
  ⟨fixedMomentum (d.val • n) ((d.val:ℂ)*zeta.val),sourceCausalComplement_regular n zeta d⟩

private theorem fiveVector_expansion (v : Fin 5→ℂ) :
    fiveVector v=∑i : Fin 5,v i • Pi.single (fiveIndex i) (1:ℂ) := by
  funext j
  by_cases inside : j.val<5
  · let i : Fin 5:=⟨j.val,inside⟩
    have same : j=fiveIndex i:=Fin.ext rfl
    simp only [fiveVector,dif_pos inside,Finset.sum_apply,Pi.smul_apply]
    rw [Finset.sum_eq_single i]
    · change v i=v i • ((Pi.single (fiveIndex i) (1:ℂ) : Fin 289→ℂ) j)
      simp only [Pi.single_apply,if_pos same,smul_eq_mul,mul_one]
    · intro k _ different
      have off : j≠fiveIndex k := by
        intro eq
        apply different
        exact Fin.ext (congrArg Fin.val eq).symm
      simp [off]
    · intro absent
      exact False.elim (absent (Finset.mem_univ i))
  · have outside (i : Fin 5) : j≠fiveIndex i := by
      intro same
      have equal:=congrArg Fin.val same
      change j.val=i.val at equal
      omega
    simp [fiveVector,inside,Finset.sum_apply,Pi.smul_apply,outside]

private theorem five_mulVec (M : Matrix (Fin 289) (Fin 289) ℂ) (v : Fin 5→ℂ) (i : Fin 5) :
    (M*ᵥfiveVector v) (fiveIndex i)=(M.submatrix fiveIndex fiveIndex*ᵥv) i := by
  rw [fiveVector_expansion,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,Matrix.mulVec_single_one,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Matrix.mulVec,Matrix.submatrix_apply,dotProduct,Matrix.col_apply,mul_comm]

private theorem scaling_right (e : ℝ) (M : Matrix (Fin 289) (Fin 289) ℂ) :
    (M*wideRayScaling e).submatrix fiveIndex fiveIndex=M.submatrix fiveIndex fiveIndex*rayScaling e := by
  ext i j
  simp only [wideRayScaling,rayScaling,Matrix.submatrix_apply,Matrix.mul_diagonal,fiveIndex]
  simp only [j.isLt,if_true]

def sourceCausalBalanced (n : PhysicalMomentum) (zeta : ℂ) (d : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  sourceCausalNormalized n zeta d*rayScaling d

theorem sourceCausalScaling_unit (d : ℝ) (nonzero : d≠0) : IsUnit (rayScaling d) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [rayScaling,Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr nonzero))
  · exact inv_ne_zero (Complex.ofReal_ne_zero.mpr nonzero)

theorem sourceCausalBalanced_unit (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (d : sourceCausalScale n zeta) : IsUnit (sourceCausalBalanced n zeta.val d.val) :=
  ((Matrix.isUnit_iff_isUnit_det _).mpr d.property.2.2).mul (sourceCausalScaling_unit d.val d.property.1.ne')

/-- The paid complete five-coordinate carrier is used at the original complex momentum. -/
theorem sourceCausalBalanced_response (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (d : sourceCausalScale n zeta) (v : Fin 5→ℂ) :
    sourceCausalBalanced n zeta.val d.val*ᵥv=
      (fun i=>(wideRayScaling d.val*ᵥ(slowFastFrame.transpose*ᵥ
        (effectiveKernel (sourceCausalComplement n zeta d)*ᵥmodeCoordinates (sourceRealScale n zeta d) v))) (fiveIndex i)) := by
  funext i
  unfold sourceCausalBalanced sourceCausalNormalized
  rw [←scaling_right,←five_mulVec]
  simp only [modeCoordinates,Matrix.mulVec_mulVec,mul_assoc]
  rw [←sourceRawEffective_actual]
  rfl

private theorem sourceEffective_kernel_zero (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (d : sourceCausalScale n zeta) (u : Fin 289→ℂ) (support : fiveProjection*ᵥu=u)
    (kernel : effectiveKernel (sourceCausalComplement n zeta d)*ᵥu=0) : u=0 := by
  have reduced : sourceCausalBalanced n zeta.val d.val*ᵥunscaleCoordinates (sourceRealScale n zeta d) u=0 := by
    rw [sourceCausalBalanced_response,modeCoordinates_unscale _ u support,kernel,Matrix.mulVec_zero,Matrix.mulVec_zero]
    rfl
  have zero : unscaleCoordinates (sourceRealScale n zeta d) u=0 := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr (sourceCausalBalanced_unit n zeta d)
    simpa only [Matrix.mulVec_zero] using reduced
  rw [←modeCoordinates_unscale (sourceRealScale n zeta d) u support,zero]
  have empty : fiveVector (0:Fin 5→ℂ)=0 := by funext i;simp [fiveVector]
  simp only [modeCoordinates,empty,Matrix.mulVec_zero]

private theorem sourceActive_kernel_zero (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (d : sourceCausalScale n zeta) (field : Fin 289→ℂ) (inside : activeProjection*ᵥfield=field)
    (kernel : activeKernel (sourceCausalComplement n zeta d).val*ᵥfield=0) : field=0 := by
  have reduced:=effective_actual_equation (sourceCausalComplement n zeta d) field 0 inside kernel
  rw [Matrix.mulVec_zero] at reduced
  have coordinates : blockCoordinates field=0 := sourceEffective_kernel_zero n zeta d _
    (blockCoordinates_supported field) reduced
  have returned:=effective_field_reconstruction (sourceCausalComplement n zeta d) field 0 inside kernel
  simpa only [coordinates,Matrix.mulVec_zero,add_zero] using returned

/-- The complete 103-dimensional field inverse is generated from the original source Schur system. -/
theorem sourceCausalField_regular (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (d : sourceCausalScale n zeta) : fixedMomentum (d.val • n) ((d.val:ℂ)*zeta.val)∈regularSource := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro left right same
  have kernel : extendedKernel (sourceCausalComplement n zeta d).val*ᵥ(left-right)=0 := by
    rw [Matrix.mulVec_sub]
    have literal : extendedKernel (sourceCausalComplement n zeta d).val*ᵥleft=
        extendedKernel (sourceCausalComplement n zeta d).val*ᵥright := by simpa only [sourceCausalComplement] using same
    rw [literal,sub_self]
  let field:=left-right
  have projected:=congrArg (fun v=>activeProjection*ᵥv) kernel
  rw [Matrix.mulVec_mulVec,original_active_extended,Matrix.mulVec_zero] at projected
  have inside : activeProjection*ᵥ(activeProjection*ᵥfield)=activeProjection*ᵥfield := by
    rw [Matrix.mulVec_mulVec,active_square]
  have zero : activeProjection*ᵥfield=0 := by
    apply sourceActive_kernel_zero n zeta d _ inside
    rw [Matrix.mulVec_mulVec,activeKernel_right]
    exact projected
  rw [extendedKernel,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,projected,zero,sub_zero,zero_add] at kernel
  exact sub_eq_zero.mp kernel

def sourceCausalFieldPoint (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (d : sourceCausalScale n zeta) : regularSource :=
  ⟨fixedMomentum (d.val • n) ((d.val:ℂ)*zeta.val),sourceCausalField_regular n zeta d⟩

/-- The joint corner is a nonempty source domain, rather than an externally supplied inverse condition. -/
theorem sourceCausalField_nonempty (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∃zeta : ℂ,0<zeta.re ∧ ∃d : ℝ,0<d ∧ fixedMomentum (d • n) ((d:ℂ)*zeta)∈regularSource := by
  let frequency : sourceCausalDomain n:=⟨1,sourceCausalDomain_one n unit⟩
  obtain ⟨d,hd⟩:=sourceCausalScale_nonempty n frequency
  exact ⟨1,by norm_num,d,hd.1,sourceCausalField_regular n frequency ⟨d,hd⟩⟩

theorem sourceCausalInverse_limit (n : PhysicalMomentum) (zeta : sourceCausalDomain n) :
    Tendsto (fun d : ℝ=>(sourceCausalNormalized n zeta.val d)⁻¹) (𝓝[>] 0)
      (𝓝 ((sourceCausalPrincipal n zeta.val)⁻¹)) := by
  have inverseAt : ContinuousAt Ring.inverse (sourceCausalPrincipal n zeta.val).det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ zeta.property.2
  exact (continuousAt_matrix_inv (sourceCausalPrincipal n zeta.val) inverseAt).tendsto.comp
    (sourceCausalNormalized_limit n zeta.val)

/-- The source read entering the complete five-dimensional equation. -/
def sourceCausalBalancedForcing (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (d : sourceCausalScale n zeta) (forcing : Fin 289→ℂ) : Fin 5→ℂ :=
  fun i=>(wideRayScaling d.val*ᵥ(slowFastFrame.transpose*ᵥ
    (effectiveReader (sourceCausalComplement n zeta d)*ᵥ
      activeForcing (sourceCausalComplement n zeta d).val forcing))) (fiveIndex i)

theorem sourceCausal_coordinates (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (d : sourceCausalScale n zeta) (forcing : Fin 289→ℂ) :
    blockCoordinates (dynamicActiveField (sourceCausalFieldPoint n zeta d) forcing)=
      modeCoordinates (sourceRealScale n zeta d) ((sourceCausalBalanced n zeta.val d.val)⁻¹*ᵥ
        sourceCausalBalancedForcing n zeta d forcing) := by
  let field:=dynamicActiveField (sourceCausalFieldPoint n zeta d) forcing
  let u:=blockCoordinates field
  have reduced:=effective_actual_equation (sourceCausalComplement n zeta d) field
    (activeForcing (sourceCausalComplement n zeta d).val forcing)
    (dynamicActiveField_inside (sourceCausalFieldPoint n zeta d) forcing)
    (dynamicActiveField_source (sourceCausalFieldPoint n zeta d) forcing)
  have normalized : sourceCausalBalanced n zeta.val d.val*ᵥunscaleCoordinates (sourceRealScale n zeta d) u=
      sourceCausalBalancedForcing n zeta d forcing := by
    rw [sourceCausalBalanced_response,modeCoordinates_unscale _ u (blockCoordinates_supported field)]
    exact congrArg (fun v : Fin 289→ℂ=>fun i=>(wideRayScaling d.val*ᵥ(slowFastFrame.transpose*ᵥv)) (fiveIndex i)) reduced
  have solved:=congrArg (fun v=>(sourceCausalBalanced n zeta.val d.val)⁻¹*ᵥv) normalized
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (sourceCausalBalanced_unit n zeta d)),Matrix.one_mulVec] at solved
  calc
    _=modeCoordinates (sourceRealScale n zeta d) (unscaleCoordinates (sourceRealScale n zeta d) u) :=
      (modeCoordinates_unscale _ u (blockCoordinates_supported field)).symm
    _=_ := congrArg (modeCoordinates (sourceRealScale n zeta d)) solved

/-- The original uncleared field retains the five modes, complete complement, and contact response. -/
theorem sourceCausalField_schur (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (d : sourceCausalScale n zeta) (forcing : Fin 289→ℂ) :
    sourceField (sourceCausalFieldPoint n zeta d) forcing=
      originalChange (sourceCausalComplement n zeta d).val*ᵥ
        (contactInverse (sourceCausalComplement n zeta d).val*ᵥ
          (originalReadback (sourceCausalComplement n zeta d).val*ᵥforcing))+
      originalChange (sourceCausalComplement n zeta d).val*ᵥ
        (effectiveFrame (sourceCausalComplement n zeta d)*ᵥ
          modeCoordinates (sourceRealScale n zeta d) ((sourceCausalBalanced n zeta.val d.val)⁻¹*ᵥ
            sourceCausalBalancedForcing n zeta d forcing))+
      originalChange (sourceCausalComplement n zeta d).val*ᵥ
        (complementGreen (sourceCausalComplement n zeta d)*ᵥ
          activeForcing (sourceCausalComplement n zeta d).val forcing) := by
  have returned:=effective_field_reconstruction (sourceCausalComplement n zeta d)
    (dynamicActiveField (sourceCausalFieldPoint n zeta d) forcing)
    (activeForcing (sourceCausalComplement n zeta d).val forcing)
    (dynamicActiveField_inside (sourceCausalFieldPoint n zeta d) forcing)
    (dynamicActiveField_source (sourceCausalFieldPoint n zeta d) forcing)
  rw [sourceCausal_coordinates] at returned
  have completed:=originalField_contact_active (sourceCausalFieldPoint n zeta d) forcing
  rw [returned,Matrix.mulVec_add] at completed
  exact completed.trans (add_assoc _ _ _).symm

end LowEnergy.PreparationVacuumFullSlowFieldResponse
