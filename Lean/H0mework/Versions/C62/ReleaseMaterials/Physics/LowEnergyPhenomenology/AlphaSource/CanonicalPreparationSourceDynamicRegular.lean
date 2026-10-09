import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSimplePhysicalSheet

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNativePoleTensor
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumWholeOrigin
open PreparationVacuumFullOriginResponse PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumStaticPoleResponse CanonicalGradedSpatialSource
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator

private theorem fiveProjection_diagonal : fiveProjection=Matrix.diagonal (fun i : Fin 289=>if i.val<5 then (1:ℂ) else 0):=by
  have h:=normalization_equal fiveProjectionTerms (projectionTerms (fun i=>decide (i.val<5))) (by decide +kernel) (0:Fin 4→ℂ)
  simpa only [fiveProjection,projectionTerms_value,projectionMatrix,decide_eq_true_eq] using h

private theorem fiveVector_expansion (v : Fin 5→ℂ) :
    fiveVector v=∑i : Fin 5,v i • Pi.single (fiveIndex i) (1:ℂ):=by
  funext j
  by_cases inside : j.val<5
  · let i : Fin 5:=⟨j.val,inside⟩
    have same : j=fiveIndex i:=Fin.ext rfl
    simp only [fiveVector,dif_pos inside,Finset.sum_apply,Pi.smul_apply]
    rw [Finset.sum_eq_single i]
    · change v i=v i • ((Pi.single (fiveIndex i) (1:ℂ) : Fin 289→ℂ) j)
      simp only [Pi.single_apply,if_pos same,smul_eq_mul,mul_one]
    · intro k _ different
      have off : j≠fiveIndex k:=by
        intro eq
        apply different
        exact Fin.ext (congrArg Fin.val eq).symm
      simp [off]
    · intro absent
      exact False.elim (absent (Finset.mem_univ i))
  · have outside (i : Fin 5) : j≠fiveIndex i:=by
      intro same
      have equal:=congrArg Fin.val same
      change j.val=i.val at equal
      omega
    simp [fiveVector,inside,Finset.sum_apply,Pi.smul_apply,outside]


private theorem five_mulVec (M : Matrix (Fin 289) (Fin 289) ℂ) (v : Fin 5→ℂ) (i : Fin 5) :
    (M*ᵥfiveVector v) (fiveIndex i)=(M.submatrix fiveIndex fiveIndex*ᵥv) i:=by
  rw [fiveVector_expansion,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,Matrix.mulVec_single_one,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Matrix.mulVec,Matrix.submatrix_apply,dotProduct,Matrix.col_apply,mul_comm]


private theorem frame_supported : fiveProjection*slowFastFrame=slowFastFrame ∧ slowFastFrame*fiveProjection=slowFastFrame:=by
  constructor
  · have h:=normalization_equal (productTerms fiveProjectionTerms slowFastFrameTerms) slowFastFrameTerms (by decide +kernel) (0:Fin 4→ℂ)
    simpa only [productTerms_value,fiveProjection,slowFastFrame] using h
  · have h:=normalization_equal (productTerms slowFastFrameTerms fiveProjectionTerms) slowFastFrameTerms (by decide +kernel) (0:Fin 4→ℂ)
    simpa only [productTerms_value,fiveProjection,slowFastFrame] using h

/-- Source inverse scale restores the actual five coordinates before their native field lift. -/
def inverseScale (e : ℝ) : Matrix (Fin 289) (Fin 289) ℂ:=
  Matrix.diagonal (fun i=>if i.val<3 then (e:ℂ)^2 else if i.val<5 then (e:ℂ) else 0)

private theorem inverseScale_supported (e : ℝ) : fiveProjection*inverseScale e=inverseScale e:=by
  rw [fiveProjection_diagonal,inverseScale,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp_all
  all_goals omega

private theorem scale_inverse (e : scaleDomain) : wideRayScaling e.val*inverseScale e.val=fiveProjection:=by
  have nonzero : (e.val:ℂ)≠0:=Complex.ofReal_ne_zero.mpr e.property.1.ne'
  rw [inverseScale,wideRayScaling,fiveProjection_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp_all
  all_goals omega

private theorem fiveVector_restore (u : Fin 289→ℂ) (support : fiveProjection*ᵥu=u) :
    fiveVector (fun i=>u (fiveIndex i))=u:=by
  funext j
  by_cases inside : j.val<5
  · have same : fiveIndex ⟨j.val,inside⟩=j:=Fin.ext rfl
    simp only [fiveVector,dif_pos inside,same]
  · have h:=congrFun support j
    rw [fiveProjection_diagonal,Matrix.mulVec_diagonal] at h
    simpa only [fiveVector,dif_neg inside,if_neg inside,zero_mul] using h

def unscaleCoordinates (e : scaleDomain) (u : Fin 289→ℂ) : Fin 5→ℂ:=
  fun i=>(inverseScale e.val*ᵥ(slowFastInverse*ᵥu)) (fiveIndex i)

theorem modeCoordinates_unscale (e : scaleDomain) (u : Fin 289→ℂ) (support : fiveProjection*ᵥu=u) :
    modeCoordinates e (unscaleCoordinates e u)=u:=by
  have inside : fiveProjection*ᵥ(inverseScale e.val*ᵥ(slowFastInverse*ᵥu))=
      inverseScale e.val*ᵥ(slowFastInverse*ᵥu):=by
    rw [Matrix.mulVec_mulVec,inverseScale_supported]
  unfold modeCoordinates unscaleCoordinates
  rw [fiveVector_restore _ inside]
  simp only [Matrix.mulVec_mulVec,←mul_assoc,scale_inverse,frame_supported.2,slowFastFrame_inverse_right,support]

theorem normalized_response (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (v : Fin 5→ℂ) :
    normalizedEffective e s n direction*ᵥv=
      (fun i=>(wideRayScaling e.val*ᵥ(slowFastFrame.transpose*ᵥ
        (effectiveKernel (rayPoint e s n direction)*ᵥmodeCoordinates e v))) (fiveIndex i)):=by
  funext i
  unfold PreparationVacuumPhysicalCharacteristic.normalizedEffective
  rw [←five_mulVec]
  simp only [modeCoordinates,Matrix.mulVec_mulVec,mul_assoc]
  rfl

theorem source_effective_injective (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (regular : IsUnit (normalizedEffective e s n direction).det)
    (u : Fin 289→ℂ) (support : fiveProjection*ᵥu=u)
    (kernel : effectiveKernel (rayPoint e s n direction)*ᵥu=0) : u=0:=by
  have reduced : normalizedEffective e s n direction*ᵥunscaleCoordinates e u=0:=by
    rw [normalized_response,modeCoordinates_unscale e u support,kernel,Matrix.mulVec_zero,Matrix.mulVec_zero]
    rfl
  have zero : unscaleCoordinates e u=0:=by
    apply Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr regular)
    simpa only [Matrix.mulVec_zero] using reduced
  rw [←modeCoordinates_unscale e u support,zero]
  have empty : fiveVector (0:Fin 5→ℂ)=0:=by
    funext i
    simp [fiveVector]
  simp only [modeCoordinates,empty,Matrix.mulVec_zero]

theorem source_dynamic_kernel_zero (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (regular : IsUnit (normalizedEffective e s n direction).det)
    (field : Fin 289→ℂ) (inside : activeProjection*ᵥfield=field)
    (kernel : activeKernel (frequencyRay e.val s.val n)*ᵥfield=0) : field=0:=by
  have reduced:=effective_actual_equation (rayPoint e s n direction) field 0 inside kernel
  rw [Matrix.mulVec_zero] at reduced
  have coordinates : blockCoordinates field=0:=source_effective_injective e s n direction regular _
    (blockCoordinates_supported field) reduced
  have returned:=effective_field_reconstruction (rayPoint e s n direction) field 0 inside kernel
  simpa only [coordinates,Matrix.mulVec_zero,add_zero] using returned

theorem source_dynamic_regular (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (regular : IsUnit (normalizedEffective e s n direction).det) :
    frequencyRay e.val s.val n∈regularSource:=by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro left right same
  have kernel : extendedKernel (frequencyRay e.val s.val n)*ᵥ(left-right)=0:=by
    rw [Matrix.mulVec_sub,same,sub_self]
  let field:=left-right
  have projected:=congrArg (fun v=>activeProjection*ᵥv) kernel
  rw [Matrix.mulVec_mulVec,original_active_extended,Matrix.mulVec_zero] at projected
  have inside : activeProjection*ᵥ(activeProjection*ᵥfield)=activeProjection*ᵥfield:=by
    rw [Matrix.mulVec_mulVec,active_square]
  have zero : activeProjection*ᵥfield=0:=by
    apply source_dynamic_kernel_zero e s n direction regular _ inside
    rw [Matrix.mulVec_mulVec,activeKernel_right]
    exact projected
  change extendedKernel (frequencyRay e.val s.val n)*ᵥfield=0 at kernel
  rw [extendedKernel,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,projected,zero,sub_zero,zero_add] at kernel
  exact sub_eq_zero.mp kernel

/-- A punctured neighborhood of each actual source sheet is a legal domain for the original uncleared Green. -/
theorem sourceSheet_regular_near (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀ᶠ t in 𝓝[≠] (sourceSheet branch n unit e.val),
      ∃s : slopeDomain,s.val=t ∧ frequencyRay e.val t n∈regularSource:=by
  filter_upwards [scaleVal_tendsto.eventually (sourceSheet_simple branch n unit),
    scaleVal_tendsto.eventually (sourceSheet_equation branch n unit),
    scaleVal_tendsto.eventually (sourceSheet_bounds branch n unit)] with e simple equation bounds
  let center:=sourceSheet branch n unit e.val
  have inside : |center|<1:=by
    apply abs_lt.mpr
    change (if branch=0 then (1/2:ℝ) else (4/5:ℝ))<center ∧ center<(if branch=0 then (2/3:ℝ) else (9/10:ℝ)) at bounds
    split_ifs at bounds <;> constructor <;> linarith
  have slopes:=simple.2.tendsto_slope.eventually_ne simple.1
  have interval := ((continuous_abs.continuousAt : ContinuousAt (fun t : ℝ=>|t|) center).eventually_lt_const inside).filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] center≤𝓝 center)
  filter_upwards [slopes,interval] with t slope insideT
  have realNonzero : physicalDeterminant e.val t n≠0:=by
    intro zero
    apply slope
    simp only [slope_def_module,zero,equation,sub_self,smul_zero]
  let s : slopeDomain:=⟨t,insideT.le⟩
  refine ⟨s,rfl,source_dynamic_regular e s n (unit_direction_bound n unit) ?_⟩
  apply isUnit_iff_ne_zero.mpr
  intro zero
  have same:=extendedTensor_actual e s n (unit_direction_bound n unit)
  rw [←same] at zero
  apply realNonzero
  exact congrArg Complex.re zero

theorem sourceSheet_regular_nonempty (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∃e : scaleDomain,∃s : slopeDomain,frequencyRay e.val s.val n∈regularSource:=by
  let : scaleApproach.NeBot:=scaleApproach_nonempty
  obtain ⟨e,near⟩:=(sourceSheet_regular_near branch n unit).exists
  obtain ⟨t,s,equal,regular⟩:=near.exists
  exact ⟨e,s,by simpa only [equal] using regular⟩

end LowEnergy.PreparationVacuumNativePoleTensor
