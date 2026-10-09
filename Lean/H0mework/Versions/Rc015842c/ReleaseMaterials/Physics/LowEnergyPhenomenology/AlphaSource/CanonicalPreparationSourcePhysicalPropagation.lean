import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSlowFastLeading

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalCharacteristic
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumWholeOrigin
open PreparationVacuumFullOriginResponse CanonicalGradedSpatialSource
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator

private theorem sourceMatrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms):=by
  induction terms with
  | nil=>exact continuous_const
  | cons a rest ih=>
    have term : Continuous a.matrix:=by
      apply continuous_matrix
      intro i j
      simp only [SourceTerm.matrix,Matrix.single_apply]
      split_ifs
      · unfold Powers.value;fun_prop
      · exact continuous_const
    exact term.add ih

private theorem effectiveKernel_continuous : Continuous (PreparationVacuumFullOriginResponse.effectiveKernel):=by
  have kernel : Continuous (fun p : PreparationVacuumFullOriginResponse.complementRegular=>activeKernel p.val):=
    (sourceMatrix_continuous activeTerms).comp continuous_subtype_val
  have inverse : Continuous (fun p : PreparationVacuumFullOriginResponse.complementRegular=>
      (PreparationVacuumFullOriginResponse.complementKernel p.val)⁻¹):=by
    apply continuous_iff_continuousAt.mpr
    intro p
    have detInverse : ContinuousAt Ring.inverse (PreparationVacuumFullOriginResponse.complementKernel p.val).det:=by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (isUnit_iff_ne_zero.mp p.property)
    exact (continuousAt_matrix_inv _ detInverse).tendsto.comp
      ((PreparationVacuumFullOriginResponse.complementKernel_continuous.comp continuous_subtype_val).continuousAt.tendsto)
  have green : Continuous (PreparationVacuumFullOriginResponse.complementGreen):=
    (continuous_const.mul inverse).mul continuous_const
  exact ((continuous_const.mul kernel).mul continuous_const).sub
    ((((continuous_const.mul kernel).mul green).mul kernel).mul continuous_const)

private theorem rayPoint_continuous (e : scaleDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    Continuous (fun s : slopeDomain=>rayPoint e s n direction):=by
  have point : Continuous (fun s : slopeDomain=>frequencyRay e.val s.val n):=by
    unfold frequencyRay physicalFrequencyMomentum
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · simp only [Fin.cases_zero]
      fun_prop
    · exact continuous_const
  exact point.subtype_mk (fun s=>(rayPoint e s n direction).property)

theorem normalizedEffective_continuous (e : scaleDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    Continuous (fun s : slopeDomain=>normalizedEffective e s n direction):=by
  have E:=effectiveKernel_continuous.comp (rayPoint_continuous e n direction)
  have whole : Continuous (fun s : slopeDomain=>wideRayScaling e.val*
      (slowFastFrame.transpose*rayEffective e s n direction*slowFastFrame)*wideRayScaling e.val):=
    (continuous_const.mul ((continuous_const.mul E).mul continuous_const)).mul continuous_const
  apply continuous_matrix
  intro i j
  exact (continuous_apply (fiveIndex j)).comp ((continuous_apply (fiveIndex i)).comp whole)

def actualCharacteristic (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) : ℝ:=
  (normalizedEffective e s n direction).det.re

theorem actualCharacteristic_continuous (e : scaleDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    Continuous (fun s : slopeDomain=>actualCharacteristic e s n direction):=
  Complex.continuous_re.comp (normalizedEffective_continuous e n direction).matrix_det

theorem actualCharacteristic_tendsto (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1) :
    Tendsto (fun e : scaleDomain=>actualCharacteristic e s n direction) scaleApproach (𝓝 (characteristicDeterminant s.val n)):=by
  have h:=Complex.continuous_re.continuousAt.tendsto.comp
    (continuous_id.matrix_det.continuousAt.tendsto.comp (normalizedEffective_tendsto s n direction))
  simpa only [Function.comp_def,id_eq,characteristic_det_real,Complex.ofReal_re,actualCharacteristic] using h

private theorem zero_between (f : slopeDomain→ℝ) (continuous : Continuous f) (a b : slopeDomain)
    (ordered : a.val<b.val) (left : f a<0) (right : 0<f b) :
    ∃s : slopeDomain,a.val<s.val ∧ s.val<b.val ∧ f s=0:=by
  let g : Icc a.val b.val→slopeDomain:=fun u=>⟨u.val,abs_le.mpr
    ⟨(abs_le.mp a.property).1.trans u.property.1,u.property.2.trans (abs_le.mp b.property).2⟩⟩
  have mapContinuous : Continuous g:=by fun_prop
  let start : Icc a.val b.val:=⟨a.val,le_rfl,ordered.le⟩
  let finish : Icc a.val b.val:=⟨b.val,ordered.le,le_rfl⟩
  have start_eq : g start=a:=Subtype.ext rfl
  have finish_eq : g finish=b:=Subtype.ext rfl
  let : PreconnectedSpace (Icc a.val b.val):=Subtype.preconnectedSpace isPreconnected_Icc
  have image:=(isPreconnected_univ : IsPreconnected (univ:Set (Icc a.val b.val))).intermediate_value
    (mem_univ start) (mem_univ finish) (continuous.comp mapContinuous).continuousOn
  have between : (0:ℝ)∈Icc ((f ∘ g) start) ((f ∘ g) finish):=by
    simpa only [Set.mem_Icc,Function.comp_def,start_eq,finish_eq] using And.intro left.le right.le
  obtain ⟨u,_inside,zero⟩:=image between
  change f (g u)=0 at zero
  have lower : a.val<u.val:=by
    rcases lt_or_eq_of_le u.property.1 with lt|same
    · exact lt
    · have same' : g u=a:=Subtype.ext same.symm
      rw [same'] at zero
      linarith
  have upper : u.val<b.val:=by
    rcases lt_or_eq_of_le u.property.2 with lt|same
    · exact lt
    · have same' : g u=b:=Subtype.ext same
      rw [same'] at zero
      linarith
  exact ⟨g u,lower,upper,zero⟩

theorem unit_direction_bound (n : PhysicalMomentum) (unit : spatialSquare n=1) : ∀i,|n i|≤1:=by
  unfold spatialSquare at unit
  have square (i : Fin 3) : (n i)^2≤1:=by
    fin_cases i
    · change (n 0)^2≤1
      nlinarith [sq_nonneg (n 1),sq_nonneg (n 2)]
    · change (n 1)^2≤1
      nlinarith [sq_nonneg (n 0),sq_nonneg (n 2)]
    · change (n 2)^2≤1
      nlinarith [sq_nonneg (n 0),sq_nonneg (n 1)]
  intro i
  apply abs_le.mpr
  constructor <;> nlinarith [square i,sq_nonneg (n i+1),sq_nonneg (n i-1)]

private def firstLow : slopeDomain:=⟨1/2,by norm_num [slopeDomain]⟩
private def firstHigh : slopeDomain:=⟨2/3,by norm_num [slopeDomain]⟩
private def secondLow : slopeDomain:=⟨4/5,by norm_num [slopeDomain]⟩
private def secondHigh : slopeDomain:=⟨9/10,by norm_num [slopeDomain]⟩

/-- Both branches are zeros of the complete original effective field tensor, for every sufficiently small nonzero source scale. -/
theorem physical_branches_eventually (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      (∃s : slopeDomain,(1/2:ℝ)<s.val ∧ s.val<(2/3:ℝ) ∧
        (normalizedEffective e s n (unit_direction_bound n unit)).det=0) ∧
      (∃s : slopeDomain,(4/5:ℝ)<s.val ∧ s.val<(9/10:ℝ) ∧
        (normalizedEffective e s n (unit_direction_bound n unit)).det=0):=by
  let direction:=unit_direction_bound n unit
  obtain ⟨h1,h2,h3,h4⟩:=characteristic_endpoint_signs n unit
  have left1:=(actualCharacteristic_tendsto firstLow n direction).eventually_lt_const h1
  have right1:=(actualCharacteristic_tendsto firstHigh n direction).eventually_const_lt h2
  have left2:=(actualCharacteristic_tendsto secondLow n direction).eventually_const_lt h3
  have right2:=(actualCharacteristic_tendsto secondHigh n direction).eventually_lt_const h4
  filter_upwards [left1,right1,left2,right2] with e le1 re1 le2 re2
  constructor
  · obtain ⟨s,low,high,zero⟩:=zero_between (fun s=>actualCharacteristic e s n direction)
      (actualCharacteristic_continuous e n direction) firstLow firstHigh (by norm_num [firstLow,firstHigh]) le1 re1
    refine ⟨s,low,high,?_⟩
    rw [normalizedEffective_det_real]
    change (actualCharacteristic e s n direction:ℂ)=0
    rw [zero,Complex.ofReal_zero]
  · obtain ⟨s,low,high,zero⟩:=zero_between (fun s=> -actualCharacteristic e s n direction)
      (actualCharacteristic_continuous e n direction).neg secondLow secondHigh (by norm_num [secondLow,secondHigh])
      (neg_neg_of_pos le2) (neg_pos.mpr re2)
    refine ⟨s,low,high,?_⟩
    have value : actualCharacteristic e s n direction=0:=neg_eq_zero.mp zero
    rw [normalizedEffective_det_real]
    change (actualCharacteristic e s n direction:ℂ)=0
    rw [value,Complex.ofReal_zero]

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

private theorem fiveVector_nonzero (v : Fin 5→ℂ) (nonzero : v≠0) : fiveVector v≠0:=by
  intro zero
  apply nonzero
  funext i
  have h:=congrFun zero (fiveIndex i)
  simpa only [fiveVector,fiveIndex,dif_pos i.isLt,Pi.zero_apply] using h

private theorem five_mulVec (M : Matrix (Fin 289) (Fin 289) ℂ) (v : Fin 5→ℂ) (i : Fin 5) :
    (M*ᵥfiveVector v) (fiveIndex i)=(M.submatrix fiveIndex fiveIndex*ᵥv) i:=by
  rw [fiveVector_expansion,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,Matrix.mulVec_single_one,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Matrix.mulVec,Matrix.submatrix_apply,dotProduct,Matrix.col_apply,mul_comm]

private theorem five_supported_zero (v : Fin 289→ℂ) (support : fiveProjection*ᵥv=v)
    (zero : ∀i : Fin 5,v (fiveIndex i)=0) : v=0:=by
  funext j
  have source:=congrFun support j
  rw [fiveProjection_diagonal,Matrix.mulVec_diagonal] at source
  by_cases inside : j.val<5
  · have h:=zero ⟨j.val,inside⟩
    have same : fiveIndex ⟨j.val,inside⟩=j:=Fin.ext rfl
    rw [same] at h
    exact h
  · simpa only [inside,if_false,zero_mul,Pi.zero_apply] using source.symm

private theorem scaling_supported (e : ℝ) : fiveProjection*wideRayScaling e=wideRayScaling e:=by
  rw [fiveProjection_diagonal,wideRayScaling,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp_all
  all_goals omega

private theorem frame_supported : fiveProjection*slowFastFrame=slowFastFrame ∧ slowFastFrame*fiveProjection=slowFastFrame:=by
  constructor
  · have h:=normalization_equal (productTerms fiveProjectionTerms slowFastFrameTerms) slowFastFrameTerms (by decide +kernel) (0:Fin 4→ℂ)
    simpa only [productTerms_value,fiveProjection,slowFastFrame] using h
  · have h:=normalization_equal (productTerms slowFastFrameTerms fiveProjectionTerms) slowFastFrameTerms (by decide +kernel) (0:Fin 4→ℂ)
    simpa only [productTerms_value,fiveProjection,slowFastFrame] using h

private def inverseRayScaling (e : ℝ) : Matrix (Fin 289) (Fin 289) ℂ:=
  Matrix.diagonal (fun i=>if i.val<3 then (e:ℂ)^2 else if i.val<5 then (e:ℂ) else 0)

private theorem scaling_inverse (e : scaleDomain) : inverseRayScaling e.val*wideRayScaling e.val=fiveProjection:=by
  have nonzero : (e.val:ℂ)≠0:=Complex.ofReal_ne_zero.mpr e.property.1.ne'
  rw [inverseRayScaling,wideRayScaling,fiveProjection_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp_all
  all_goals omega

private theorem effective_left_five (p : PreparationVacuumFullOriginResponse.complementRegular) :
    fiveProjection*PreparationVacuumFullOriginResponse.effectiveKernel p=PreparationVacuumFullOriginResponse.effectiveKernel p:=by
  have symmetric : fiveProjection.transpose=fiveProjection:=by rw [fiveProjection_diagonal,Matrix.diagonal_transpose]
  have source:=congrArg Matrix.transpose PreparationVacuumStaticPoleResponse.fullKernel_five
  rw [Matrix.transpose_mul,symmetric] at source
  unfold PreparationVacuumFullOriginResponse.effectiveKernel
  simp only [mul_sub,←mul_assoc,source]

private theorem normalized_wide_kernel (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (v : Fin 5→ℂ) (kernel : normalizedEffective e s n direction*ᵥv=0) :
    (wideRayScaling e.val*(slowFastFrame.transpose*rayEffective e s n direction*slowFastFrame)*wideRayScaling e.val)*ᵥfiveVector v=0:=by
  apply five_supported_zero
  · simp only [Matrix.mulVec_mulVec,←mul_assoc,scaling_supported]
  · intro i
    rw [five_mulVec]
    exact congrFun kernel i

/-- Coordinates arise from an actual kernel vector of the complete normalized source tensor. -/
def modeCoordinates (e : scaleDomain) (v : Fin 5→ℂ) : Fin 289→ℂ:=
  slowFastFrame*ᵥ(wideRayScaling e.val*ᵥfiveVector v)

private theorem modeCoordinates_supported (e : scaleDomain) (v : Fin 5→ℂ) :
    fiveProjection*ᵥmodeCoordinates e v=modeCoordinates e v:=by
  unfold modeCoordinates
  rw [Matrix.mulVec_mulVec,frame_supported.1]

private theorem modeCoordinates_nonzero (e : scaleDomain) (v : Fin 5→ℂ) (nonzero : v≠0) : modeCoordinates e v≠0:=by
  intro zero
  have h:=congrArg (fun x : Fin 289→ℂ=>inverseRayScaling e.val*ᵥ(slowFastInverse*ᵥx)) zero
  simp only [modeCoordinates,Matrix.mulVec_mulVec,←mul_assoc,slowFastFrame_inverse] at h
  have project : inverseRayScaling e.val*fiveProjection*wideRayScaling e.val=fiveProjection:=by
    rw [mul_assoc,scaling_supported,scaling_inverse]
  simp only [mul_assoc] at h
  have h': fiveVector v=0:=by
    simpa only [←mul_assoc,project,fiveProjection_vector,Matrix.mulVec_zero] using h
  exact fiveVector_nonzero v nonzero h'

private theorem modeCoordinates_kernel (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (v : Fin 5→ℂ) (kernel : normalizedEffective e s n direction*ᵥv=0) :
    rayEffective e s n direction*ᵥmodeCoordinates e v=0:=by
  have source:=normalized_wide_kernel e s n direction v kernel
  have returned:=congrArg (fun x : Fin 289→ℂ=>slowFastInverse.transpose*ᵥ(inverseRayScaling e.val*ᵥx)) source
  have frame : slowFastInverse.transpose*fiveProjection*slowFastFrame.transpose=fiveProjection:=by
    have support:=congrArg Matrix.transpose frame_supported.2
    have symmetric : fiveProjection.transpose=fiveProjection:=by rw [fiveProjection_diagonal,Matrix.diagonal_transpose]
    rw [Matrix.transpose_mul,symmetric] at support
    rw [mul_assoc,support,←Matrix.transpose_mul,slowFastFrame_inverse_right,symmetric]
  have E :=effective_left_five (rayPoint e s n direction)
  change fiveProjection*rayEffective e s n direction=rayEffective e s n direction at E
  simp only [Matrix.mulVec_mulVec] at returned
  have algebra : slowFastInverse.transpose*inverseRayScaling e.val*
      (wideRayScaling e.val*(slowFastFrame.transpose*rayEffective e s n direction*slowFastFrame)*wideRayScaling e.val)=
      rayEffective e s n direction*slowFastFrame*wideRayScaling e.val:=by
    calc
      _=(slowFastInverse.transpose*(inverseRayScaling e.val*wideRayScaling e.val)*slowFastFrame.transpose)*
          rayEffective e s n direction*slowFastFrame*wideRayScaling e.val:=by noncomm_ring
      _= _:=by rw [scaling_inverse,frame,E]
  simp only [mul_assoc] at algebra returned
  rw [algebra] at returned
  simpa only [Matrix.mulVec_zero,modeCoordinates,Matrix.mulVec_mulVec,mul_assoc] using returned

private theorem selector_complement_zero : modeSelector*fullComplementProjection=0:=by
  have h:=normalization_equal (productTerms selectorTerms (projectionTerms fullComplementFlag)) [] (by decide +kernel) (0:Fin 4→ℂ)
  simpa only [productTerms_value,projectionTerms_value,modeSelector,fullComplementProjection,sourceMatrix_nil] using h

private theorem missing_recovery : modeSelector.transpose*fullKernelFrame.transpose*(activeProjection-fullComplementProjection)=
    activeProjection-fullComplementProjection:=by
  have h:=normalization_equal
    (productTerms (productTerms (reflectedTerms selectorTerms) (reflectedTerms fullKernelTerms))
      (projectionTerms activeFlag++negativeTerms (projectionTerms fullComplementFlag)))
    (projectionTerms activeFlag++negativeTerms (projectionTerms fullComplementFlag)) (by decide +kernel) (0:Fin 4→ℂ)
  simpa only [productTerms_value,reflectedTerms_value,neg_zero,fullKernel_generated,sourceMatrix_append,
    negativeTerms_value,projectionTerms_value,modeSelector,activeProjection,fullComplementProjection,sub_eq_add_neg] using h

private theorem active_complement : activeProjection*fullComplementProjection=fullComplementProjection:=by
  unfold activeProjection fullComplementProjection projectionMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  cases flag : activeFlag i <;> simp [fullComplementFlag,flag]

private theorem effectiveFrame_active (p : PreparationVacuumFullOriginResponse.complementRegular) :
    activeProjection*effectiveFrame p=effectiveFrame p:=by
  have green : activeProjection*complementGreen p=complementGreen p:=by
    calc
      _=activeProjection*(fullComplementProjection*complementGreen p):=by rw [complementGreen_left_support]
      _= _:=by rw [←mul_assoc,active_complement,complementGreen_left_support]
  unfold effectiveFrame
  simp only [mul_sub,←mul_assoc,PreparationVacuumStaticPoleResponse.fullKernel_active,green]

private theorem effectiveFrame_coordinates (p : PreparationVacuumFullOriginResponse.complementRegular) :
    modeSelector*effectiveFrame p=fiveProjection:=by
  have green : modeSelector*complementGreen p=0:=by
    calc
      _=modeSelector*(fullComplementProjection*complementGreen p):=by rw [complementGreen_left_support]
      _=0:=by rw [←mul_assoc,selector_complement_zero,zero_mul]
  unfold effectiveFrame
  simp only [mul_sub,←mul_assoc,fullKernel_coordinates,green,zero_mul,sub_zero]

private theorem effectiveFrame_kernel (p : PreparationVacuumFullOriginResponse.complementRegular) (u : Fin 289→ℂ)
    (kernel : effectiveKernel p*ᵥu=0) : activeKernel p.val*ᵥ(effectiveFrame p*ᵥu)=0:=by
  let residual:=activeKernel p.val*ᵥ(effectiveFrame p*ᵥu)
  have inside : activeProjection*ᵥresidual=residual:=by
    simp only [residual,Matrix.mulVec_mulVec,←mul_assoc,original_active_support]
  have complement : fullComplementProjection*activeKernel p.val*effectiveFrame p=0:=by
    unfold effectiveFrame
    simp only [mul_sub,←mul_assoc,complementGreen_right,sub_self]
  have compZero : fullComplementProjection*ᵥresidual=0:=by
    simp only [residual,Matrix.mulVec_mulVec,←mul_assoc,complement,Matrix.zero_mulVec]
  have kernelRead : fullKernelFrame.transpose*ᵥresidual=0:=by
    calc
      _=(fullKernelFrame.transpose*activeKernel p.val*effectiveFrame p)*ᵥu:=by
        simp only [residual,Matrix.mulVec_mulVec,mul_assoc]
      _=effectiveKernel p*ᵥu:=by rw [effectiveKernel_frame]
      _=0:=kernel
  have missing : (activeProjection-fullComplementProjection)*ᵥresidual=residual:=by
    rw [Matrix.sub_mulVec,inside,compZero,sub_zero]
  calc
    residual=(activeProjection-fullComplementProjection)*ᵥresidual:=missing.symm
    _=modeSelector.transpose*ᵥ(fullKernelFrame.transpose*ᵥ((activeProjection-fullComplementProjection)*ᵥresidual)):=by
      simpa only [Matrix.mulVec_mulVec,mul_assoc] using
        (congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>M*ᵥresidual) missing_recovery).symm
    _=0:=by rw [missing,kernelRead,Matrix.mulVec_zero]

/-- The propagated source mode retains its full native 289 components. -/
def nativeMode (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1)
    (v : Fin 5→ℂ) : Fin 289→ℂ:=
  originalChange (frequencyRay e.val s.val n)*ᵥ(effectiveFrame (rayPoint e s n direction)*ᵥmodeCoordinates e v)

theorem nativeMode_nonzero (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1)
    (v : Fin 5→ℂ) (nonzero : v≠0) : nativeMode e s n direction v≠0:=by
  have canonical : effectiveFrame (rayPoint e s n direction)*ᵥmodeCoordinates e v≠0:=by
    intro zero
    have h:=congrArg (fun x : Fin 289→ℂ=>modeSelector*ᵥx) zero
    simp only [Matrix.mulVec_mulVec,effectiveFrame_coordinates,modeCoordinates_supported,Matrix.mulVec_zero] at h
    exact modeCoordinates_nonzero e v nonzero h
  intro zero
  have h:=congrArg (fun x : Fin 289→ℂ=>originalInverse (frequencyRay e.val s.val n)*ᵥx) zero
  simp only [nativeMode,Matrix.mulVec_mulVec,←mul_assoc,original_inverse_change,one_mul,Matrix.mulVec_zero] at h
  exact canonical h

theorem nativeMode_whole_equation (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1)
    (v : Fin 5→ℂ) (kernel : normalizedEffective e s n direction*ᵥv=0) :
    originalJacobi (frequencyRay e.val s.val n)*ᵥnativeMode e s n direction v=0:=by
  let p:=rayPoint e s n direction
  let u:=modeCoordinates e v
  let field:=effectiveFrame p*ᵥu
  have inside : activeProjection*ᵥfield=field:=by
    simp only [field,Matrix.mulVec_mulVec,effectiveFrame_active]
  have zero : activeKernel p.val*ᵥfield=0:=effectiveFrame_kernel p u (modeCoordinates_kernel e s n direction v kernel)
  change originalJacobi p.val*ᵥ(originalChange p.val*ᵥfield)=0
  calc
    _=originalJacobi p.val*ᵥ(originalChange p.val*ᵥ(activeProjection*ᵥfield)):=by rw [inside]
    _=(originalJacobi p.val*originalChange p.val*activeProjection)*ᵥfield:=by simp only [Matrix.mulVec_mulVec,mul_assoc]
    _=(originalRowLift p.val*activeKernel p.val)*ᵥfield:=by rw [original_active_intertwiner]
    _=0:=by rw [←Matrix.mulVec_mulVec,zero,Matrix.mulVec_zero]

theorem source_mode_of_characteristic (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1)
    (zero : (normalizedEffective e s n direction).det=0) :
    ∃v : Fin 5→ℂ,v≠0 ∧ nativeMode e s n direction v≠0 ∧
      originalJacobi (frequencyRay e.val s.val n)*ᵥnativeMode e s n direction v=0:=by
  obtain ⟨v,nonzero,kernel⟩:=(Matrix.exists_mulVec_eq_zero_iff (M:=normalizedEffective e s n direction)).mpr zero
  exact ⟨v,nonzero,nativeMode_nonzero e s n direction v nonzero,nativeMode_whole_equation e s n direction v kernel⟩

open SourcePropagationNativeActionHessian

/-- The two real-frequency branches generate nonzero solutions of the complete original action Hessian. -/
theorem source_physical_propagation (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      (∃s : slopeDomain,∃v : Fin 5→ℂ,(1/2:ℝ)<s.val ∧ s.val<(2/3:ℝ) ∧
        nativeMode e s n (unit_direction_bound n unit) v≠0 ∧
        nativeFourierHessian nativeHessian (frequencyRay e.val s.val n)*ᵥ
          nativeMode e s n (unit_direction_bound n unit) v=0) ∧
      (∃s : slopeDomain,∃v : Fin 5→ℂ,(4/5:ℝ)<s.val ∧ s.val<(9/10:ℝ) ∧
        nativeMode e s n (unit_direction_bound n unit) v≠0 ∧
        nativeFourierHessian nativeHessian (frequencyRay e.val s.val n)*ᵥ
          nativeMode e s n (unit_direction_bound n unit) v=0):=by
  filter_upwards [physical_branches_eventually n unit] with e branches
  constructor
  · obtain ⟨s,low,high,zero⟩:=branches.1
    obtain ⟨v,_,nonzero,equation⟩:=source_mode_of_characteristic e s n (unit_direction_bound n unit) zero
    exact ⟨s,v,low,high,nonzero,by simpa only [nativeActionFourierHessian_original] using equation⟩
  · obtain ⟨s,low,high,zero⟩:=branches.2
    obtain ⟨v,_,nonzero,equation⟩:=source_mode_of_characteristic e s n (unit_direction_bound n unit) zero
    exact ⟨s,v,low,high,nonzero,by simpa only [nativeActionFourierHessian_original] using equation⟩

/-- A genuine nonzero physical frequency and spatial momentum occur on each generated branch. -/
theorem source_physical_propagation_nonempty (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∃e : scaleDomain,∃s₁ s₂ : slopeDomain,∃v₁ v₂ : Fin 5→ℂ,
      (1/2:ℝ)<s₁.val ∧ s₁.val<(2/3:ℝ) ∧ (4/5:ℝ)<s₂.val ∧ s₂.val<(9/10:ℝ) ∧
      nativeMode e s₁ n (unit_direction_bound n unit) v₁≠0 ∧
      nativeMode e s₂ n (unit_direction_bound n unit) v₂≠0 ∧
      nativeFourierHessian nativeHessian (frequencyRay e.val s₁.val n)*ᵥ
        nativeMode e s₁ n (unit_direction_bound n unit) v₁=0 ∧
      nativeFourierHessian nativeHessian (frequencyRay e.val s₂.val n)*ᵥ
        nativeMode e s₂ n (unit_direction_bound n unit) v₂=0:=by
  let : scaleApproach.NeBot:=scaleApproach_nonempty
  obtain ⟨e,⟨s₁,v₁,low₁,high₁,nonzero₁,equation₁⟩,⟨s₂,v₂,low₂,high₂,nonzero₂,equation₂⟩⟩:=
    (source_physical_propagation n unit).exists
  exact ⟨e,s₁,s₂,v₁,v₂,low₁,high₁,low₂,high₂,nonzero₁,nonzero₂,equation₁,equation₂⟩

end LowEnergy.PreparationVacuumPhysicalCharacteristic
