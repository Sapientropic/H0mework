import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceDynamicRegular

set_option autoImplicit false
set_option maxHeartbeats 50000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumNativePoleTensor
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumWholeOrigin
open PreparationVacuumFullOriginResponse PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumStaticPoleResponse CanonicalGradedSpatialSource
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] activeKernel originalChange originalReadback originalInverse contactInverse
  sourceField sourceGreen effectiveKernel effectiveFrame effectiveReader fullKernelFrame complementGreen
  PreparationVacuumPhysicalCharacteristic.normalizedEffective


/-- Generated original Green domain; no cleared denominator is used. -/
def dynamicPoint (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1)
    (regular : IsUnit (normalizedEffective e s n direction).det) : regularSource:=
  ⟨frequencyRay e.val s.val n,source_dynamic_regular e s n direction regular⟩

def dynamicActiveField (p : regularSource) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  activeProjection*ᵥ((extendedKernel p.val)⁻¹*ᵥ(originalReadback p.val*ᵥforcing))

def activeForcing (p : Fin 4→ℂ) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  activeProjection*ᵥ(originalReadback p*ᵥforcing)

attribute [local irreducible] dynamicActiveField

theorem dynamicActiveField_inside (p : regularSource) (forcing : Fin 289→ℂ) :
    activeProjection*ᵥdynamicActiveField p forcing=dynamicActiveField p forcing:=by
  rw [dynamicActiveField,Matrix.mulVec_mulVec,active_square]

theorem dynamicActiveField_source (p : regularSource) (forcing : Fin 289→ℂ) :
    activeKernel p.val*ᵥdynamicActiveField p forcing=activeForcing p.val forcing:=by
  unfold dynamicActiveField activeForcing
  rw [Matrix.mulVec_mulVec,activeKernel_right,Matrix.mulVec_mulVec,generated_active_inverse]

private theorem matrix_contact_split (S C A B R : Matrix (Fin 289) (Fin 289) ℂ) (v : Fin 289→ℂ) :
    (S*(C+A*B)*R)*ᵥv=S*ᵥ(C*ᵥ(R*ᵥv))+S*ᵥ(A*ᵥ(B*ᵥ(R*ᵥv))):=by
  rw [←Matrix.mulVec_mulVec v (S*(C+A*B)) R,
    ←Matrix.mulVec_mulVec (R*ᵥv) S (C+A*B),Matrix.add_mulVec,Matrix.mulVec_add,
    ←Matrix.mulVec_mulVec (R*ᵥv) A B]

/-- Original full field before any modal reduction. -/
theorem originalField_contact_active (p : regularSource) (forcing : Fin 289→ℂ) :
    sourceField p forcing=originalChange p.val*ᵥ(contactInverse p.val*ᵥ(originalReadback p.val*ᵥforcing))+
      originalChange p.val*ᵥdynamicActiveField p forcing:=by
  unfold sourceField sourceGreen dynamicActiveField
  exact matrix_contact_split _ _ _ _ _ _

def modeForcing (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum) (direction : ∀i,|n i|≤1)
    (forcing : Fin 289→ℂ) : Fin 5→ℂ:=
  fun i=>(wideRayScaling e.val*ᵥ(slowFastFrame.transpose*ᵥ(effectiveReader (rayPoint e s n direction)*ᵥ
    activeForcing (frequencyRay e.val s.val n) forcing))) (fiveIndex i)

private theorem matrix_solve (M : Matrix (Fin 5) (Fin 5) ℂ) (regular : IsUnit M.det)
    (u v : Fin 5→ℂ) (equation : M*ᵥu=v) : u=M⁻¹*ᵥv:=by
  have returned:=congrArg (fun w=>M⁻¹*ᵥw) equation
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul M regular,Matrix.one_mulVec] at returned
  exact returned

private theorem coordinates_from_equation (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (regular : IsUnit (normalizedEffective e s n direction).det)
    (field forcing : Fin 289→ℂ) (inside : activeProjection*ᵥfield=field)
    (equation : activeKernel (frequencyRay e.val s.val n)*ᵥfield=forcing) :
    blockCoordinates field=modeCoordinates e ((normalizedEffective e s n direction)⁻¹*ᵥ
      (fun i=>(wideRayScaling e.val*ᵥ(slowFastFrame.transpose*ᵥ(effectiveReader (rayPoint e s n direction)*ᵥforcing))) (fiveIndex i))):=by
  let u:=blockCoordinates field
  let read : (Fin 289→ℂ)→(Fin 5→ℂ):=fun v i=>(wideRayScaling e.val*ᵥ(slowFastFrame.transpose*ᵥv)) (fiveIndex i)
  have reduced : effectiveKernel (rayPoint e s n direction)*ᵥu=effectiveReader (rayPoint e s n direction)*ᵥforcing:=
    effective_actual_equation (rayPoint e s n direction) field forcing inside equation
  have normalized : normalizedEffective e s n direction*ᵥunscaleCoordinates e u=
      read (effectiveReader (rayPoint e s n direction)*ᵥforcing):=by
    calc
      _=read (effectiveKernel (rayPoint e s n direction)*ᵥmodeCoordinates e (unscaleCoordinates e u)):=
        normalized_response e s n direction (unscaleCoordinates e u)
      _=read (effectiveKernel (rayPoint e s n direction)*ᵥu):=
        congrArg (fun v=>read (effectiveKernel (rayPoint e s n direction)*ᵥv))
          (modeCoordinates_unscale e u (blockCoordinates_supported field))
      _=read (effectiveReader (rayPoint e s n direction)*ᵥforcing):=congrArg read reduced
  have returned:=matrix_solve (normalizedEffective e s n direction) regular _ _ normalized
  calc
    _=modeCoordinates e (unscaleCoordinates e u):=(modeCoordinates_unscale e u (blockCoordinates_supported field)).symm
    _= _ :=congrArg (modeCoordinates e) returned

theorem dynamic_coordinates_return (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (regular : IsUnit (normalizedEffective e s n direction).det) (forcing : Fin 289→ℂ) :
    blockCoordinates (dynamicActiveField (dynamicPoint e s n direction regular) forcing)=
      modeCoordinates e ((normalizedEffective e s n direction)⁻¹*ᵥmodeForcing e s n direction forcing):=by
  exact coordinates_from_equation e s n direction regular
    (dynamicActiveField (dynamicPoint e s n direction regular) forcing)
    (activeForcing (frequencyRay e.val s.val n) forcing)
    (dynamicActiveField_inside (dynamicPoint e s n direction regular) forcing)
    (dynamicActiveField_source (dynamicPoint e s n direction regular) forcing)

private theorem field_from_equation (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (regular : IsUnit (normalizedEffective e s n direction).det)
    (field forcing : Fin 289→ℂ) (inside : activeProjection*ᵥfield=field)
    (equation : activeKernel (frequencyRay e.val s.val n)*ᵥfield=forcing) :
    field=effectiveFrame (rayPoint e s n direction)*ᵥmodeCoordinates e ((normalizedEffective e s n direction)⁻¹*ᵥ
      (fun i=>(wideRayScaling e.val*ᵥ(slowFastFrame.transpose*ᵥ(effectiveReader (rayPoint e s n direction)*ᵥforcing))) (fiveIndex i)))+
      complementGreen (rayPoint e s n direction)*ᵥforcing:=by
  have reconstruction:=effective_field_reconstruction (rayPoint e s n direction) field forcing inside equation
  have coordinates:=coordinates_from_equation e s n direction regular field forcing inside equation
  rw [coordinates] at reconstruction
  exact reconstruction

/-- The original field is recovered from the entire effective inverse, complementary response and native contact term. -/
theorem originalField_dynamic_schur (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (regular : IsUnit (normalizedEffective e s n direction).det) (forcing : Fin 289→ℂ) :
    sourceField (dynamicPoint e s n direction regular) forcing=
      originalChange (frequencyRay e.val s.val n)*ᵥ(contactInverse (frequencyRay e.val s.val n)*ᵥ
        (originalReadback (frequencyRay e.val s.val n)*ᵥforcing))+
      nativeMode e s n direction ((normalizedEffective e s n direction)⁻¹*ᵥmodeForcing e s n direction forcing)+
      originalChange (frequencyRay e.val s.val n)*ᵥ(complementGreen (rayPoint e s n direction)*ᵥ
        activeForcing (frequencyRay e.val s.val n) forcing) :=by
  let p:=dynamicPoint e s n direction regular
  let S:=originalChange (frequencyRay e.val s.val n)
  let contact:=S*ᵥ(contactInverse (frequencyRay e.val s.val n)*ᵥ(originalReadback (frequencyRay e.val s.val n)*ᵥforcing))
  let v:=(normalizedEffective e s n direction)⁻¹*ᵥmodeForcing e s n direction forcing
  have returned : dynamicActiveField p forcing=effectiveFrame (rayPoint e s n direction)*ᵥmodeCoordinates e v+
      complementGreen (rayPoint e s n direction)*ᵥactiveForcing (frequencyRay e.val s.val n) forcing:=
    field_from_equation e s n direction regular (dynamicActiveField p forcing)
      (activeForcing (frequencyRay e.val s.val n) forcing)
      (dynamicActiveField_inside p forcing) (dynamicActiveField_source p forcing)
  have completed:=originalField_contact_active p forcing
  rw [returned,Matrix.mulVec_add] at completed
  calc
    _=contact+(nativeMode e s n direction v+
        S*ᵥ(complementGreen (rayPoint e s n direction)*ᵥactiveForcing (frequencyRay e.val s.val n) forcing)):=completed
    _= _ :=(add_assoc _ _ _).symm

/-- Total formulas retain the same source complementary inverse on its generated legal domain. -/
def rawEffectiveFrame (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  fullKernelFrame-unrestrictedGreen p*activeKernel p*fullKernelFrame

def rawEffectiveReader (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  fullKernelFrame.transpose-fullKernelFrame.transpose*activeKernel p*unrestrictedGreen p

def nativeInsertion (e s : ℝ) (n : PhysicalMomentum) (v : Fin 5→ℂ) : Fin 289→ℂ:=
  originalChange (frequencyRay e s n)*ᵥ(rawEffectiveFrame (frequencyRay e s n)*ᵥ
    (slowFastFrame*ᵥ(wideRayScaling e*ᵥfiveVector v)))

def nativeModeForcing (e s : ℝ) (n : PhysicalMomentum) (forcing : Fin 289→ℂ) : Fin 5→ℂ:=
  fun i=>(wideRayScaling e*ᵥ(slowFastFrame.transpose*ᵥ(rawEffectiveReader (frequencyRay e s n)*ᵥ
    activeForcing (frequencyRay e s n) forcing))) (fiveIndex i)

def nativeRegularResponse (e s : ℝ) (n : PhysicalMomentum) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  originalChange (frequencyRay e s n)*ᵥ(contactInverse (frequencyRay e s n)*ᵥ(originalReadback (frequencyRay e s n)*ᵥforcing))+
    originalChange (frequencyRay e s n)*ᵥ(unrestrictedGreen (frequencyRay e s n)*ᵥactiveForcing (frequencyRay e s n) forcing)

def nativeResponse (e s : ℝ) (n : PhysicalMomentum) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  nativeInsertion e s n ((extendedTensor e s n)⁻¹*ᵥnativeModeForcing e s n forcing)+nativeRegularResponse e s n forcing

attribute [local irreducible] nativeResponse nativeRegularResponse nativeInsertion nativeModeForcing rawEffectiveFrame rawEffectiveReader

theorem nativeResponse_original (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (regular : IsUnit (normalizedEffective e s n direction).det) (forcing : Fin 289→ℂ) :
    nativeResponse e.val s.val n forcing=sourceField (dynamicPoint e s n direction regular) forcing:=by
  apply Eq.trans ?_ (originalField_dynamic_schur e s n direction regular forcing).symm
  unfold nativeResponse nativeRegularResponse
  rw [extendedTensor_actual e s n direction]
  have insertion (v : Fin 5→ℂ) : nativeInsertion e.val s.val n v=nativeMode e s n direction v:=by
    unfold nativeInsertion nativeMode rawEffectiveFrame effectiveFrame modeCoordinates unrestrictedGreen complementGreen
      rayPoint PreparationVacuumFullOriginResponse.controlledPoint
    rfl
  have forcingRead : nativeModeForcing e.val s.val n forcing=modeForcing e s n direction forcing:=by
    unfold nativeModeForcing modeForcing rawEffectiveReader effectiveReader unrestrictedGreen complementGreen
      rayPoint PreparationVacuumFullOriginResponse.controlledPoint
    rfl
  rw [forcingRead,insertion]
  have green : unrestrictedGreen (frequencyRay e.val s.val n)=complementGreen (rayPoint e s n direction):=by
    unfold unrestrictedGreen complementGreen rayPoint PreparationVacuumFullOriginResponse.controlledPoint
    rfl
  rw [green]
  abel

theorem nativeResponse_whole (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (regular : IsUnit (normalizedEffective e s n direction).det) (forcing : Fin 289→ℂ) :
    originalJacobi (frequencyRay e.val s.val n)*ᵥnativeResponse e.val s.val n forcing=
      forcing-originalRowLift (frequencyRay e.val s.val n)*ᵥ
        (nullProjection*ᵥ(originalReadback (frequencyRay e.val s.val n)*ᵥforcing)):=by
  rw [nativeResponse_original e s n direction regular]
  exact original_forced_field (dynamicPoint e s n direction regular) forcing

attribute [local semireducible] originalChange originalReadback contactInverse activeKernel
  rawEffectiveFrame rawEffectiveReader nativeInsertion nativeModeForcing nativeRegularResponse

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

private theorem ray_continuous (e : ℝ) (n : PhysicalMomentum) : Continuous (fun s=>frequencyRay e s n):=by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · change Continuous (fun s : ℝ=> -Complex.I*((s*e^2:ℝ):ℂ))
    fun_prop
  · exact continuous_const

private theorem green_continuous_at (p : Fin 4→ℂ) (regular : p∈complementRegular) :
    ContinuousAt unrestrictedGreen p:=by
  have detInverse : ContinuousAt Ring.inverse (complementKernel p).det:=by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (isUnit_iff_ne_zero.mp regular)
  have inverse : ContinuousAt (fun p=> (complementKernel p)⁻¹) p:=
    (continuousAt_matrix_inv _ detInverse).tendsto.comp complementKernel_continuous.continuousAt.tendsto
  exact (continuousAt_const.mul inverse).mul continuousAt_const

private theorem frame_continuous_at (p : Fin 4→ℂ) (regular : p∈complementRegular) :
    ContinuousAt rawEffectiveFrame p:=
  continuousAt_const.sub (((green_continuous_at p regular).mul (sourceMatrix_continuous activeTerms).continuousAt).mul continuousAt_const)

private theorem reader_continuous_at (p : Fin 4→ℂ) (regular : p∈complementRegular) :
    ContinuousAt rawEffectiveReader p:=
  continuousAt_const.sub ((continuousAt_const.mul (sourceMatrix_continuous activeTerms).continuousAt).mul (green_continuous_at p regular))

private theorem mulVec_contAt {X : Type*} [TopologicalSpace X] {m n : ℕ}
    {M : X→Matrix (Fin m) (Fin n) ℂ} {v : X→Fin n→ℂ} {x : X}
    (matrix : ContinuousAt M x) (vector : ContinuousAt v x) : ContinuousAt (fun x=>M x*ᵥv x) x:=
by
  apply tendsto_pi_nhds.mpr
  intro i
  change Tendsto (fun y=>∑j : Fin n,M y i j*v y j) (𝓝 x) (𝓝 (∑j : Fin n,M x i j*v x j))
  apply tendsto_finsetSum
  intro j _
  exact ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp matrix i) j).mul (tendsto_pi_nhds.mp vector j))

private theorem fiveVector_continuous : Continuous (fiveVector : (Fin 5→ℂ)→Fin 289→ℂ):=by
  apply continuous_pi
  intro i
  unfold fiveVector
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem nativeInsertion_continuous_at (e s : ℝ) (n : PhysicalMomentum)
    (regular : frequencyRay e s n∈complementRegular) (v : Fin 5→ℂ) :
    ContinuousAt (fun x : ℝ×(Fin 5→ℂ)=>nativeInsertion e x.1 n x.2) (s,v):=by
  have point : Continuous (fun x : ℝ×(Fin 5→ℂ)=>frequencyRay e x.1 n):=(ray_continuous e n).comp continuous_fst
  have changeMatrix : ContinuousAt (fun x : ℝ×(Fin 5→ℂ)=>originalChange (frequencyRay e x.1 n)) (s,v):=
    ((sourceMatrix_continuous originalChangeTerms).comp point).continuousAt
  have frame : ContinuousAt (fun x : ℝ×(Fin 5→ℂ)=>rawEffectiveFrame (frequencyRay e x.1 n)) (s,v):=
    (frame_continuous_at _ regular).tendsto.comp point.continuousAt.tendsto
  exact mulVec_contAt changeMatrix (mulVec_contAt frame (mulVec_contAt continuousAt_const
    (mulVec_contAt continuousAt_const (fiveVector_continuous.comp continuous_snd).continuousAt)))

private theorem readback_continuous : Continuous originalReadback:=
  ((sourceMatrix_continuous originalChangeTerms).comp continuous_neg).matrix_transpose

private theorem activeForcing_continuous : Continuous (fun x : (Fin 4→ℂ)×(Fin 289→ℂ)=>activeForcing x.1 x.2):=
  continuous_const.matrix_mulVec ((readback_continuous.comp continuous_fst).matrix_mulVec continuous_snd)

theorem nativeModeForcing_continuous_at (e s : ℝ) (n : PhysicalMomentum)
    (regular : frequencyRay e s n∈complementRegular) (forcing : Fin 289→ℂ) :
    ContinuousAt (fun x : ℝ×(Fin 289→ℂ)=>nativeModeForcing e x.1 n x.2) (s,forcing):=by
  have point : Continuous (fun x : ℝ×(Fin 289→ℂ)=>frequencyRay e x.1 n):=(ray_continuous e n).comp continuous_fst
  have field : Continuous (fun x : ℝ×(Fin 289→ℂ)=>activeForcing (frequencyRay e x.1 n) x.2):=
    continuous_const.matrix_mulVec ((readback_continuous.comp point).matrix_mulVec continuous_snd)
  have reader : ContinuousAt (fun x : ℝ×(Fin 289→ℂ)=>rawEffectiveReader (frequencyRay e x.1 n)) (s,forcing):=
    (reader_continuous_at _ regular).tendsto.comp point.continuousAt.tendsto
  have all : ContinuousAt (fun x : ℝ×(Fin 289→ℂ)=>wideRayScaling e*ᵥ(slowFastFrame.transpose*ᵥ
      (rawEffectiveReader (frequencyRay e x.1 n)*ᵥactiveForcing (frequencyRay e x.1 n) x.2))) (s,forcing):=
    mulVec_contAt continuousAt_const (mulVec_contAt continuousAt_const (mulVec_contAt reader field.continuousAt))
  exact (continuous_pi (fun i=>continuous_apply (fiveIndex i))).continuousAt.tendsto.comp all.tendsto

theorem nativeRegularResponse_continuous_at (e s : ℝ) (n : PhysicalMomentum)
    (regular : frequencyRay e s n∈complementRegular) (forcing : Fin 289→ℂ) :
    ContinuousAt (fun x : ℝ×(Fin 289→ℂ)=>nativeRegularResponse e x.1 n x.2) (s,forcing):=by
  have point : Continuous (fun x : ℝ×(Fin 289→ℂ)=>frequencyRay e x.1 n):=(ray_continuous e n).comp continuous_fst
  have changeMatrix : Continuous (fun x : ℝ×(Fin 289→ℂ)=>originalChange (frequencyRay e x.1 n)):=
    (sourceMatrix_continuous originalChangeTerms).comp point
  have contact : Continuous (fun x : ℝ×(Fin 289→ℂ)=>contactInverse (frequencyRay e x.1 n)):=
    (sourceMatrix_continuous contactInverseTerms).comp point
  have readback : Continuous (fun x : ℝ×(Fin 289→ℂ)=>originalReadback (frequencyRay e x.1 n)):=readback_continuous.comp point
  have field : Continuous (fun x : ℝ×(Fin 289→ℂ)=>activeForcing (frequencyRay e x.1 n) x.2):=
    continuous_const.matrix_mulVec ((readback_continuous.comp point).matrix_mulVec continuous_snd)
  have green : ContinuousAt (fun x : ℝ×(Fin 289→ℂ)=>unrestrictedGreen (frequencyRay e x.1 n)) (s,forcing):=
    (green_continuous_at _ regular).tendsto.comp point.continuousAt.tendsto
  exact (changeMatrix.matrix_mulVec (contact.matrix_mulVec (readback.matrix_mulVec continuous_snd))).continuousAt.add
    (mulVec_contAt changeMatrix.continuousAt (mulVec_contAt green field.continuousAt))

theorem nativeInsertion_smul (e s : ℝ) (n : PhysicalMomentum) (c : ℂ) (v : Fin 5→ℂ) :
    nativeInsertion e s n (c • v)=c • nativeInsertion e s n v:=by
  have lift : fiveVector (c • v)=c • fiveVector v:=by
    funext i
    simp only [fiveVector,Pi.smul_apply]
    split_ifs <;> simp
  simp only [nativeInsertion,lift,Matrix.mulVec_smul]

theorem nativeInsertion_zero (e s : ℝ) (n : PhysicalMomentum) : nativeInsertion e s n 0=0:=by
  have empty : fiveVector (0:Fin 5→ℂ)=0:=by funext i;simp [fiveVector]
  simp only [nativeInsertion,empty,Matrix.mulVec_zero]

end LowEnergy.PreparationVacuumNativePoleTensor
