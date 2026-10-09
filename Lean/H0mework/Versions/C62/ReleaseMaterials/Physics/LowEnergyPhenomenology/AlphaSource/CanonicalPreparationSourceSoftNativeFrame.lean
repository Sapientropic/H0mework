import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSoftResidueKernel

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumSoftPoleSelection
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse PreparationVacuumMixedPrincipal
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumNativePoleTensor
open PreparationVacuumWholeOrigin PreparationVacuumStaticPoleResponse CanonicalGradedSpatialSource Filter Set
open scoped Matrix BigOperators Topology

/-- The source degree scaling has no inverse epsilon in this native insertion. -/
def softInsertion (epsilon s : ℝ) (n : PhysicalMomentum) (v : Fin 5→ℂ) : Fin 289→ℂ:=
  originalChange (frequencyRay epsilon s n)*ᵥ(rawEffectiveFrame (frequencyRay epsilon s n)*ᵥ
    (slowFastFrame*ᵥfiveVector (regularScaling epsilon*ᵥv)))

def softForcing (epsilon s : ℝ) (n : PhysicalMomentum) (forcing : Fin 289→ℂ) : Fin 5→ℂ:=
  regularScaling epsilon*ᵥ(fun i=>(slowFastFrame.transpose*ᵥ(rawEffectiveReader (frequencyRay epsilon s n)*ᵥ
    activeForcing (frequencyRay epsilon s n) forcing)) (fiveIndex i))

def softResponse (epsilon s : ℝ) (n : PhysicalMomentum) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  softInsertion epsilon s n (((2*(s:ℂ)) • sourceResidue epsilon s n)*ᵥsoftForcing epsilon s n forcing)

private theorem lifted_scale (epsilon : ℝ) (nonzero : epsilon≠0) (v : Fin 5→ℂ) :
    (epsilon:ℂ)^2 • (wideRayScaling epsilon*ᵥfiveVector v)=fiveVector (regularScaling epsilon*ᵥv):=by
  have ne : (epsilon:ℂ)≠0:=Complex.ofReal_ne_zero.mpr nonzero
  funext i
  simp only [Pi.smul_apply,wideRayScaling,regularScaling,Matrix.mulVec_diagonal,smul_eq_mul]
  by_cases inside : i.val<5
  · simp only [fiveVector,dif_pos inside,if_pos inside,Matrix.mulVec_diagonal]
    split_ifs <;> field_simp
  · simp [fiveVector,inside]

private theorem read_scale (epsilon : ℝ) (nonzero : epsilon≠0) (v : Fin 289→ℂ) :
    (epsilon:ℂ)^2 • (fun i : Fin 5=>(wideRayScaling epsilon*ᵥv) (fiveIndex i))=
      regularScaling epsilon*ᵥ(fun i=>v (fiveIndex i)):=by
  have ne : (epsilon:ℂ)≠0:=Complex.ofReal_ne_zero.mpr nonzero
  funext i
  simp only [Pi.smul_apply,wideRayScaling,regularScaling,Matrix.mulVec_diagonal,smul_eq_mul,fiveIndex,i.isLt,if_true]
  split_ifs <;> field_simp

theorem softInsertion_generated (epsilon s : ℝ) (n : PhysicalMomentum) (nonzero : epsilon≠0) (v : Fin 5→ℂ) :
    (epsilon:ℂ)^2 • nativeInsertion epsilon s n v=softInsertion epsilon s n v:=by
  unfold nativeInsertion softInsertion
  rw [←Matrix.mulVec_smul,←Matrix.mulVec_smul,←Matrix.mulVec_smul,lifted_scale epsilon nonzero]

theorem softForcing_generated (epsilon s : ℝ) (n : PhysicalMomentum) (nonzero : epsilon≠0) (forcing : Fin 289→ℂ) :
    (epsilon:ℂ)^2 • nativeModeForcing epsilon s n forcing=softForcing epsilon s n forcing:=
  read_scale epsilon nonzero _

theorem native_soft_normalization (epsilon s : ℝ) (n : PhysicalMomentum) (nonzero : epsilon≠0) (forcing : Fin 289→ℂ) :
    (2*(sourceFrequency epsilon s:ℂ)) • ((epsilon:ℂ)^2 •
      nativeInsertion epsilon s n (sourceResidue epsilon s n*ᵥnativeModeForcing epsilon s n forcing))=
      softResponse epsilon s n forcing:=by
  rw [softResponse,←softInsertion_generated epsilon s n nonzero,←softForcing_generated epsilon s n nonzero]
  simp only [Matrix.smul_mulVec,Matrix.mulVec_smul,nativeInsertion_smul,smul_smul,sourceFrequency,Complex.ofReal_mul,Complex.ofReal_pow]
  congr 1
  ring

def nativeBranchVector (branch : Fin 2) : Fin 289→ℂ:=
  originalChange 0*ᵥ(fullKernelFrame*ᵥ(slowFastFrame*ᵥfiveVector (Pi.single (residueIndex branch) 1)))

def nativeBranchRead (branch : Fin 2) (forcing : Fin 289→ℂ) : ℂ:=
  (slowFastFrame.transpose*ᵥ(fullKernelFrame.transpose*ᵥactiveForcing 0 forcing)) (fiveIndex (residueIndex branch))

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

private theorem ray_continuous (n : PhysicalMomentum) : Continuous (fun x : ℝ×ℝ=>frequencyRay x.1 x.2 n):=by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · change Continuous (fun x : ℝ×ℝ=> -Complex.I*((x.2*x.1^2:ℝ):ℂ))
    fun_prop
  · change Continuous (fun x : ℝ×ℝ=>Complex.I*((x.1^2*n j:ℝ):ℂ))
    fun_prop

private theorem green_continuous_origin : ContinuousAt unrestrictedGreen (0:Fin 4→ℂ):=by
  have detInverse : ContinuousAt Ring.inverse (complementKernel 0).det:=by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ origin_determinant
  have inverse : ContinuousAt (fun p=>(complementKernel p)⁻¹) (0:Fin 4→ℂ):=
    (continuousAt_matrix_inv _ detInverse).tendsto.comp complementKernel_continuous.continuousAt.tendsto
  exact (continuousAt_const.mul inverse).mul continuousAt_const

private theorem frame_continuous_origin : ContinuousAt rawEffectiveFrame (0:Fin 4→ℂ):=
  continuousAt_const.sub ((green_continuous_origin.mul (sourceMatrix_continuous activeTerms).continuousAt).mul continuousAt_const)

private theorem reader_continuous_origin : ContinuousAt rawEffectiveReader (0:Fin 4→ℂ):=
  continuousAt_const.sub ((continuousAt_const.mul (sourceMatrix_continuous activeTerms).continuousAt).mul green_continuous_origin)

theorem rawEffectiveFrame_origin : rawEffectiveFrame 0=fullKernelFrame:=by
  unfold rawEffectiveFrame
  rw [mul_assoc,fullKernel_origin,mul_zero,sub_zero]

theorem rawEffectiveReader_origin : rawEffectiveReader 0=fullKernelFrame.transpose:=by
  have h:=congrArg Matrix.transpose fullKernel_origin
  have symmetric : (activeKernel 0).transpose=activeKernel 0:=by
    simpa only [neg_zero] using PreparationVacuumMixedEffective.activeKernel_reflect (0:Fin 4→ℂ)
  rw [Matrix.transpose_mul,Matrix.transpose_zero,symmetric] at h
  unfold rawEffectiveReader
  rw [h,zero_mul,sub_zero]

private theorem mulVec_tendsto {X : Type*} {m n : ℕ} {L : Filter X}
    {M : X→Matrix (Fin m) (Fin n) ℂ} {v : X→Fin n→ℂ} {M₀ : Matrix (Fin m) (Fin n) ℂ} {v₀ : Fin n→ℂ}
    (matrix : Tendsto M L (𝓝 M₀)) (vector : Tendsto v L (𝓝 v₀)) :
    Tendsto (fun x=>M x*ᵥv x) L (𝓝 (M₀*ᵥv₀)):=by
  apply tendsto_pi_nhds.mpr
  intro i
  change Tendsto (fun x=>∑j : Fin n,M x i j*v x j) L (𝓝 (∑j : Fin n,M₀ i j*v₀ j))
  apply tendsto_finsetSum
  intro j _
  exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp matrix i) j).mul (tendsto_pi_nhds.mp vector j)

private theorem fiveVector_continuous : Continuous (fiveVector : (Fin 5→ℂ)→Fin 289→ℂ):=by
  apply continuous_pi
  intro i
  unfold fiveVector
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

private theorem regularScaling_continuous : Continuous regularScaling:=by
  apply continuous_matrix
  intro i j
  simp only [regularScaling,Matrix.diagonal_apply]
  split_ifs <;> fun_prop

theorem sourceRay_soft_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>frequencyRay e.val (sourceSheet branch n unit e.val) n) scaleApproach (𝓝 0):=by
  have path := scaleVal_tendsto.prodMk_nhds ((sourceSheet_tendsto branch n unit).comp scaleVal_tendsto)
  have result:=(ray_continuous n).tendsto (0,sourceSpeed branch) |>.comp path
  simpa only [Function.comp_def,frequencyRay_scaled,Complex.ofReal_zero,zero_pow (by decide : 2≠0),zero_smul] using result

private theorem fieldFrame_soft_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>rawEffectiveFrame (frequencyRay e.val (sourceSheet branch n unit e.val) n)) scaleApproach
      (𝓝 fullKernelFrame):=by
  have result:=frame_continuous_origin.tendsto.comp (sourceRay_soft_limit branch n unit)
  simpa only [Function.comp_def,rawEffectiveFrame_origin] using result

private theorem fieldReader_soft_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>rawEffectiveReader (frequencyRay e.val (sourceSheet branch n unit e.val) n)) scaleApproach
      (𝓝 fullKernelFrame.transpose):=by
  have result:=reader_continuous_origin.tendsto.comp (sourceRay_soft_limit branch n unit)
  simpa only [Function.comp_def,rawEffectiveReader_origin] using result

private theorem softInsertion_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (v : scaleDomain→Fin 5→ℂ) (v₀ : Fin 5→ℂ) (limit : Tendsto v scaleApproach (𝓝 v₀)) :
    Tendsto (fun e : scaleDomain=>softInsertion e.val (sourceSheet branch n unit e.val) n (v e)) scaleApproach
      (𝓝 (originalChange 0*ᵥ(fullKernelFrame*ᵥ(slowFastFrame*ᵥfiveVector (regularScaling 0*ᵥv₀))))):=by
  have source : Tendsto (fun e : scaleDomain=>originalChange (frequencyRay e.val (sourceSheet branch n unit e.val) n))
      scaleApproach (𝓝 (originalChange 0)):=
    (sourceMatrix_continuous originalChangeTerms).tendsto 0 |>.comp (sourceRay_soft_limit branch n unit)
  have scale : Tendsto (fun e : scaleDomain=>regularScaling e.val) scaleApproach (𝓝 (regularScaling 0)):=
    (regularScaling_continuous.tendsto 0).comp scaleVal_tendsto
  have scaled:=mulVec_tendsto scale limit
  have lift:= (fiveVector_continuous.tendsto (regularScaling 0*ᵥv₀)).comp scaled
  exact mulVec_tendsto source (mulVec_tendsto (fieldFrame_soft_limit branch n unit)
    (mulVec_tendsto tendsto_const_nhds lift))

private theorem readback_continuous : Continuous originalReadback:=
  ((sourceMatrix_continuous originalChangeTerms).comp continuous_neg).matrix_transpose

private theorem select_continuous : Continuous (fun v : Fin 289→ℂ=>fun i : Fin 5=>v (fiveIndex i)):=
  continuous_pi (fun i=>continuous_apply (fiveIndex i))

private theorem softForcing_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (forcing : scaleDomain→Fin 289→ℂ) (forcing₀ : Fin 289→ℂ) (limit : Tendsto forcing scaleApproach (𝓝 forcing₀)) :
    Tendsto (fun e : scaleDomain=>softForcing e.val (sourceSheet branch n unit e.val) n (forcing e)) scaleApproach
      (𝓝 (regularScaling 0*ᵥ(fun i=>(slowFastFrame.transpose*ᵥ(fullKernelFrame.transpose*ᵥactiveForcing 0 forcing₀)) (fiveIndex i)))):=by
  have readback := (readback_continuous.tendsto 0).comp (sourceRay_soft_limit branch n unit)
  have active : Tendsto (fun e : scaleDomain=>activeForcing (frequencyRay e.val (sourceSheet branch n unit e.val) n) (forcing e))
      scaleApproach (𝓝 (activeForcing 0 forcing₀)):=mulVec_tendsto tendsto_const_nhds (mulVec_tendsto readback limit)
  have read := mulVec_tendsto (fieldReader_soft_limit branch n unit) active
  have changed : Tendsto (fun e : scaleDomain=>slowFastFrame.transpose*ᵥ(rawEffectiveReader
      (frequencyRay e.val (sourceSheet branch n unit e.val) n)*ᵥactiveForcing
        (frequencyRay e.val (sourceSheet branch n unit e.val) n) (forcing e))) scaleApproach
      (𝓝 (slowFastFrame.transpose*ᵥ(fullKernelFrame.transpose*ᵥactiveForcing 0 forcing₀))):=
    mulVec_tendsto tendsto_const_nhds read
  have selected:=select_continuous.tendsto _ |>.comp changed
  have scale : Tendsto (fun e : scaleDomain=>regularScaling e.val) scaleApproach (𝓝 (regularScaling 0)):=
    (regularScaling_continuous.tendsto 0).comp scaleVal_tendsto
  exact mulVec_tendsto scale selected

private theorem regular_single (branch : Fin 2) :
    regularScaling 0*ᵥ(Pi.single (residueIndex branch) (1:ℂ))=Pi.single (residueIndex branch) 1:=by
  funext i
  rw [regularScaling,Matrix.mulVec_diagonal]
  by_cases same : i=residueIndex branch
  · subst i
    fin_cases branch <;> norm_num [residueIndex]
  · simp [same]

private theorem regular_read (branch : Fin 2) (v : Fin 5→ℂ) :
    (regularScaling 0*ᵥv) (residueIndex branch)=v (residueIndex branch):=by
  rw [regularScaling,Matrix.mulVec_diagonal]
  fin_cases branch <;> norm_num [residueIndex]

private theorem fiveVector_smul (c : ℂ) (v : Fin 5→ℂ) : fiveVector (c • v)=c • fiveVector v:=by
  funext i
  simp only [fiveVector,Pi.smul_apply]
  split_ifs <;> simp

/-- The soft response keeps the complete native source direction and its actual source forcing read. -/
def leadingNativeResponse (branch : Fin 2) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  ((softCoefficient branch:ℂ)*nativeBranchRead branch forcing) • nativeBranchVector branch

theorem softResponse_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (forcing : scaleDomain→Fin 289→ℂ) (forcing₀ : Fin 289→ℂ) (limit : Tendsto forcing scaleApproach (𝓝 forcing₀)) :
    Tendsto (fun e : scaleDomain=>softResponse e.val (sourceSheet branch n unit e.val) n (forcing e)) scaleApproach
      (𝓝 (leadingNativeResponse branch forcing₀)):=by
  have mode := mulVec_tendsto (sourceResidue_normalized_soft_limit branch n unit)
    (softForcing_limit branch n unit forcing forcing₀ limit)
  have returned := softInsertion_limit branch n unit _ _ mode
  rw [Matrix.single_mulVec_eq,regular_read,Matrix.mulVec_smul,regular_single,fiveVector_smul,
    Matrix.mulVec_smul,Matrix.mulVec_smul,Matrix.mulVec_smul] at returned
  exact returned

end LowEnergy.PreparationVacuumSoftPoleSelection
