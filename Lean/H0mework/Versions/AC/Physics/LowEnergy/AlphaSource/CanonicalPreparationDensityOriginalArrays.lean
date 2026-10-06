import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationDensityPoleJets

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDensityBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry PreparationScalarCoordinates
open PreparationVacuumDensityTrace PreparationVacuumLowerLeaves PreparationPhaseScalar
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert
open PreparationActualFactor CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology

private theorem cjet_germ {f g : Symbol} {x : Phase} (same : f=ᶠ[𝓝 x]g) (m : ℕ) (w : Word m) :
    jet m f w x=jet m g w x := PreparationVacuumCoframeBudget.jet_germ same m w
private theorem cjet_scale (c : ℝ) (f : Symbol) (m : ℕ) (w : Word m) (x : Phase)
    (smooth : ContDiffAt ℝ ∞ f x) : jet m (fun y => c*f y) w x=c*jet m f w x :=
  PreparationVacuumCoframeBudget.jet_scale c f m w x smooth
private theorem cjet_zero (m : ℕ) (w : Word m) (x : Phase) : jet m (fun _ => 0) w x=0 :=
  PreparationVacuumCoframeBudget.jet_zero m w x

def rhoSupport : Finset (Fin 100) := {67,77}
def coframeSupport : Finset (Fin 100) := {0,2,5}
def rhoWeight (i : Fin 100) : ℝ := if i=77 then 1/2 else 1

def sparseField (s : Finset (Fin 100)) (weight : Fin 100 → ℝ) (a : ℕ) (i : Fin 100) : Symbol :=
  if i∈s then (fun x => weight i*inversePower i a x) else (fun _ => 0)
def sparseHessian (s : Finset (Fin 100)) (weight : Fin 100 → ℝ) (i k : Fin 100) : Symbol :=
  if i=k then sparseField s (fun j => -weight j) 2 k else (fun _ => 0)

theorem rhoSupport_selected (i : Fin 100) (hi : i∈rhoSupport) : selectedPole i := by
  simp only [rhoSupport,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl <;> simp [selectedPole]
theorem coframeSupport_selected (i : Fin 100) (hi : i∈coframeSupport) : selectedPole i := by
  simp only [coframeSupport,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl <;> simp [selectedPole]

theorem physical_pole (x : Phase) (hx : x∈originalPhysicalPhase) (i : Fin 100) (selected : selectedPole i) :
    x∈poleDomainAt i := by
  change positionCoordinate i x≠0
  rw [←coordinate_pullback]
  rcases selected with rfl|rfl|rfl|rfl|rfl
  · exact hx.1.ne'
  · exact hx.2.1.ne'
  · exact hx.2.2.1.ne'
  · exact hx.2.2.2.2.1.ne'
  · exact hx.2.2.2.2.2.1.ne'

theorem sparseField_smooth (s : Finset (Fin 100)) (weight : Fin 100 → ℝ) (a : ℕ) (i : Fin 100)
    (selected : ∀ j∈s,selectedPole j) (x : Phase) (hx : x∈originalPhysicalPhase) :
    ContDiffAt ℝ ∞ (sparseField s weight a i) x := by
  by_cases hi : i∈s
  · rw [sparseField,if_pos hi]
    exact contDiffAt_const.mul (inversePower_smooth i a x (physical_pole x hx i (selected i hi)))
  · simpa only [sparseField,if_neg hi] using
      (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Phase => (0 : ℝ)) x)

theorem sparseField_budget (s : Finset (Fin 100)) (weight : Fin 100 → ℝ) (a : ℕ)
    (selected : ∀ j∈s,selectedPole j) (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (m : ℕ) (w : Word m) :
    (∑ i : Fin 100,|jet m (sparseField s weight a i) w x|) ≤ (∑ i∈s,|weight i|)*poleArray a m := by
  have point (i : Fin 100) : |jet m (sparseField s weight a i) w x| ≤
      if i∈s then |weight i| *poleArray a m else 0 := by
    by_cases hi : i∈s
    · obtain ⟨hx,bound⟩ := source_pole_inverse x box i (selected i hi)
      rw [sparseField,if_pos hi,cjet_scale _ _ _ _ _ (inversePower_smooth i a x hx),abs_mul]
      rw [if_pos hi]
      exact mul_le_mul_of_nonneg_left (inversePower_budget i a m w x hx bound) (abs_nonneg _)
    · simp only [sparseField,if_neg hi,cjet_zero,abs_zero,le_refl]
  calc
    _ ≤ ∑ i : Fin 100,if i∈s then |weight i| *poleArray a m else 0 := Finset.sum_le_sum (fun i _ => point i)
    _ = _ := by simp [Finset.sum_mul]

theorem sparseHessian_budget (s : Finset (Fin 100)) (weight : Fin 100 → ℝ)
    (selected : ∀ j∈s,selectedPole j) (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (m : ℕ) (w : Word m) :
    (∑ i : Fin 100,∑ k : Fin 100,|jet m (sparseHessian s weight i k) w x|) ≤
      (∑ i∈s,|weight i|)*poleArray 2 m := by
  have read (i k : Fin 100) : jet m (sparseHessian s weight i k) w x=
      if i=k then jet m (sparseField s (fun j => -weight j) 2 k) w x else 0 := by
    by_cases h : i=k <;> simp only [sparseHessian,h,if_true,if_false,cjet_zero]
  simp_rw [read,apply_ite,abs_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simpa only [abs_neg] using sparseField_budget s (fun j => -weight j) 2 selected x box m w

def rhoAmbient (i : Fin 100) : Symbol := fun x => rhoLog i (fullCoordinates.symm x.1)
def coframeAmbient (i : Fin 100) : Symbol := fun x => coframeLog i (fullCoordinates.symm x.1)
def rawAmbient (i : Fin 100) : Symbol := fun x => rawHalfLog i (fullCoordinates.symm x.1)

theorem rhoAmbient_sparse (i : Fin 100) : rhoAmbient i=sparseField rhoSupport rhoWeight 1 i := by
  funext x
  by_cases h67 : i=67
  · subst i; simp [rhoAmbient,rhoLog,sparseField,rhoSupport,rhoWeight,inversePower,coordinate_pullback,Fin.ext_iff]
  · by_cases h77 : i=77
    · subst i; simp [rhoAmbient,rhoLog,sparseField,rhoSupport,rhoWeight,inversePower,coordinate_pullback,Fin.ext_iff]
    · simp [rhoAmbient,rhoLog,sparseField,rhoSupport,h67,h77]

theorem coframeAmbient_sparse (i : Fin 100) : coframeAmbient i=sparseField coframeSupport (fun _ => 1) 1 i := by
  funext x
  by_cases h0 : i=0
  · subst i; simp [coframeAmbient,coframeLog,sparseField,coframeSupport,inversePower,coordinate_pullback,Fin.ext_iff]
  · by_cases h2 : i=2
    · subst i; simp [coframeAmbient,coframeLog,sparseField,coframeSupport,inversePower,coordinate_pullback,Fin.ext_iff]
    · by_cases h5 : i=5
      · subst i; simp [coframeAmbient,coframeLog,sparseField,coframeSupport,inversePower,coordinate_pullback,Fin.ext_iff]
      · simp [coframeAmbient,coframeLog,sparseField,coframeSupport,h0,h2,h5]

theorem rhoLog_smooth (i : Fin 100) (z : physicalChart) : ContDiffAt ℝ ∞ (rhoLog i) z.val := by
  unfold rhoLog
  apply ContDiffAt.add
  · exact contDiffAt_const.mul ((coordinate 67).contDiff.contDiffAt.inv z.property.2.2.2.2.1.ne')
  · exact contDiffAt_const.mul ((coordinate 77).contDiff.contDiffAt.inv z.property.2.2.2.2.2.1.ne')

theorem coframeLog_smooth (i : Fin 100) (z : physicalChart) : ContDiffAt ℝ ∞ (coframeLog i) z.val := by
  unfold coframeLog
  apply ContDiffAt.add
  · apply ContDiffAt.add
    · exact contDiffAt_const.mul ((coordinate 0).contDiff.contDiffAt.inv z.property.1.ne')
    · exact contDiffAt_const.mul ((coordinate 2).contDiff.contDiffAt.inv z.property.2.1.ne')
  · exact contDiffAt_const.mul ((coordinate 5).contDiff.contDiffAt.inv z.property.2.2.1.ne')

def rhoHessianAmbient (i k : Fin 100) : Symbol := fun x =>
  fderiv ℝ (rhoLog k) (fullCoordinates.symm x.1) (rawDirection i)
def coframeHessianAmbient (i k : Fin 100) : Symbol := fun x =>
  fderiv ℝ (coframeLog k) (fullCoordinates.symm x.1) (rawDirection i)
def rawHessianAmbient (i k : Fin 100) : Symbol := fun x =>
  fderiv ℝ (rawHalfLog k) (fullCoordinates.symm x.1) (rawDirection i)

private def configurationMap : Phase →L[ℝ] Configuration :=
  fullCoordinates.symm.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ _ _)

private theorem native_derivative (f : Configuration → ℝ) (x : Phase) (i : Fin 100)
    (smooth : ContDiffAt ℝ ∞ f (fullCoordinates.symm x.1)) :
    fderiv ℝ (fun y => f (fullCoordinates.symm y.1)) x (qDirection i)=
      fderiv ℝ f (fullCoordinates.symm x.1) (rawDirection i) := by
  have derivative := (smooth.differentiableAt (by simp)).hasFDerivAt.comp x configurationMap.hasFDerivAt
  change fderiv ℝ (f∘configurationMap) x (qDirection i)=_
  rw [derivative.fderiv]
  rfl

theorem sparseField_derivative (s : Finset (Fin 100)) (weight : Fin 100 → ℝ)
    (selected : ∀ j∈s,selectedPole j) (x : Phase) (hx : x∈originalPhysicalPhase) (i k : Fin 100) :
    fderiv ℝ (sparseField s weight 1 k) x (qDirection i)=sparseHessian s weight i k x := by
  by_cases hk : k∈s
  · have regular := physical_pole x hx k (selected k hk)
    rw [sparseField,if_pos hk,((inversePower_smooth k 1 x regular).differentiableAt (by simp)).hasFDerivAt.const_mul (weight k) |>.fderiv]
    simp only [smul_apply,smul_eq_mul]
    change weight k*fderiv ℝ (inversePower k 1) x (slotDirection (i,false))=_
    rw [inversePower_direction k 1 (i,false) x regular]
    by_cases h : i=k
    · subst i; simp [sparseHessian,sparseField,hk]
    · simp [sparseHessian,h,Ne.symm h]
  · simp [sparseField,hk,sparseHessian,fderiv_const_apply]

theorem rhoHessian_sparse (x : Phase) (hx : x∈originalPhysicalPhase) (i k : Fin 100) :
    rhoHessianAmbient i k x=sparseHessian rhoSupport rhoWeight i k x := by
  rw [rhoHessianAmbient,←native_derivative (rhoLog k) x i (rhoLog_smooth k ⟨_,hx⟩)]
  change fderiv ℝ (rhoAmbient k) x (qDirection i)=_
  rw [rhoAmbient_sparse]
  exact sparseField_derivative rhoSupport rhoWeight rhoSupport_selected x hx i k

theorem coframeHessian_sparse (x : Phase) (hx : x∈originalPhysicalPhase) (i k : Fin 100) :
    coframeHessianAmbient i k x=sparseHessian coframeSupport (fun _ => 1) i k x := by
  rw [coframeHessianAmbient,←native_derivative (coframeLog k) x i (coframeLog_smooth k ⟨_,hx⟩)]
  change fderiv ℝ (coframeAmbient k) x (qDirection i)=_
  rw [coframeAmbient_sparse]
  exact sparseField_derivative coframeSupport (fun _ => 1) coframeSupport_selected x hx i k

def ellArray (m : ℕ) : ℝ := 2*(m.factorial : ℝ)*15^(m+1)
def logHArray (m : ℕ) : ℝ := 2*((m+1).factorial : ℝ)*15^(m+2)
def coframeEllArray (m : ℕ) : ℝ := 3*(m.factorial : ℝ)*15^(m+1)
def coframeLogHArray (m : ℕ) : ℝ := 3*((m+1).factorial : ℝ)*15^(m+2)

private theorem poleArray_one (m : ℕ) : poleArray 1 m=inverseArray m := by
  simp [poleArray,inverseArray,Nat.one_ascFactorial,Nat.add_comm]
private theorem poleArray_two (m : ℕ) : poleArray 2 m=inverseSquareArray m := by
  have rising : (2 : ℕ).ascFactorial m=(m+1).factorial := by
    simpa only [Nat.factorial_one,one_mul,Nat.add_comm] using Nat.factorial_mul_ascFactorial 1 m
  simp [poleArray,inverseSquareArray,rising,Nat.add_comm]

private theorem source_physical (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x) :
    x∈originalPhysicalPhase := (phaseChart x.1 box).property

theorem original_rho_ell_budget (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (m : ℕ) (w : Word m) : (∑ i : Fin 100,|jet m (rhoAmbient i) w x|) ≤ ellArray m := by
  simp_rw [rhoAmbient_sparse]
  have result := sparseField_budget rhoSupport rhoWeight 1 rhoSupport_selected x box m w
  norm_num [rhoSupport,rhoWeight,Fin.ext_iff,poleArray_one] at result
  apply result.trans
  unfold ellArray inverseArray
  have nonnegative : 0 ≤ (m.factorial : ℝ)*15^(m+1) := by positivity
  nlinarith

theorem original_rho_logH_budget (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (m : ℕ) (w : Word m) : (∑ i : Fin 100,∑ k : Fin 100,|jet m (rhoHessianAmbient i k) w x|) ≤ logHArray m := by
  have read (i k : Fin 100) : jet m (rhoHessianAmbient i k) w x=jet m (sparseHessian rhoSupport rhoWeight i k) w x := by
    apply cjet_germ
    filter_upwards [originalPhysicalPhase_open.mem_nhds (source_physical x box)] with y hy
    exact rhoHessian_sparse y hy i k
  simp_rw [read]
  have result := sparseHessian_budget rhoSupport rhoWeight rhoSupport_selected x box m w
  norm_num [rhoSupport,rhoWeight,Fin.ext_iff,poleArray_two] at result
  apply result.trans
  unfold logHArray inverseSquareArray
  have nonnegative : 0 ≤ ((m+1).factorial : ℝ)*15^(m+2) := by positivity
  nlinarith

theorem coframe_ell_budget (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (m : ℕ) (w : Word m) : (∑ i : Fin 100,|jet m (coframeAmbient i) w x|) ≤ coframeEllArray m := by
  simp_rw [coframeAmbient_sparse]
  have result := sparseField_budget coframeSupport (fun _ => 1) 1 coframeSupport_selected x box m w
  simpa [coframeSupport,poleArray_one,inverseArray,coframeEllArray,mul_assoc] using result

theorem coframe_logH_budget (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (m : ℕ) (w : Word m) : (∑ i : Fin 100,∑ k : Fin 100,|jet m (coframeHessianAmbient i k) w x|) ≤ coframeLogHArray m := by
  have read (i k : Fin 100) : jet m (coframeHessianAmbient i k) w x=jet m (sparseHessian coframeSupport (fun _ => 1) i k) w x := by
    apply cjet_germ
    filter_upwards [originalPhysicalPhase_open.mem_nhds (source_physical x box)] with y hy
    exact coframeHessian_sparse y hy i k
  simp_rw [read]
  have result := sparseHessian_budget coframeSupport (fun _ => 1) coframeSupport_selected x box m w
  simpa [coframeSupport,poleArray_two,inverseSquareArray,coframeLogHArray,mul_assoc] using result

private theorem embedded_sum {a b : ℕ} (e : Fin a ↪ Fin b) (f : Fin b → ℝ)
    (positive : ∀ i,0 ≤ f i) : (∑ i,f (e i)) ≤ ∑ i,f i := by
  rw [←Finset.sum_image]
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => positive i)
  · exact fun i _ j _ h => e.injective h

private theorem embedded_double {a b : ℕ} (e : Fin a ↪ Fin b) (f : Fin b → Fin b → ℝ)
    (positive : ∀ i k,0 ≤ f i k) : (∑ i,∑ k,f (e i) (e k)) ≤ ∑ i,∑ k,f i k := by
  apply (Finset.sum_le_sum (fun i _ => embedded_sum e (f (e i)) (positive (e i)))).trans
  exact embedded_sum e (fun i => ∑ k,f i k) (fun i => Finset.sum_nonneg (fun k _ => positive i k))

theorem actual_rho94_budget (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (m : ℕ) (w : Word m) : (∑ i : Fin 94,|jet m (rawAmbient (Fin.natAdd 6 i)) w x|) ≤ ellArray m := by
  have read (i : Fin 94) : jet m (rawAmbient (Fin.natAdd 6 i)) w x=jet m (rhoAmbient (Fin.natAdd 6 i)) w x := by
    apply cjet_germ
    filter_upwards [originalPhysicalPhase_open.mem_nhds (source_physical x box)] with y hy
    exact actual_rawHalfLog_rho i ⟨_,hy⟩
  simp_rw [read]
  exact (embedded_sum ⟨Fin.natAdd 6,Fin.natAdd_injective 94 6⟩
    (fun i => |jet m (rhoAmbient i) w x|) (fun i => abs_nonneg _)).trans (original_rho_ell_budget x box m w)

theorem actual_coframe6_budget (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (m : ℕ) (w : Word m) : (∑ i : Fin 6,|jet m (rawAmbient (Fin.castAdd 94 i)) w x|) ≤ coframeEllArray m := by
  have read (i : Fin 6) : jet m (rawAmbient (Fin.castAdd 94 i)) w x=jet m (coframeAmbient (Fin.castAdd 94 i)) w x := by
    apply cjet_germ
    filter_upwards [originalPhysicalPhase_open.mem_nhds (source_physical x box)] with y hy
    exact actual_rawHalfLog_coframe i ⟨_,hy⟩
  simp_rw [read]
  exact (embedded_sum ⟨Fin.castAdd 94,Fin.castAdd_injective 6 94⟩
    (fun i => |jet m (coframeAmbient i) w x|) (fun i => abs_nonneg _)).trans (coframe_ell_budget x box m w)

private theorem native_rho_hessian (i : Fin 100) (k : Fin 94) (z : physicalChart) :
    fderiv ℝ (rawHalfLog (Fin.natAdd 6 k)) z.val (rawDirection i)=
      fderiv ℝ (rhoLog (Fin.natAdd 6 k)) z.val (rawDirection i) := by
  have germ : rawHalfLog (Fin.natAdd 6 k)=ᶠ[𝓝 z.val]rhoLog (Fin.natAdd 6 k) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with y hy
    exact actual_rawHalfLog_rho k ⟨y,hy⟩
  rw [germ.fderiv_eq]

private theorem native_coframe_hessian (i : Fin 100) (k : Fin 6) (z : physicalChart) :
    fderiv ℝ (rawHalfLog (Fin.castAdd 94 k)) z.val (rawDirection i)=
      fderiv ℝ (coframeLog (Fin.castAdd 94 k)) z.val (rawDirection i) := by
  have germ : rawHalfLog (Fin.castAdd 94 k)=ᶠ[𝓝 z.val]coframeLog (Fin.castAdd 94 k) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with y hy
    exact actual_rawHalfLog_coframe k ⟨y,hy⟩
  rw [germ.fderiv_eq]

theorem actual_rho94_logH_budget (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (m : ℕ) (w : Word m) :
    (∑ i : Fin 94,∑ k : Fin 94,|jet m (rawHessianAmbient (Fin.natAdd 6 i) (Fin.natAdd 6 k)) w x|) ≤ logHArray m := by
  have read (i k : Fin 94) : jet m (rawHessianAmbient (Fin.natAdd 6 i) (Fin.natAdd 6 k)) w x=
      jet m (rhoHessianAmbient (Fin.natAdd 6 i) (Fin.natAdd 6 k)) w x := by
    apply cjet_germ
    filter_upwards [originalPhysicalPhase_open.mem_nhds (source_physical x box)] with y hy
    exact native_rho_hessian _ k ⟨_,hy⟩
  simp_rw [read]
  exact (embedded_double ⟨Fin.natAdd 6,Fin.natAdd_injective 94 6⟩
    (fun i k => |jet m (rhoHessianAmbient i k) w x|) (fun i k => abs_nonneg _)).trans
      (original_rho_logH_budget x box m w)

theorem actual_coframe6_logH_budget (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (m : ℕ) (w : Word m) :
    (∑ i : Fin 6,∑ k : Fin 6,|jet m (rawHessianAmbient (Fin.castAdd 94 i) (Fin.castAdd 94 k)) w x|) ≤ coframeLogHArray m := by
  have read (i k : Fin 6) : jet m (rawHessianAmbient (Fin.castAdd 94 i) (Fin.castAdd 94 k)) w x=
      jet m (coframeHessianAmbient (Fin.castAdd 94 i) (Fin.castAdd 94 k)) w x := by
    apply cjet_germ
    filter_upwards [originalPhysicalPhase_open.mem_nhds (source_physical x box)] with y hy
    exact native_coframe_hessian _ k ⟨_,hy⟩
  simp_rw [read]
  exact (embedded_double ⟨Fin.castAdd 94,Fin.castAdd_injective 6 94⟩
    (fun i k => |jet m (coframeHessianAmbient i k) w x|) (fun i k => abs_nonneg _)).trans
      (coframe_logH_budget x box m w)

theorem rawHessian_off_diagonal (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (i k : Fin 100) (different : i≠k) (m : ℕ) (w : Word m) : jet m (rawHessianAmbient i k) w x=0 := by
  have germ : rawHessianAmbient i k=ᶠ[𝓝 x](fun _ => 0) := by
    filter_upwards [originalPhysicalPhase_open.mem_nhds (source_physical x box)] with y hy
    have split : rawHalfLog k=ᶠ[𝓝 (fullCoordinates.symm y.1)](fun z => coframeLog k z+rhoLog k z) := by
      filter_upwards [physicalChart.isOpen.mem_nhds hy] with z hz
      exact actual_rawHalfLog_split k ⟨z,hz⟩
    have derivative := ((coframeLog_smooth k ⟨_,hy⟩).differentiableAt (by simp)).hasFDerivAt.add
      ((rhoLog_smooth k ⟨_,hy⟩).differentiableAt (by simp)).hasFDerivAt
    unfold rawHessianAmbient
    rw [split.fderiv_eq]
    change fderiv ℝ (coframeLog k+rhoLog k) (fullCoordinates.symm y.1) (rawDirection i)=0
    have formula : fderiv ℝ (coframeLog k+rhoLog k) (fullCoordinates.symm y.1)=
        fderiv ℝ (coframeLog k) (fullCoordinates.symm y.1)+fderiv ℝ (rhoLog k) (fullCoordinates.symm y.1) := derivative.fderiv
    rw [formula]
    change coframeHessianAmbient i k y+rhoHessianAmbient i k y=0
    rw [coframeHessian_sparse y hy,rhoHessian_sparse y hy]
    simp [sparseHessian,different]
  rw [cjet_germ germ,cjet_zero]

end LowEnergy.PreparationVacuumDensityBudget
