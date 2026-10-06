import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceMatterForceTimeBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceMatterContactCoframe
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy GaussMatterCore
open SourceCartanCubic GaussNativePotential
open GaussHistoryHilbert GaussLiveMomentum SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumScalarChart SourceQuantumFockGauge SourcePhysicalKineticSquare SourceScalarBalancedForce
open SourceElectricColumns SourceElectricCompletedSquare SourceMatterForceAbsorption
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private def evaluate (z : SourceCoordinateSlice) : QuantumTest →ₗ[ℂ] FockFiber where
  toFun f := f z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem source_lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem source_sigma_pos : 0<sourceSigma :=
  SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource.legacy.sigma_pos

private theorem root_cancel (n σ v : ℝ) (hn : 0<n) (hσ : 0<σ) (hv : 0<v) :
    Real.sqrt (σ*v/n)*(Real.sqrt v)⁻¹*(2*n)=2*Real.sqrt (σ*n) := by
  have he : σ*v/n=(σ/n)*v := by ring
  have hs : σ*n=(σ/n)*n^2 := by field_simp
  rw [he,Real.sqrt_mul (div_nonneg hσ.le hn.le),hs,Real.sqrt_mul (div_nonneg hσ.le hn.le),
    Real.sqrt_sq hn.le]
  field_simp [(Real.sqrt_pos.mpr hv).ne']

/-- The original electric metric factor and inverse volume cancel exactly against the true matter coefficient. -/
theorem original_coframe_factor (k i b : Fin 3) (z : physicalChart) :
    factorCoefficient k i z.val*GaussMatterCore.coefficient i b z.val*inverseRootVolume z.val=
      2*Real.sqrt (sourceSigma*sourceTime 0)*(triadInverse z.val.1 i k*triadInverse z.val.1 i b) := by
  have h := root_cancel (sourceTime 0) sourceSigma (volume z.val) source_lapse_pos source_sigma_pos (volume_pos z)
  unfold factorCoefficient GaussMatterCore.coefficient inverseRootVolume
  linear_combination h*(triadInverse z.val.1 i k*triadInverse z.val.1 i b)

def coframeGram (k b : Fin 3) (z : SourceCoordinateSlice) : ℝ :=
  ∑ i : Fin 3,triadInverse z.1 i k*triadInverse z.1 i b
private theorem coframe_gram_smooth (k b : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (coframeGram k b) z.val :=
  ContDiffAt.sum (fun i _ => (triadInverse_smooth i k z).mul (triadInverse_smooth i b z))

def fixedContact (b : Fin 3) (a : LieIndex) : End :=
  localMultiplier (fun _ => quantumTerm b (lieBasis a)) (fun _ => contDiffAt_const)

def coframeColumn (k : Fin 3) (a : LieIndex) : End :=
  ∑ b : Fin 3,multiply (coframeGram k b) (coframe_gram_smooth k b)*fixedContact b a

private theorem contact_apply (i : Fin 3) (a : LieIndex) (f : QuantumTest) (z : SourceCoordinateSlice) :
    matterContact (gaugeDirection i a) f z=
      (∑ b : Fin 3,(GaussMatterCore.coefficient i b z : ℂ) • quantumTerm b (lieBasis a)) (f z) := by
  change contactFiber (gaugeDirection i a) z (f z)=_
  have hc (j : Fin 3) : gaugeCoordinate j (gaugeDirection i a).2=if j=i then lieBasis a else 0 := by
    change (Pi.single i (lieBasis a) : Fin 3 → NativeLie) j=_
    simp only [Pi.single_apply]
  simp only [contactFiber,sum_apply,smul_apply]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro b _
    rw [hc,if_pos rfl]
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro b _
    rw [hc,if_neg hji,map_zero,zero_apply,smul_zero]
  · simp only [Finset.mem_univ,not_true_eq_false,false_implies]

/-- Every original contact column is a coframe-only finite CAR column, with its source normalization. -/
theorem original_contact_column (k : Fin 3) (a : LieIndex) (f : QuantumTest) :
    (∑ i : Fin 3,factorColumn k i (matterContact (gaugeDirection i a) (inverseRootAction f)))=
      ((2*Real.sqrt (sourceSigma*sourceTime 0) : ℝ) : ℂ) • coframeColumn k a f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · change (∑ i : Fin 3,(factorCoefficient k i z : ℂ) •
        (matterContact (gaugeDirection i a) (inverseRootAction f)) z)=_
    simp only [contact_apply,sum_apply,smul_apply]
    change (∑ i : Fin 3,(factorCoefficient k i z : ℂ) •
      (∑ b : Fin 3,(GaussMatterCore.coefficient i b z : ℂ) •
        (quantumTerm b (lieBasis a)) ((inverseRootVolume z : ℂ) • f z)))=_
    simp only [map_smul,Finset.smul_sum,smul_smul,←Complex.ofReal_mul]
    have he (i b : Fin 3) : factorCoefficient k i z*(GaussMatterCore.coefficient i b z*inverseRootVolume z)=
        2*Real.sqrt (sourceSigma*sourceTime 0)*(triadInverse z.1 i k*triadInverse z.1 i b) := by
      simpa only [mul_assoc] using original_coframe_factor k i b ⟨z,hz⟩
    simp_rw [he]
    rw [Finset.sum_comm]
    simp only [coframeColumn,LinearMap.sum_apply,Module.End.mul_apply]
    change _=((2*Real.sqrt (sourceSigma*sourceTime 0) : ℝ) : ℂ) •
      evaluate z (∑ b : Fin 3,multiply (coframeGram k b) (coframe_gram_smooth k b) (fixedContact b a f))
    rw [map_sum,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b _
    change (∑ i : Fin 3,((2*Real.sqrt (sourceSigma*sourceTime 0)*
      (triadInverse z.1 i k*triadInverse z.1 i b) : ℝ) : ℂ) • (quantumTerm b (lieBasis a)) (f z))=
      ((2*Real.sqrt (sourceSigma*sourceTime 0) : ℝ) : ℂ) •
        ((coframeGram k b z : ℂ) • (quantumTerm b (lieBasis a)) (f z))
    rw [smul_smul,←Finset.sum_smul]
    congr 1
    simp only [coframeGram,Complex.ofReal_sum,Complex.ofReal_mul,Finset.mul_sum]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

/-- The complete original contact moment has no gauge/scalar-coordinate or volume factor: only inverse-triad Gram and fixed CAR actions remain. -/
theorem original_contact_energy_coframe (f : QuantumTest) :
    contactEnergy f=4*sourceSigma*sourceTime 0*
      ∑ a : LieIndex,∑ k : Fin 3,‖embed (coframeColumn k a f)‖^2 := by
  rw [contactEnergy,gauge_pair_factor]
  simp_rw [original_contact_column]
  simp only [Complex.re_sum,sourcePair,map_smul,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal,←mul_assoc,←Complex.ofReal_mul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  have hs := Real.sq_sqrt (mul_nonneg source_sigma_pos.le source_lapse_pos.le)
  have he : (2*Real.sqrt (sourceSigma*sourceTime 0))*(2*Real.sqrt (sourceSigma*sourceTime 0))=
      4*sourceSigma*sourceTime 0 := by nlinarith only [hs]
  have hr (g : QuantumTest) : (inner ℂ (embed g) (embed g)).re=‖embed g‖^2 := by
    simpa only using! inner_self_eq_norm_sq (𝕜 := ℂ) (embed g)
  simp only [hr,←Finset.mul_sum]
  rw [show 2*Real.sqrt (sourceSigma*sourceTime 0)*2*Real.sqrt (sourceSigma*sourceTime 0)=
      4*sourceSigma*sourceTime 0 from by nlinarith only [hs]]

open SourceMatterForceTimeBudget SourceShiftedBulkTimeBudget SourceBulkTwoTime SourceBulkParseval
open GaussDiagonalHistory GaussUnitaryHistory SourceScalarSignedInverseReturn SourceFourPoleEnergyClosed
open SourceScalarInverseRetardedBudget Filter MeasureTheory

def coframeTime (F : Index) (μ : ℝ) (T : End) (g : diagonal.domain) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*
    ∑ a : LieIndex,∑ k : Fin 3,‖embed (coframeColumn k a (T (coreTime F g t)))‖^2

/-- Source sigma=1/2 fixes the complete contact price to nine; the moving coframe Gram remains exact. -/
theorem original_contact_time_price (F : Index) (μ : ℝ) (T : End) (g : diagonal.domain) :
    (9/(2*sourceTime 0))*contactTime F μ T g=9*coframeTime F μ T g := by
  have he : contactTime F μ T g=4*sourceSigma*sourceTime 0*coframeTime F μ T g := by
    unfold contactTime coframeTime
    simp_rw [original_contact_energy_coframe]
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by ring)
  rw [he]
  have hs : sourceSigma=1/2 := SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.sourceCoupling_eq
  rw [hs]
  field_simp [source_lapse_pos.ne']
  ring

/-- The full original cost now reads the actual coframe-only CAR column moment at its fixed source price. -/
theorem actual_original_coframe_contact_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (hgap : 3*sourceTime 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε+
          (4*Real.pi*formPrice sharp*μ⁻¹^2*‖(k : H)‖^2/(μ-3*sourceTime 0))*
            (otherTime F μ (theta m ell) g+9*coframeTime F μ (theta m ell) g) := by
  simpa only [original_contact_time_price] using!
    actual_original_matter_time_budget sharp μ hμ hgap g k

end LowEnergy.SourceMatterContactCoframe
