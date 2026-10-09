import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceWholePhotonPoleOperator

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePhotonFluxReturn
open CanonicalGradedSpatialSource PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator ContDiff
attribute [local irreducible] originalJacobi originalChange originalInverse originalRowLift originalReadback
  sourceWholePhotonGreen sourceWholePhotonResidue sourcePhotonNullSource sourcePhotonNullField

@[fun_prop] private theorem ofReal_smooth : ContDiff ℝ ∞ (fun x : ℝ=>(x:ℂ)) := Complex.ofRealCLM.contDiff

private theorem source_matrix_smooth (terms : List SourceTerm) : ContDiff ℝ ∞ (sourceMatrix terms) := by
  induction terms with
  | nil=>exact contDiff_const
  | cons a rest ih=>
    have scalar : ContDiff ℝ ∞ (fun p : Fin 4→ℂ=>coefficientValue a.coefficient*a.powers.value p) := by
      unfold Powers.value
      fun_prop
    have term : ContDiff ℝ ∞ a.matrix := by
      have result:=scalar.smul (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin 4→ℂ=>Matrix.single a.row a.column (1:ℂ)))
      change ContDiff ℝ ∞ (fun p : Fin 4→ℂ=>(coefficientValue a.coefficient*a.powers.value p) • Matrix.single a.row a.column (1:ℂ)) at result
      change ContDiff ℝ ∞ (fun p : Fin 4→ℂ=>Matrix.single a.row a.column (coefficientValue a.coefficient*a.powers.value p))
      simpa only [Matrix.smul_single,smul_eq_mul,mul_one] using result
    exact term.add ih

private theorem ray_smooth (epsilon : ℝ) (n : PhysicalMomentum) :
    ContDiff ℝ ∞ (fun s : ℝ=>frequencyRay epsilon s n) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · change ContDiff ℝ ∞ (fun s : ℝ=>-Complex.I*((s*epsilon^2:ℝ):ℂ))
    fun_prop
  · exact contDiff_const

/-- The derivative is taken on the original full Jacobi polynomial, before any modal restriction. -/
def sourcePhotonSheetJacobiJet (epsilon s : ℝ) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  deriv (fun t : ℝ=>originalJacobi (frequencyRay epsilon t n)) s

theorem sourcePhotonSheetJacobi_hasDerivAt (epsilon s : ℝ) (n : PhysicalMomentum) :
    HasDerivAt (fun t : ℝ=>originalJacobi (frequencyRay epsilon t n))
      (sourcePhotonSheetJacobiJet epsilon s n) s := by
  have smooth : ContDiff ℝ ∞ (fun t : ℝ=>originalJacobi (frequencyRay epsilon t n)) := by
    simpa only [originalJacobi,Function.comp_def] using (source_matrix_smooth originalJacobiTerms).comp (ray_smooth epsilon n)
  exact (smooth.differentiable (by simp)).differentiableAt.hasDerivAt

theorem sourcePhotonNullSource_continuous (epsilon : ℝ) (n : PhysicalMomentum) :
    Continuous (fun s=>sourcePhotonNullSource epsilon s n) := by
  have row : Continuous (fun s=>originalRowLift (frequencyRay epsilon s n)) := by
    simpa only [originalRowLift,originalInverse,Function.comp_def,Pi.neg_apply] using
      ((source_matrix_smooth originalInverseTerms).continuous.comp (ray_smooth epsilon n).continuous.neg).matrix_transpose
  have read : Continuous (fun s=>originalReadback (frequencyRay epsilon s n)) := by
    simpa only [originalReadback,originalChange,Function.comp_def,Pi.neg_apply] using
      ((source_matrix_smooth originalChangeTerms).continuous.comp (ray_smooth epsilon n).continuous.neg).matrix_transpose
  unfold sourcePhotonNullSource
  exact (row.mul continuous_const).mul read

theorem sourcePhotonNullField_continuous (epsilon : ℝ) (n : PhysicalMomentum) :
    Continuous (fun s=>sourcePhotonNullField epsilon s n) := by
  have change : Continuous (fun s=>originalChange (frequencyRay epsilon s n)) := by
    simpa only [originalChange,Function.comp_def] using
      (source_matrix_smooth originalChangeTerms).continuous.comp (ray_smooth epsilon n).continuous
  have inverse : Continuous (fun s=>originalInverse (frequencyRay epsilon s n)) := by
    simpa only [originalInverse,Function.comp_def] using
      (source_matrix_smooth originalInverseTerms).continuous.comp (ray_smooth epsilon n).continuous
  unfold sourcePhotonNullField
  exact (change.mul continuous_const).mul inverse

private theorem real_smul_matrix (r : ℝ) (M : Matrix (Fin 289) (Fin 289) ℂ) :
    (r:ℂ) • M=r • M := by
  ext i j
  simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]

/-- Both full homogeneous identities are limits of the original two projected Green equations. -/
theorem sourceWholePhotonResidue_homogeneous (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n * originalJacobi (frequencyRay e.val (sourceSheet branch n unit e.val) n)=0 ∧
      originalJacobi (frequencyRay e.val (sourceSheet branch n unit e.val) n) * sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n=0 := by
  filter_upwards [sourceWholePhotonGreen_equations branch n unit,sourceWholePhotonGreen_residue branch n unit] with e equations pole
  let c:=sourceSheet branch n unit e.val
  have jacobi:=((sourcePhotonSheetJacobi_hasDerivAt e.val c n).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] c≤𝓝 c)
  have scalar : Tendsto (fun s : ℝ=>((s-c:ℝ):ℂ)) (𝓝[≠] c) (𝓝 (0:ℂ)) := by
    have continuous : Continuous (fun s : ℝ=>((s-c:ℝ):ℂ)) := by fun_prop
    simpa only [sub_self,Complex.ofReal_zero] using (continuous.tendsto c).mono_left nhdsWithin_le_nhds
  have right:=scalar.smul ((tendsto_const_nhds (x:=(1 : Matrix (Fin 289) (Fin 289) ℂ))).sub (((sourcePhotonNullField_continuous e.val n).tendsto c).mono_left nhdsWithin_le_nhds))
  have left:=scalar.smul ((tendsto_const_nhds (x:=(1 : Matrix (Fin 289) (Fin 289) ℂ))).sub (((sourcePhotonNullSource_continuous e.val n).tendsto c).mono_left nhdsWithin_le_nhds))
  simp only [zero_smul] at right left
  constructor
  · apply tendsto_nhds_unique (pole.mul jacobi)
    apply right.congr'
    filter_upwards [equations] with s original
    rw [smul_mul_assoc,original.2]
  · apply tendsto_nhds_unique (jacobi.mul pole)
    apply left.congr'
    filter_upwards [equations] with s original
    rw [mul_smul_comm,original.1]

/-- The varying null-source term is retained in the difference quotient and annihilated by the actual source residue. -/
theorem sourceWholePhotonResidue_sheetFlux (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n *
        sourcePhotonSheetJacobiJet e.val (sourceSheet branch n unit e.val) n *
        sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n =
      sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceWholePhotonGreen_equations branch n unit,sourceWholePhotonGreen_residue branch n unit,
    sourceWholePhotonResidue_homogeneous branch n unit] with e equations pole homogeneous
  let c:=sourceSheet branch n unit e.val
  let R:=sourceWholePhotonResidue e.val c n
  let K:=fun s : ℝ=>originalJacobi (frequencyRay e.val s n)
  have slopeLimit:= (sourcePhotonSheetJacobi_hasDerivAt e.val c n).tendsto_slope
  have poleReal : Tendsto (fun s : ℝ=>(s-c) • sourceWholePhotonGreen e.val s n) (𝓝[≠] c) (𝓝 R) := by
    simpa only [real_smul_matrix] using pole
  have returning := ((tendsto_const_nhds (x:=R)).mul slopeLimit).mul poleReal
  have nullReturning:=(tendsto_const_nhds (x:=R) (f:=𝓝[≠] c)).mul ((tendsto_const_nhds (x:=(1 : Matrix (Fin 289) (Fin 289) ℂ))).sub
    (((sourcePhotonNullSource_continuous e.val n).tendsto c).mono_left nhdsWithin_le_nhds))
  have annihilate : R*(1-sourcePhotonNullSource e.val c n)=R := by
    rw [mul_sub,mul_one,sourceWholePhotonResidue_null,sub_zero]
  rw [annihilate] at nullReturning
  apply tendsto_nhds_unique returning
  apply nullReturning.congr'
  filter_upwards [equations,self_mem_nhdsWithin] with s original different
  have nonzero : s-c≠0 := sub_ne_zero.mpr different
  symm
  change R * slope K c s * ((s-c) • sourceWholePhotonGreen e.val s n)=R*(1-sourcePhotonNullSource e.val s n)
  rw [slope_def_module,mul_smul_comm,mul_smul_comm,smul_mul_assoc,smul_smul,mul_inv_cancel₀ nonzero,one_smul]
  rw [mul_sub,homogeneous.1,sub_zero,mul_assoc,original.1]

/-- The physical-frequency pencil retains the original frequency ray with its source scale conversion. -/
def sourcePhotonFrequencyJacobi (epsilon omega : ℝ) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  originalJacobi (frequencyRay epsilon (omega/epsilon^2) n)

def sourcePhotonFrequencyJacobiJet (epsilon omega : ℝ) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  deriv (fun w : ℝ=>sourcePhotonFrequencyJacobi epsilon w n) omega

def sourceWholePhotonFrequencyResidue (epsilon s : ℝ) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  (epsilon^2:ℝ) • sourceWholePhotonResidue epsilon s n

theorem sourcePhotonFrequencyJacobi_hasDerivAt (e : scaleDomain) (s : ℝ) (n : PhysicalMomentum) :
    HasDerivAt (fun w : ℝ=>sourcePhotonFrequencyJacobi e.val w n)
      ((e.val^2)⁻¹ • sourcePhotonSheetJacobiJet e.val s n) (sourceFrequency e.val s) := by
  have nonzero : e.val^2≠0 := pow_ne_zero _ (ne_of_gt e.property.1)
  have point : s=sourceFrequency e.val s/e.val^2 := by
    unfold sourceFrequency
    field_simp [ne_of_gt e.property.1]
  have chain := (sourcePhotonSheetJacobi_hasDerivAt e.val s n).scomp_of_eq
    (sourceFrequency e.val s) ((hasDerivAt_id (sourceFrequency e.val s)).div_const (e.val^2)) point
  simpa only [Function.comp_def,id_eq,one_div,sourcePhotonFrequencyJacobi] using chain

/-- The two frequency-residue factors and the inverse derivative scale leave exactly one original epsilon-squared factor. -/
theorem sourceWholePhotonResidue_frequencyFlux (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *
        sourcePhotonFrequencyJacobiJet e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n *
        sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n =
      sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceWholePhotonResidue_sheetFlux branch n unit] with e flux
  have nonzero : e.val^2≠0 := pow_ne_zero _ (ne_of_gt e.property.1)
  have derivative := (sourcePhotonFrequencyJacobi_hasDerivAt e (sourceSheet branch n unit e.val) n).deriv
  unfold sourcePhotonFrequencyJacobiJet sourceWholePhotonFrequencyResidue
  rw [derivative]
  have cancel (R J : Matrix (Fin 289) (Fin 289) ℂ) :
      ((e.val^2) • R)*((e.val^2)⁻¹ • J)=R*J := by
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,mul_inv_cancel₀ nonzero,one_smul]
  rw [cancel,mul_smul_comm,flux]

end LowEnergy.PreparationPhysicalNativePhotonFluxReturn
