import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePhotonScatteringResidue

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePhotonScatteringSheetReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumOriginalGreenFeedback PreparationVacuumElectromagneticIdentity
open PreparationVacuumNativePoleTensor PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalQuantumLockedCharge
open SourcePropagationNativeActionHessian Filter Set
open scoped BigOperators Matrix Topology
attribute [local irreducible] originalJacobi originalChange originalInverse originalRowLift originalReadback
  actualSheetField actualSheetResidue sourcePhotonField sourcePhotonResidue

private theorem source_matrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms) := by
  induction terms with
  | nil=>exact continuous_const
  | cons a rest ih=>
    have term : Continuous a.matrix := by
      apply continuous_matrix
      intro i j
      simp only [SourceTerm.matrix,Matrix.single_apply]
      split_ifs
      · unfold Powers.value
        fun_prop
      · exact continuous_const
    exact term.add ih

private theorem ray_continuous (epsilon : ℝ) (n : PhysicalMomentum) :
    Continuous (fun s : ℝ=>frequencyRay epsilon s n) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · change Continuous (fun s : ℝ=>-Complex.I*((s*epsilon^2:ℝ):ℂ))
    fun_prop
  · exact continuous_const

/-- The original full forcing includes the null-projected initial/final cosource through its exact Ward return. -/
private def photonForcing (leg : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  let current:=sheetCurrent leg.q epsilon s n leg.momentum
    (sourceChargedRestIndex leg.sideL leg.edgeL) (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window
  current-originalRowLift (frequencyRay epsilon s n)*ᵥ
    (nullProjection*ᵥ(originalReadback (frequencyRay epsilon s n)*ᵥcurrent))

private theorem forcing_continuous (leg : SourcePhotonLeg) (epsilon : ℝ) (n : PhysicalMomentum) :
    Continuous (fun s=>photonForcing leg epsilon s n) := by
  have current:=sheetCurrent_continuous leg.q epsilon n leg.momentum
    (sourceChargedRestIndex leg.sideL leg.edgeL) (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window
  have row : Continuous (fun s=>originalRowLift (frequencyRay epsilon s n)) := by
    simpa only [originalRowLift,originalInverse,Function.comp_def,Pi.neg_apply] using
      ((source_matrix_continuous originalInverseTerms).comp (ray_continuous epsilon n).neg).matrix_transpose
  have read : Continuous (fun s=>originalReadback (frequencyRay epsilon s n)) := by
    simpa only [originalReadback,originalChange,Function.comp_def,Pi.neg_apply] using
      ((source_matrix_continuous originalChangeTerms).comp (ray_continuous epsilon n).neg).matrix_transpose
  exact current.sub (row.matrix_mulVec (continuous_const.matrix_mulVec (read.matrix_mulVec current)))

/-- The actual residue is a complete original homogeneous mode, generated from the full forced equation and Ward boundary. -/
theorem sourcePhotonResidue_hessian_zero (leg : SourcePhotonLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      nativeFourierHessian nativeHessian (frequencyRay e.val (sourceSheet branch n unit e.val) n)*ᵥ
        sourcePhotonResidue leg e.val (sourceSheet branch n unit e.val) n=0 := by
  have residue:=actualSheetField_residue leg.q branch n leg.momentum unit
    (sourceChargedRestIndex leg.sideL leg.edgeL) (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window
  filter_upwards [sourcePhoton_fieldWhole leg branch n unit,residue] with e whole limit
  let center:=sourceSheet branch n unit e.val
  have matrix : Continuous (fun s=>originalJacobi (frequencyRay e.val s n)) := by
    simpa only [originalJacobi,Function.comp_def] using (source_matrix_continuous originalJacobiTerms).comp (ray_continuous e.val n)
  have fieldLimit : Tendsto (fun s : ℝ=>((s-center:ℝ):ℂ) • sourcePhotonField leg e.val s n)
      (𝓝[≠] center) (𝓝 (sourcePhotonResidue leg e.val center n)) := by
    simpa only [sourcePhotonField,sourcePhotonResidue,center] using limit
  have returning := (continuous_fst.matrix_mulVec continuous_snd).tendsto
    (originalJacobi (frequencyRay e.val center n),sourcePhotonResidue leg e.val center n) |>.comp
      (((matrix.tendsto center).mono_left nhdsWithin_le_nhds).prodMk_nhds fieldLimit)
  have scalar : Tendsto (fun s : ℝ=>((s-center:ℝ):ℂ)) (𝓝[≠] center) (𝓝 (0:ℂ)) := by
    have continuous : Continuous (fun s : ℝ=>((s-center:ℝ):ℂ)) := by fun_prop
    simpa only [sub_self,Complex.ofReal_zero] using (continuous.tendsto center).mono_left nhdsWithin_le_nhds
  have forcing:=scalar.smul (((forcing_continuous leg e.val n).tendsto center).mono_left nhdsWithin_le_nhds)
  simp only [zero_smul] at forcing
  have same : (fun s : ℝ=>originalJacobi (frequencyRay e.val s n)*ᵥ
      (((s-center:ℝ):ℂ) • sourcePhotonField leg e.val s n))=ᶠ[𝓝[≠] center]
        (fun s=>((s-center:ℝ):ℂ) • photonForcing leg e.val s n) := by
    filter_upwards [whole] with s original
    rw [nativeActionFourierHessian_original,←sourcePhoton_currentWard leg e.val s n] at original
    rw [Matrix.mulVec_smul,original]
    rfl
  have vanished := forcing.congr' same.symm
  have originalLimit : Tendsto (fun s : ℝ=>originalJacobi (frequencyRay e.val s n)*ᵥ
      (((s-center:ℝ):ℂ) • sourcePhotonField leg e.val s n)) (𝓝[≠] center)
      (𝓝 (originalJacobi (frequencyRay e.val center n)*ᵥsourcePhotonResidue leg e.val center n)) := by
    simpa only [Function.comp_def,sourcePhotonField,sourcePhotonResidue] using returning
  rw [nativeActionFourierHessian_original]
  exact tendsto_nhds_unique originalLimit vanished

/-- The physical-frequency residue inherits the same generated full-field equation, with its epsilon-squared factor intact. -/
theorem sourcePhotonFrequencyResidue_hessian_zero (leg : SourcePhotonLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      nativeFourierHessian nativeHessian (frequencyRay e.val (sourceSheet branch n unit e.val) n)*ᵥ
        sourcePhotonFrequencyResidue leg e.val (sourceSheet branch n unit e.val) n=0 := by
  filter_upwards [sourcePhotonResidue_hessian_zero leg branch n unit] with e generated
  rw [sourcePhotonFrequencyResidue,actualFrequencyResidue,Matrix.mulVec_smul]
  unfold sourcePhotonResidue at generated
  rw [generated,smul_zero]

end LowEnergy.PreparationPhysicalNativePhotonScatteringSheetReturn
