import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePhotonScatteringPreparation

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePhotonScatteringSheetReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumNativePoleTensor PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalQuantumLockedCharge
open GaussComposite.PhysicalFullFieldScattering Electromagnetic.CanonicalCoframe
open FullQuantum FullSpace Filter
open scoped InnerProductSpace BigOperators Matrix Topology
attribute [local irreducible] actualSheetField actualSheetResidue actualFrequencyResidue
  complexCoefficients complexFrequencyCoefficients realReaderCoefficients realMixedCoefficients

private def preparedFieldPair (sideL edgeL sideR edgeR : Fin 2) (shift : Fin 3→ℝ) (time age : ℝ)
    (fields : FourFields) : ℂ × ℂ :=
  sourcePreparedScatteringPair sideL edgeL sideR edgeR
    (originalTransferPair fields.1.1 fields.1.2) (originalTransferPair fields.2.1 fields.2.2) shift time age

private theorem preparedFieldPair_continuous (sideL edgeL sideR edgeR : Fin 2) (shift : Fin 3→ℝ) (time age : ℝ) :
    Continuous (preparedFieldPair sideL edgeL sideR edgeR shift time age) := by
  change Continuous (fun fields : FourFields=>preparedFieldPair sideL edgeL sideR edgeR shift time age fields)
  simp only [preparedFieldPair,sourcePreparedScatteringPair,sourceActualScatteringRead_source]
  exact (continuous_const.inner ((fieldTwoTimeKernel_joint_cts shift time age).clm_apply continuous_const)).prodMk
    (continuous_const.inner ((fieldMixedContact_joint_cts time).clm_apply continuous_const))

private theorem preparedFieldPair_scale (sideL edgeL sideR edgeR : Fin 2) (shift : Fin 3→ℝ) (time age r : ℝ)
    (Ap An Bp Bn : Fin 289→ℂ) :
    preparedFieldPair sideL edgeL sideR edgeR shift time age
      (((r:ℂ) • Ap,(r:ℂ) • An),((r:ℂ) • Bp,(r:ℂ) • Bn))=
        (r:ℂ)^2 • preparedFieldPair sideL edgeL sideR edgeR shift time age ((Ap,An),(Bp,Bn)) := by
  simp only [preparedFieldPair,sourcePreparedScatteringPair,fieldTwoTimeKernel_smul,fieldMixedContact_smul,
    sourceActualScatteringRead_source,Prod.smul_mk,smul_apply,inner_smul_right,smul_eq_mul]

/-- Both determinant-generated propagating branches feed the complete same-preparation scattering pole. -/
theorem sourcePhotonScattering_sheetPole (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : SourcePhotonLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (time age : ℝ) :
    ∀ᶠ e in scaleApproach,Tendsto
      (fun s : ℝ=>((s-sourceSheet branch n unit e.val:ℝ):ℂ)^2 •
        sourcePhotonScatteringPair sideL edgeL sideR edgeR Ap An Bp Bn e.val s n time age)
      (𝓝[≠] (sourceSheet branch n unit e.val))
      (𝓝 (sourcePhotonScatteringResidue sideL edgeL sideR edgeR Ap An Bp Bn e.val
        (sourceSheet branch n unit e.val) n time age)) := by
  have leg (a : SourcePhotonLeg) := actualSheetField_residue a.q branch n a.momentum unit
    (sourceChargedRestIndex a.sideL a.edgeL) (sourceChargedRestIndex a.sideR a.edgeR) a.window
  filter_upwards [leg Ap,leg An,leg Bp,leg Bn] with e ap an bp bn
  have fields:=(ap.prodMk_nhds an).prodMk_nhds (bp.prodMk_nhds bn)
  have returned:=(preparedFieldPair_continuous sideL edgeL sideR edgeR (e.val^2 • n) time age).tendsto
    ((sourcePhotonResidue Ap e.val (sourceSheet branch n unit e.val) n,
      sourcePhotonResidue An e.val (sourceSheet branch n unit e.val) n),
     (sourcePhotonResidue Bp e.val (sourceSheet branch n unit e.val) n,
      sourcePhotonResidue Bn e.val (sourceSheet branch n unit e.val) n)) |>.comp fields
  simp only [Function.comp_def,preparedFieldPair_scale] at returned
  simpa only [preparedFieldPair,sourcePhotonField,sourcePhotonResidue,
    sourcePhotonScatteringPair,sourcePhotonScatteringResidue,sourcePhotonTransfer,sourcePhotonResidueTransfer] using returned

/-- This residue uses the original Fourier frequency, including its source epsilon-squared change of variable. -/
theorem sourcePhotonScattering_frequencyPole (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : SourcePhotonLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (time age : ℝ) :
    ∀ᶠ e in scaleApproach,Tendsto
      (fun omega : ℝ=>((omega-sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ)^2 •
        sourcePhotonScatteringPair sideL edgeL sideR edgeR Ap An Bp Bn e.val (omega/e.val^2) n time age)
      (𝓝[≠] (sourceFrequency e.val (sourceSheet branch n unit e.val)))
      (𝓝 (sourcePhotonScatteringFrequencyResidue sideL edgeL sideR edgeR Ap An Bp Bn e.val
        (sourceSheet branch n unit e.val) n time age)) := by
  have leg (a : SourcePhotonLeg) := actualSheetField_frequency_residue a.q branch n a.momentum unit
    (sourceChargedRestIndex a.sideL a.edgeL) (sourceChargedRestIndex a.sideR a.edgeR) a.window
  filter_upwards [leg Ap,leg An,leg Bp,leg Bn] with e ap an bp bn
  have fields:=(ap.prodMk_nhds an).prodMk_nhds (bp.prodMk_nhds bn)
  have returned:=(preparedFieldPair_continuous sideL edgeL sideR edgeR (e.val^2 • n) time age).tendsto
    ((sourcePhotonFrequencyResidue Ap e.val (sourceSheet branch n unit e.val) n,
      sourcePhotonFrequencyResidue An e.val (sourceSheet branch n unit e.val) n),
     (sourcePhotonFrequencyResidue Bp e.val (sourceSheet branch n unit e.val) n,
      sourcePhotonFrequencyResidue Bn e.val (sourceSheet branch n unit e.val) n)) |>.comp fields
  simp only [Function.comp_def,preparedFieldPair_scale] at returned
  simpa only [preparedFieldPair,sourcePhotonField,sourcePhotonFrequencyResidue,
    sourcePhotonScatteringPair,sourcePhotonScatteringFrequencyResidue,sourcePhotonTransfer,
    sourcePhotonFrequencyResidueTransfer] using returned

/-- Two actual field insertions pay the original frequency factor epsilon to the fourth, exactly once. -/
theorem sourcePhotonScattering_frequencyScale (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) :
    sourcePhotonScatteringFrequencyResidue sideL edgeL sideR edgeR Ap An Bp Bn epsilon s n time age=
      (epsilon:ℂ)^4 • sourcePhotonScatteringResidue sideL edgeL sideR edgeR Ap An Bp Bn epsilon s n time age := by
  have scaled:=preparedFieldPair_scale sideL edgeL sideR edgeR (epsilon^2 • n) time age (epsilon^2)
    (sourcePhotonResidue Ap epsilon s n) (sourcePhotonResidue An epsilon s n)
    (sourcePhotonResidue Bp epsilon s n) (sourcePhotonResidue Bn epsilon s n)
  rw [Complex.ofReal_pow,←pow_mul] at scaled
  simpa only [sourcePhotonScatteringFrequencyResidue,sourcePhotonFrequencyResidueTransfer,
    sourcePhotonFrequencyResidue,actualFrequencyResidue,sourcePhotonResidue,preparedFieldPair,
    sourcePhotonScatteringResidue,sourcePhotonResidueTransfer,Complex.ofReal_pow] using scaled

end LowEnergy.PreparationPhysicalNativePhotonScatteringSheetReturn
