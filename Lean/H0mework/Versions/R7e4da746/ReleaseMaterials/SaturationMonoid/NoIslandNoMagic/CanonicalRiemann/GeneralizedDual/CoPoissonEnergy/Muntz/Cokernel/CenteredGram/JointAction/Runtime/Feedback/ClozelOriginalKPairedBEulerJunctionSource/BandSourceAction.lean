import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKContactClosureSourceData
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFiniteWriteback

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedBEulerJunctionSource.BandSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "p" => junctionPoint
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier

-- These are the already paid branch regularity and native L² integral proofs.
elab "paidProof%" name:ident : term => do
  let head := `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource
  let tail := `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPairedBEulerJunctionSource
  pure (Lean.mkConst (((Lean.Name.num head 0).append tail).append name.getId))

private def branchDensity (f df g dg : ℝ → ℂ) (x : ℝ) : ℂ :=
 star ((x:ℂ)*df x+(1/2:ℂ)*f x)*g x+
 star (f x)*((x:ℂ)*dg x+(1/2:ℂ)*g x)

private theorem branch_product_derivative (f df g dg : ℝ → ℂ) (x : ℝ)
 (hf : HasDerivAt f (df x) x) (hg : HasDerivAt g (dg x) x) :
 HasDerivAt (fun y : ℝ => (y:ℂ)*star (f y)*g y)
  (branchDensity f df g dg x) x := by
 have cast : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := by
  simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using!
   (Complex.ofRealCLM.hasDerivAt (x:=x))
 have sx : star (x:ℂ)=(x:ℂ) := Complex.conj_ofReal x
 convert! (cast.mul hf.star).mul hg using 1
 simp only [branchDensity,star_add,star_mul,star_div₀,star_one,star_ofNat,sx,Pi.mul_apply,one_mul]
 ring

private theorem branch_integral (a b : ℝ) (ordered : a ≤ b) (f df g dg : ℝ → ℂ)
 (cf : ContinuousOn f (Icc a b)) (cdf : ContinuousOn df (Icc a b))
 (cg : ContinuousOn g (Icc a b)) (cdg : ContinuousOn dg (Icc a b))
 (hf : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
 (hg : ∀ x ∈ Ioo a b, HasDerivAt g (dg x) x) :
 (∫ x : ℝ in a..b, branchDensity f df g dg x)=
  (b:ℂ)*star (f b)*g b-(a:ℂ)*star (f a)*g a := by
 have fbulk : ContinuousOn (fun x : ℝ => (x:ℂ)*df x+(1/2:ℂ)*f x) (Icc a b) :=
  (Complex.continuous_ofReal.continuousOn.mul cdf).add (continuousOn_const.mul cf)
 have gbulk : ContinuousOn (fun x : ℝ => (x:ℂ)*dg x+(1/2:ℂ)*g x) (Icc a b) :=
  (Complex.continuous_ofReal.continuousOn.mul cdg).add (continuousOn_const.mul cg)
 have regular : ContinuousOn (branchDensity f df g dg) (Icc a b) :=
  (fbulk.star.mul cg).add (cf.star.mul gbulk)
 have integrable : IntervalIntegrable (branchDensity f df g dg) volume a b :=
  ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le ordered] using regular)
 exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ordered
  ((Complex.continuous_ofReal.continuousOn.mul cf.star).mul cg)
  (fun x hx => branch_product_derivative f df g dg x (hf x hx) (hg x hx)) integrable

private def matrixDensity (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) (x:ℝ) : ℂ :=
 star (sourceBulkRaw c i x)*sourceRaw c j x+
 star (sourceRaw c i x)*sourceBulkRaw c j x

private theorem matrix_density_integrable (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) :
 IntervalIntegrable (matrixDensity c i j) volume (-q) q := by
 have first := (paidProof% native_pair_integrable) (sourceBulk c i) (sourceCorrection c j:Hq)
  _ _ (source_bulk_read c i) (source_correction_read c j)
 have second := (paidProof% native_pair_integrable) (sourceCorrection c i:Hq) (sourceBulk c j)
  _ _ (source_correction_read c i) (source_bulk_read c j)
 exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num:-q≤q)).mpr (first.add second)

private theorem matrix_density_even (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) (x:ℝ) :
 matrixDensity c i j (-x)=matrixDensity c i j x := by
 simp only [matrixDensity,sourceBulkRaw,sourceRaw,TwoPieceFourierAction.bulkRaw,
  TwoPieceFourierAction.pieceRaw,abs_neg]

private theorem matrix_positive_green (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) :
 (∫ x : ℝ in 0..q, matrixDensity c i j x)=
  (q:ℂ)*star (sourceTrace c i)*sourceTrace c j-
   (p:ℂ)*(star (sourceOuterRaw c i p)*sourceOuterRaw c j p-
     star (sourceInnerRaw c i p)*sourceInnerRaw c j p) := by
 have whole := matrix_density_integrable c i j
 have first : IntervalIntegrable (matrixDensity c i j) volume 0 p :=
  whole.mono_set (by
   rw [uIcc_of_le junctionPoint_bounds.1.le,uIcc_of_le (by norm_num:-q≤q)]
   intro x hx
   exact ⟨by linarith [hx.1],hx.2.trans junctionPoint_bounds.2.le⟩)
 have second : IntervalIntegrable (matrixDensity c i j) volume p q :=
  whole.mono_set (by
   rw [uIcc_of_le junctionPoint_bounds.2.le,uIcc_of_le (by norm_num:-q≤q)]
   intro x hx
   exact ⟨by linarith [hx.1,junctionPoint_bounds.1],hx.2⟩)
 have firstEq : EqOn (matrixDensity c i j)
   (branchDensity (sourceInnerRaw c i) (sourceInnerSlope c i)
     (sourceInnerRaw c j) (sourceInnerSlope c j)) (uIoo 0 p) := by
  rw [uIoo_of_le junctionPoint_bounds.1.le]
  intro x hx
  simp only [matrixDensity,sourceBulkRaw,sourceRaw,TwoPieceFourierAction.bulkRaw,
   TwoPieceFourierAction.pieceRaw,abs_of_pos hx.1,if_pos hx.2.le,branchDensity]
 have secondEq : EqOn (matrixDensity c i j)
   (branchDensity (sourceOuterRaw c i) (sourceOuterSlope c i)
     (sourceOuterRaw c j) (sourceOuterSlope c j)) (uIoo p q) := by
  rw [uIoo_of_le junctionPoint_bounds.2.le]
  intro x hx
  have positive : 0<x := junctionPoint_bounds.1.trans hx.1
  simp only [matrixDensity,sourceBulkRaw,sourceRaw,TwoPieceFourierAction.bulkRaw,
   TwoPieceFourierAction.pieceRaw,abs_of_pos positive,if_neg hx.1.not_ge,branchDensity]
 have inner := branch_integral 0 p junctionPoint_bounds.1.le
  (sourceInnerRaw c i) (sourceInnerSlope c i) (sourceInnerRaw c j) (sourceInnerSlope c j)
  ((paidProof% source_inner_continuousOn) c i) ((paidProof% source_inner_slope_continuousOn) c i)
  ((paidProof% source_inner_continuousOn) c j) ((paidProof% source_inner_slope_continuousOn) c j)
  (fun x _ => (paidProof% source_inner_hasDerivAt) c i x)
  (fun x _ => (paidProof% source_inner_hasDerivAt) c j x)
 have outer := branch_integral p q junctionPoint_bounds.2.le
  (sourceOuterRaw c i) (sourceOuterSlope c i) (sourceOuterRaw c j) (sourceOuterSlope c j)
  ((paidProof% source_outer_continuousOn) c i) ((paidProof% source_outer_slope_continuousOn) c i)
  ((paidProof% source_outer_continuousOn) c j) ((paidProof% source_outer_slope_continuousOn) c j)
  (fun x hx => (paidProof% source_outer_hasDerivAt) c i x hx.1)
  (fun x hx => (paidProof% source_outer_hasDerivAt) c j x hx.1)
 rw [← intervalIntegral.integral_add_adjacent_intervals first second,
  intervalIntegral.integral_congr_uIoo firstEq,intervalIntegral.integral_congr_uIoo secondEq]
 simp only [Complex.ofReal_zero,zero_mul,sub_zero] at inner
 unfold sourceTrace
 linear_combination inner+outer

/-- Both actual junction traces contribute; no single-sided delta product is substituted. -/
def chargeGram (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) : ℂ :=
 (2*q:ℂ)*star (sourceTrace c i)*sourceTrace c j-
 (2*(p:ℂ))*(star (sourceOuterRaw c i p)*sourceOuterRaw c j p-
  star (sourceInnerRaw c i p)*sourceInnerRaw c j p)

private theorem matrix_full_green (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) :
 (∫ x : ℝ in (-q)..q, matrixDensity c i j x)=chargeGram c i j := by
 have full := matrix_density_integrable c i j
 have negative := full.mono_set (show uIcc (-q) 0 ⊆ uIcc (-q) q by
  rw [uIcc_of_le (by norm_num:-q≤(0:ℝ)),uIcc_of_le (by norm_num:-q≤q)]
  exact Icc_subset_Icc le_rfl (by norm_num))
 have positive := full.mono_set (show uIcc 0 q ⊆ uIcc (-q) q by
  rw [uIcc_of_le (by norm_num:(0:ℝ)≤q),uIcc_of_le (by norm_num:-q≤q)]
  exact Icc_subset_Icc (by norm_num) le_rfl)
 have reflection := intervalIntegral.integral_comp_neg (f:=matrixDensity c i j) (a:=0) (b:=q)
 simp only [matrix_density_even,neg_zero] at reflection
 rw [← intervalIntegral.integral_add_adjacent_intervals negative positive,← reflection]
 unfold chargeGram
 linear_combination 2*matrix_positive_green c i j

/-- The actual paired B corrections generate their complete complex Green matrix. -/
theorem source_correction_green (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) :
 inner ℂ (sourceEulerBulk c i) (sourceCorrection c j)+
  inner ℂ (sourceCorrection c i) (sourceEulerBulk c j)=chargeGram c i j := by
 have first := (paidProof% native_pair_integrable) (sourceBulk c i) (sourceCorrection c j:Hq)
  _ _ (source_bulk_read c i) (source_correction_read c j)
 have second := (paidProof% native_pair_integrable) (sourceCorrection c i:Hq) (sourceBulk c j)
  _ _ (source_correction_read c i) (source_bulk_read c j)
 have int0 : IntervalIntegrable (fun x:ℝ => star (sourceBulkRaw c i x)*sourceRaw c j x) volume (-q) q :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num:-q≤q)).mpr first
 have int1 : IntervalIntegrable (fun x:ℝ => star (sourceRaw c i x)*sourceBulkRaw c j x) volume (-q) q :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num:-q≤q)).mpr second
 change inner ℂ (Constructor.zeroMean (sourceBulk c i)) (sourceCorrection c j)+
  inner ℂ (sourceCorrection c i) (Constructor.zeroMean (sourceBulk c j))=_
 unfold Constructor.zeroMean
 rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
 rw [(paidProof% native_pair_read) _ _ _ _ (source_bulk_read c i) (source_correction_read c j),
  (paidProof% native_pair_read) _ _ _ _ (source_correction_read c i) (source_bulk_read c j),
  ← intervalIntegral.integral_add int0 int1]
 exact matrix_full_green c i j


private theorem source_force_action (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
 sourceEulerBulk c i+PsiDrive.sourceRate c i • sourceCorrection c i=sourceForce c i := by
 have actual := PsiDrive.source_B_Psi_action c
 fin_cases i
 · exact actual.1
 · change sourceEulerBulk c 1+(-(star c.value-1/2)) • sourceSecond c=_
   rw [neg_smul,← sub_eq_add_neg]
   exact actual.2

/-- All four phase-sensitive source pairings are generated by the original B/Psi action. -/
theorem paired_source_matrix_action (c:BurnolCompletedMellinCoordinate) (i j:Fin 2) :
 (star (PsiDrive.sourceRate c i)+PsiDrive.sourceRate c j)*
   inner ℂ (sourceCorrection c i) (sourceCorrection c j)=
  inner ℂ (sourceForce c i) (sourceCorrection c j)+
  inner ℂ (sourceCorrection c i) (sourceForce c j)-chargeGram c i j := by
 have left := congrArg (fun value:M => inner ℂ value (sourceCorrection c j)) (source_force_action c i)
 have right := congrArg (fun value:M => inner ℂ (sourceCorrection c i) value) (source_force_action c j)
 rw [inner_add_left,inner_smul_left,starRingEnd_apply] at left
 rw [inner_add_right,inner_smul_right] at right
 linear_combination left+right-source_correction_green c i j

/-- The scalar source norm imbalance retains the complete forcing and both endpoint/internal charges. -/
theorem paired_source_energy_action (c:BurnolCompletedMellinCoordinate) :
 (c.value+star c.value-1)*
  (inner ℂ (sourceFirst c) (sourceFirst c)-inner ℂ (sourceSecond c) (sourceSecond c))=
 inner ℂ (sourceForce c 0) (sourceFirst c)+inner ℂ (sourceFirst c) (sourceForce c 0)+
 inner ℂ (sourceForce c 1) (sourceSecond c)+inner ℂ (sourceSecond c) (sourceForce c 1)-
  (chargeGram c 0 0+chargeGram c 1 1) := by
 have first := paired_source_matrix_action c 0 0
 have second := paired_source_matrix_action c 1 1
 simp only [PsiDrive.sourceRate,sourceCorrection,Matrix.cons_val_zero,Matrix.cons_val_one,
  star_neg,star_sub,star_star,star_div₀,star_one,star_ofNat] at first second
 linear_combination first+second

end OriginalKPairedBEulerJunctionSource.BandSourceAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
