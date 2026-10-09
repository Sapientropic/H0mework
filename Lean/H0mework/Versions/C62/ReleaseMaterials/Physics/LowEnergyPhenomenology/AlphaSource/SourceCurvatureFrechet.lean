import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteCurvatureChannels

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCurvatureSheetLimit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective PreparationVacuumMixedControl
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumFullSlowFieldResponse PreparationVacuumNativeSlowCoupling PreparationVacuumNativePoleTensor
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumFieldConstraintResponse
open PreparationPhysicalFinitePoleCurvatureReturn PreparationPhysicalNormalizedFullField
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumSoftPoleSelection CanonicalGradedSpatialSource
open Filter Set
open scoped BigOperators Matrix Topology ContDiff Matrix.Norms.Operator
attribute [local irreducible] sourceNativeFrame fullKernelFrame fullInverse sourceChargedNativeFrameJet

private def sourceEntry (i j : Fin 289) : (Matrix (Fin 289) (Fin 289) ℂ)→L[ℝ]ℂ :=
  ({ toFun:=fun A=>A i j
     map_add':=fun _ _=>rfl
     map_smul':=fun _ _=>rfl } : (Matrix (Fin 289) (Fin 289) ℂ)→ₗ[ℝ]ℂ).toContinuousLinearMap

private theorem sourcePolynomial_smooth (terms : List SourceTerm) : ContDiff ℝ ∞ (sourceMatrix terms) := by
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

/-- Smoothness is paid by the actual full polynomial and original complement inverse at its generated regular origin. -/
theorem sourceNativeFrame_smooth : ContDiffAt ℝ ∞ sourceNativeFrame (0:Fin 4→ℂ) := by
  have O : ContDiffAt ℝ ∞ originalChange (0:Fin 4→ℂ):=(sourcePolynomial_smooth originalChangeTerms).contDiffAt
  have K : ContDiffAt ℝ ∞ activeKernel (0:Fin 4→ℂ):=(sourcePolynomial_smooth activeTerms).contDiffAt
  have result : ContDiffAt ℝ ∞
      (fun p : Fin 4→ℂ=>originalChange p*(fullKernelFrame-unrestrictedGreen p*activeKernel p*fullKernelFrame)*slowFastFrame) 0 :=
    (O.mul (contDiffAt_const.sub ((unrestrictedGreen_smooth_origin.mul K).mul contDiffAt_const))).mul contDiffAt_const
  change ContDiffAt ℝ ∞ (fun p : Fin 4→ℂ=>sourceNativeFrame p) 0
  simpa only [sourceNativeFrame,rawEffectiveFrame,mul_assoc] using result

private theorem sourceReader_entry_smooth (r : Fin 36) (c : Fin 289) :
    ContDiff ℝ ∞ (fun p : Fin 4→ℂ=>originalReader36 p r c) := by
  have polynomial:= (sourceEntry (Fin.castLE (by decide) r) c).contDiff.comp
    (sourcePolynomial_smooth sourceCurvatureSlopeTerms)
  have returned : (fun p : Fin 4→ℂ=>originalReader36 p r c)=
      fun p=>sourceEntry (Fin.castLE (by decide) r) c (sourceMatrix sourceCurvatureSlopeTerms p)+originalReader36 0 r c := by
    funext p
    change _=sourceMatrix sourceCurvatureSlopeTerms p (Fin.castLE (by decide) r) c+_
    rw [sourceCurvatureSlope_generated]
    ring
  rw [returned]
  exact polynomial.add contDiff_const

/-- This is the complete ordinary-source curvature field, before cofactor selection or preparation. -/
def sourceCurvatureFrame (p : Fin 4→ℂ) : Matrix (Fin 36) (Fin 289) ℂ :=
  fun r c=>∑k : Fin 289,originalReader36 p r k*sourceNativeFrame p k c

theorem sourceCurvatureFrame_smooth (r : Fin 36) (c : Fin 289) :
    ContDiffAt ℝ ∞ (fun p=>sourceCurvatureFrame p r c) (0:Fin 4→ℂ) := by
  change ContDiffAt ℝ ∞ (fun p=>∑k : Fin 289,originalReader36 p r k*sourceNativeFrame p k c) 0
  apply ContDiffAt.sum
  intro k _
  have entry := (sourceEntry k c).contDiff.contDiffAt.comp (0:Fin 4→ℂ) sourceNativeFrame_smooth
  exact (sourceReader_entry_smooth r k).contDiffAt.mul entry

/-- No background curvature is silently left in the subsequent divided response. -/
theorem sourceCurvatureFrame_origin (r : Fin 36) (c : Fin 289) : sourceCurvatureFrame 0 r c=0 := by
  have original:=sourceCurvatureOrigin_zero (slowFastFrame*ᵥPi.single c (1:ℂ))
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,Matrix.mulVec_single_one] at original
  rw [Matrix.mul_assoc] at original
  have row:=congrFun original r
  simpa only [sourceCurvatureFrame,sourceChargedNativeFrame_origin,Matrix.col_apply,Pi.zero_apply,mul_assoc,Matrix.mul_apply] using row

/-- The entire first matrix is generated by the actual inverse/frame, including its temporal fast column. -/
theorem sourceCurvatureJetMatrix (v : Fin 4→ℂ) (r : Fin 36) (c : Fin 289) :
    sourceMatrix (sourceSlowCurvatureTerms++sourceFastCurvatureTerms) v (Fin.castLE (by decide) r) c=
      (∑k : Fin 289,(originalReader36 v r k-originalReader36 0 r k)*(fullNativeOrigin*slowFastFrame) k c)+
        ∑k : Fin 289,originalReader36 0 r k*sourceChargedNativeFrameJet v k c := by
  have energy:=sourceEnergyChannelMatrix_generated v
  change sourceMatrix sourceEnergyChannelTerms v=sourceChargedNativeFrameJet v*
    projectionMatrix (fun j : Fin 289=>decide (j.val<3)) at energy
  rw [sourceMatrix_append,sourceSlowCurvature_generated,sourceFastCurvature_generated,energy]
  have algebra {R : Type} [Ring R] (S O F C J P : R) :
      S*O*F+C*(J*P)+C*J*(1-P)=S*(O*F)+C*J := by noncomm_ring
  have combined:=algebra (sourceMatrix sourceCurvatureSlopeTerms v) fullNativeOrigin slowFastFrame
    sourceCurvatureOriginMatrix (sourceChargedNativeFrameJet v)
    (projectionMatrix (fun j : Fin 289=>decide (j.val<3)))
  rw [combined]
  simp only [Matrix.add_apply,Matrix.mul_apply,sourceCurvatureSlope_generated,
    sourceCurvatureOrigin_generated]

private theorem sourceReader_ray (v : Fin 4→ℂ) (r : Fin 36) (c : Fin 289) :
    HasDerivAt (fun d : ℝ=>originalReader36 ((d:ℂ) • v) r c)
      (originalReader36 v r c-originalReader36 0 r c) 0 := by
  have scalar : HasDerivAt (fun d : ℝ=>(d:ℂ)) (1:ℂ) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).ofReal_comp
  have generated:= (scalar.mul_const (originalReader36 v r c-originalReader36 0 r c)).const_add (originalReader36 0 r c)
  have expression : (fun d : ℝ=>originalReader36 ((d:ℂ) • v) r c)=
      fun d : ℝ=>originalReader36 0 r c+(d:ℂ)*(originalReader36 v r c-originalReader36 0 r c) := by
    funext d
    have row:=congrFun (congrFun (sourceCurvatureReader_affine v (d:ℂ)) r) c
    simpa only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul] using row
  rw [expression]
  simpa only [one_mul] using generated

/-- The generated seven-term matrix is the derivative of the actual full curvature field. -/
theorem sourceCurvatureFrame_derivative (v : Fin 4→ℂ) (r : Fin 36) (c : Fin 289) :
    HasDerivAt (fun d : ℝ=>sourceCurvatureFrame ((d:ℂ) • v) r c)
      (sourceMatrix (sourceSlowCurvatureTerms++sourceFastCurvatureTerms) v (Fin.castLE (by decide) r) c) 0 := by
  have pieces (k : Fin 289) : HasDerivAt
      (fun d : ℝ=>originalReader36 ((d:ℂ) • v) r k*sourceNativeFrame ((d:ℂ) • v) k c)
      ((originalReader36 v r k-originalReader36 0 r k)*(fullNativeOrigin*slowFastFrame) k c+
        originalReader36 0 r k*sourceChargedNativeFrameJet v k c) 0 := by
    have frame : HasDerivAt (fun d : ℝ=>sourceNativeFrame ((d:ℂ) • v) k c)
        (sourceChargedNativeFrameJet v k c) 0 :=
      (sourceEntry k c).hasFDerivAt.comp_hasDerivAt (0:ℝ) (sourceChargedNativeFrame_derivative v)
    have result:= (sourceReader_ray v r k).mul frame
    simp only [zero_smul,Complex.ofReal_zero,sourceChargedNativeFrame_origin] at result
    convert result using 1 <;> rfl
  have total:=HasDerivAt.fun_sum (fun k (_ : k∈Finset.univ)=>pieces k)
  rw [sourceCurvatureJetMatrix]
  simpa only [sourceCurvatureFrame,Matrix.mul_apply,Matrix.add_apply,Matrix.sub_apply,Finset.sum_add_distrib] using total

/-- Frechet control, not an assumed uniform price, is generated for the moving physical ray. -/
theorem sourceCurvatureFrame_frechet (v : Fin 4→ℂ) (r : Fin 36) (c : Fin 289) :
    (fderiv ℝ (fun p=>sourceCurvatureFrame p r c) 0) v=
      sourceMatrix (sourceSlowCurvatureTerms++sourceFastCurvatureTerms) v (Fin.castLE (by decide) r) c := by
  have ray : HasDerivAt (fun d : ℝ=>(d:ℂ) • v) v 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).ofReal_comp.smul_const v
  have derivative:=((sourceCurvatureFrame_smooth r c).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    (0:ℝ) ray (show (0:Fin 4→ℂ)=(0:ℂ) • v by simp)
  exact derivative.unique (sourceCurvatureFrame_derivative v r c)

end LowEnergy.PreparationPhysicalCurvatureSheetLimit
