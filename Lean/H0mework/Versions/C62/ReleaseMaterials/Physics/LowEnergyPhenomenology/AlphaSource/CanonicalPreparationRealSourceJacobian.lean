import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPhysicalFullHalfAxis

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumRealReaction
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumActionFieldLift PreparationVacuumFieldCovector
open PreparationVacuumGaugeSourceInjection
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace Interval
local instance : NormedAlgebra ℝ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointResolvent rawReader rawReaderContact

/-- This is the original raw action source, before the field Green acts. -/
def actualSource (q : PhysicalResponsePoint) (age : ℝ) (h : Field289) : Fin 289→ℂ:=
  eulerCovector q.epsilon q.precision q.p q.k q.F q.z q.w age
    q.left q.right q.lc q.ls q.rc q.rs h

theorem actualSource_C2 (q : PhysicalResponsePoint) (age : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) : ContDiffAt ℝ 2 (actualSource q age) 0 :=by
  apply contDiffAt_pi.mpr
  intro i
  have path : ContDiffAt ℝ 2 (fun h : Field289=>(h,age)) 0:=
    contDiffAt_id.prodMk contDiffAt_const
  have kernel:=(jointFiveKernel_C2 (fieldUnit i) q.p q.k q.F q.z q.w hz hw age).comp 0 path
  have pair:=(sourceRead q).restrictScalars ℝ |>.contDiff.contDiffAt.comp 0 kernel
  exact pair.neg

/-- Real-linear: no complex extension of an independent field direction is used. -/
def sourceJacobian (q : PhysicalResponsePoint) (age : ℝ) : Field289→L[ℝ] (Fin 289→ℂ):=
  fderiv ℝ (actualSource q age) 0

theorem sourceJacobian_actual (q : PhysicalResponsePoint) (age : ℝ) (force : Field289)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceJacobian q age force=(fun i=>(sourceSlopeJet q force age i).value) :=by
  have differential:=(actualSource_C2 q age hz hw).differentiableAt (by norm_num) |>.hasFDerivAt
  have generated:=differential.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
  have original:=eulerCovector_generated q.epsilon q.precision force q.p q.k q.F q.z q.w hz hw age
    q.left q.right q.lc q.ls q.rc q.rs
  have equal:=generated.unique original
  change sourceJacobian q age force=_ at equal
  exact equal.trans (funext (fun i=>(sourceSlopeJet_value q force age i).symm))

theorem sourceJacobian_coordinates (q : PhysicalResponsePoint) (age : ℝ) (force : Field289) :
    sourceJacobian q age force=∑j : Fin 289,force j • sourceJacobian q age (fieldUnit j) :=by
  have coordinates : force=∑j : Fin 289,force j • fieldUnit j:=by
    funext i
    simp [fieldUnit,Finset.sum_apply,Pi.single_apply,ite_smul]
  have generated:=congrArg (sourceJacobian q age) coordinates
  simpa only [map_sum,map_smul] using generated

theorem actualSlope_coordinates (q : PhysicalResponsePoint) (age : ℝ) (force : Field289)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (i : Fin 289) :
    (sourceSlopeJet q force age i).value=
      ∑j : Fin 289,force j • (sourceSlopeJet q (fieldUnit j) age i).value :=by
  have generated:=congrArg (fun f : Fin 289→ℂ=>f i) (sourceJacobian_coordinates q age force)
  simpa only [sourceJacobian_actual q age force hz hw,Finset.sum_apply,Pi.smul_apply,
    sourceJacobian_actual q age (fieldUnit _) hz hw] using generated

def windowSourceMatrix (q : PhysicalResponsePoint) (lambda : ℂ) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ:=
  fun i j=>fullForcing q (fieldUnit j) true lambda T i

theorem windowSourceMatrix_actual (q : PhysicalResponsePoint) (force : Field289)
    (lambda : ℂ) (T : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) (i : Fin 289) :
    fullForcing q force true lambda T i=
      ∑j : Fin 289,force j • windowSourceMatrix q lambda T i j :=by
  have integrable (j : Fin 289) : IntervalIntegrable
      (fun r : ℝ=>laplaceWeight lambda r*(sourceSlopeJet q (fieldUnit j) r i).value) volume 0 T:=by
    have h:=sourceSlopeJets_continuous q (fieldUnit j) i
    have w : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
    exact (w.mul h.1).intervalIntegrable _ _
  unfold fullForcing windowSourceMatrix
  simp only [fullSourceJet,↓reduceIte]
  have same (r : ℝ) : laplaceWeight lambda r*(sourceSlopeJet q force r i).value=
      ∑j : Fin 289,force j • (laplaceWeight lambda r*(sourceSlopeJet q (fieldUnit j) r i).value) :=by
    rw [actualSlope_coordinates q r force hz hw i,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_smul_comm _ _ _
  rw [intervalIntegral.integral_congr (fun r _=>same r),intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_smul,fullForcing,fullSourceJet,↓reduceIte]
  · intro j _
    simpa only [Complex.real_smul] using (integrable j).const_mul (force j:ℂ)

def halfSourceMatrix (q : PhysicalResponsePoint) (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  fun i j=>halfForcing q (fieldUnit j) true lambda i

theorem halfSourceMatrix_actual (q : PhysicalResponsePoint) (force : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) (hz : q.z.im≠0) (hw : q.w.im≠0) (i : Fin 289) :
    halfForcing q force true lambda i=
      ∑j : Fin 289,force j • halfSourceMatrix q lambda i j :=by
  have limitLeft:=actual_forcing_limit q force true lambda positive i
  have limitRight:=tendsto_finsetSum Finset.univ (fun j _=>
    (actual_forcing_limit q (fieldUnit j) true lambda positive i).const_smul (force j))
  have equal : (fun T=>fullForcing q force true lambda T i)=
      (fun T=>∑j : Fin 289,force j • fullForcing q (fieldUnit j) true lambda T i):=
    funext (fun T=>windowSourceMatrix_actual q force lambda T hz hw i)
  exact tendsto_nhds_unique limitLeft (equal.symm ▸ limitRight)

theorem sourceMatrix_window_limit (q : PhysicalResponsePoint) (lambda : ℂ)
    (positive : 0<lambda.re) (i j : Fin 289) :
    Tendsto (fun T=>windowSourceMatrix q lambda T i j) atTop (𝓝 (halfSourceMatrix q lambda i j)) :=
  actual_forcing_limit q (fieldUnit j) true lambda positive i

end LowEnergy.PreparationVacuumRealReaction
