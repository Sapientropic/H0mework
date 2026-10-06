import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockPoleSupport

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockSymbol
open PreparationActualFactor PreparationVacuumClockJacobian PreparationVacuumClockPole
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff GaussHistoryHilbert
open PreparationPhaseSource PreparationPhaseBounds PreparationVacuumWeyl
open scoped BigOperators ContDiff Topology Matrix

abbrev Phase := PreparationVacuumClockJacobian.Phase
def poleDomain : Set Phase := {zp | nativePhase zp∈positiveCone ∧ (sourceM zp).det≠0}
def sourceDet (zp : Phase) : ℝ := (sourceM zp).det

theorem actualA_smooth (zp : Phase) (physical : (nativePhase zp).1∈physicalChart) :
    ContDiffAt ℝ ∞ actualA zp :=
  (A_smooth (nativePhase zp) physical).comp zp nativePhase_smooth.contDiffAt
theorem actualT_smooth (zp : Phase) (physical : (nativePhase zp).1∈physicalChart) :
    ContDiffAt ℝ ∞ actualT zp :=
  (T_smooth (nativePhase zp) physical).comp zp nativePhase_smooth.contDiffAt
theorem actualS_smooth (zp : Phase) (physical : (nativePhase zp).1∈physicalChart) (i k : Fin 3) :
    ContDiffAt ℝ ∞ (fun q => actualS q i k) zp :=
  (S_smooth (nativePhase zp) physical i k).comp zp nativePhase_smooth.contDiffAt
theorem actualC_smooth (zp : Phase) (cone : nativePhase zp∈positiveCone) :
    ContDiffAt ℝ ∞ actualC zp :=
  (C_smooth (nativePhase zp) cone).comp zp nativePhase_smooth.contDiffAt

theorem sourceM_entry_smooth (zp : Phase) (physical : (nativePhase zp).1∈physicalChart) (i k : Fin 3) :
    ContDiffAt ℝ ∞ (fun q => sourceM q i k) zp := by
  change ContDiffAt ℝ ∞ (fun q => actualT q*(1 : Matrix (Fin 3) (Fin 3) ℝ) i k-actualS q i k) zp
  exact ((actualT_smooth zp physical).mul contDiffAt_const).sub (actualS_smooth zp physical i k)

private theorem matrixDet_smooth (F : Phase → Matrix (Fin 3) (Fin 3) ℝ) (zp : Phase)
    (entries : ∀ i k,ContDiffAt ℝ ∞ (fun q => F q i k) zp) :
    ContDiffAt ℝ ∞ (fun q => (F q).det) zp := by
  simp_rw [Matrix.det_apply']
  exact ContDiffAt.sum (fun sigma _ => contDiffAt_const.mul
    (contDiffAt_prod (fun i _ => entries (sigma i) i)))

theorem sourceDet_smooth (zp : Phase) (physical : (nativePhase zp).1∈physicalChart) :
    ContDiffAt ℝ ∞ sourceDet zp :=
  matrixDet_smooth sourceM zp (sourceM_entry_smooth zp physical)

theorem sourceAdjugate_smooth (zp : Phase) (physical : (nativePhase zp).1∈physicalChart) (i k : Fin 3) :
    ContDiffAt ℝ ∞ (fun q => (sourceM q).adjugate i k) zp := by
  simp_rw [Matrix.adjugate_apply]
  apply matrixDet_smooth
  intro a b
  by_cases chosen : a=k
  · simpa [Matrix.updateRow_apply,chosen] using
      (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Phase => (Pi.single i (1 : ℝ) : Fin 3 → ℝ) b) zp)
  · simpa [Matrix.updateRow_apply,chosen] using sourceM_entry_smooth zp physical a b

theorem sourceM_inverse_smooth (zp : Phase) (admitted : zp∈poleDomain) (i k : Fin 3) :
    ContDiffAt ℝ ∞ (fun q => (sourceM q)⁻¹ i k) zp := by
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact ((sourceDet_smooth zp admitted.1.1).inv admitted.2).mul
    (sourceAdjugate_smooth zp admitted.1.1 i k)

theorem sourceInverse_smooth (zp : Phase) (admitted : zp∈poleDomain) (a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun q => sourceInverse q a b) zp := by
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun k => ?_) b
    · simpa only [sourceInverse_clock] using!
        (((actualC_smooth zp admitted.1).pow 3).neg.div
          (actualT_smooth zp admitted.1.1) admitted.1.2.2.ne')
    · simpa only [sourceInverse_clock_shift] using
        (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Phase => (0 : ℝ)) zp)
  · refine Fin.cases ?_ (fun k => ?_) b
    · simpa only [sourceInverse_shift_clock] using
        (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Phase => (0 : ℝ)) zp)
    · simpa only [sourceInverse_shift] using
        (((actualC_smooth zp admitted.1).pow 3).neg.mul (sourceM_inverse_smooth zp admitted i k))

theorem poleDomain_open : IsOpen poleDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro zp admitted
  have physical : ∀ᶠ q in 𝓝 zp,(nativePhase q).1∈physicalChart :=
    (continuous_fst.comp nativePhase_smooth.continuous).continuousAt.eventually
      (physicalChart.isOpen.mem_nhds admitted.1.1)
  have aPositive := continuousAt_const.eventually_lt (actualA_smooth zp admitted.1.1).continuousAt admitted.1.2.1
  have tPositive := continuousAt_const.eventually_lt (actualT_smooth zp admitted.1.1).continuousAt admitted.1.2.2
  have determinant := (sourceDet_smooth zp admitted.1.1).continuousAt.eventually_ne admitted.2
  filter_upwards [physical,aPositive,tPositive,determinant] with q hq ha ht hd
  exact ⟨⟨hq,ha,ht⟩,hd⟩

theorem source_support_admitted (z : FlatConfiguration) (p : PhysicalMomentum)
    (position : z∈thetaPositionClosed) (direction : normalizedMomentum p∈thetaDirectionClosed)
    (nonzero : p≠0) : (z,p)∈poleDomain :=
  ⟨source_support_positiveCone z p position direction nonzero,
    sourceM_det_nonzero z p position direction nonzero⟩

theorem original_clockInverse_smooth (z : FlatConfiguration) (p : PhysicalMomentum)
    (position : z∈thetaPositionClosed) (direction : normalizedMomentum p∈thetaDirectionClosed)
    (nonzero : p≠0) (a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun q => sourceInverse q a b) (z,p) :=
  sourceInverse_smooth (z,p) (source_support_admitted z p position direction nonzero) a b

end LowEnergy.PreparationVacuumClockSymbol
