import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalSmoothPermutation

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMoyalSymmetry
open PreparationVacuumCanonicalMoyal PreparationVacuumLowerLeaves PreparationVacuumWeylOrdering
open PreparationVacuumEnergyTail PreparationActualFactor PreparationScalarCoordinates
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open GaussHistoryHilbert GaussNativeEnergy GaussNativePotential GaussDensityCore
open scoped BigOperators ContDiff Topology RealInnerProductSpace

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

def originalPhysicalPhase : Set Phase := {zp | (nativePhase zp).1∈physicalChart}

theorem originalPhysicalPhase_open : IsOpen originalPhysicalPhase :=
  physicalChart.isOpen.preimage (continuous_fst.comp nativePhase_smooth.continuous)

theorem originalScalarPotential_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ scalarPotential z.val := by
  have field : ContDiff ℝ ∞ (fun w : SourceCoordinateSlice => (w.2.1 : Scalar)) :=
    scalarSlice.subtypeL.contDiff.comp (contDiff_fst.comp contDiff_snd)
  have coefficient (i j : Fin 3) : ContDiffAt ℝ ∞
      (fun w => inverseSpatial w i j*⟪scalarGradient w i,scalarGradient w j⟫) z.val :=
    (inverseSpatial_smooth i j z).mul
      ((scalarGradient_smooth i).contDiffAt.inner ℝ (scalarGradient_smooth j).contDiffAt)
  unfold scalarPotential
  exact ((contDiffAt_const.mul volume_smooth.contDiffAt).mul
    (field.contDiffAt.inner ℝ field.contDiffAt)).sub
    (((contDiffAt_const.mul volume_smooth.contDiffAt).div_const 2).mul
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => coefficient i j))

theorem nativeScalarClassical_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ nativeScalarClassical z.val :=
  ((originalScalarPotential_smooth z).div_const _).add
    (contDiffAt_const.mul volume_smooth.contDiffAt)

theorem nativeMagneticTensor_smooth (k l : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => nativeMagneticTensor w k l) z.val := by
  unfold nativeMagneticTensor nativeMagneticGram
  exact (volume_smooth.contDiffAt.div_const _).mul
    (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
      (((triadInverse_smooth i k z).mul
        ((magneticField_smooth i).contDiffAt.inner ℝ (magneticField_smooth j).contDiffAt)).mul
          (triadInverse_smooth j l z)))

theorem originalClassicalLeaf_smooth (j : Fin 13) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => originalClassicalLeaves w j) z.val := by
  fin_cases j <;> first
    | exact nativeScalarClassical_smooth z
    | exact nativeMagneticTensor_smooth _ _ z
    | exact contDiffAt_const

theorem nativeHalfCorrection_smooth (j : Fin 13) (z : physicalChart) :
    ContDiffAt ℝ ∞ (nativeHalfCorrection j) z.val := by
  unfold nativeHalfCorrection
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro k _
  exact ((rawPrincipalCoefficient_smooth j i k z).mul
    (((rawHalfLog_smooth i z).mul (rawHalfLog_smooth k z)).add
      (DR_smooth i (rawHalfLog_smooth k z)))).add
        ((DR_smooth i (rawPrincipalCoefficient_smooth j i k z)).mul (rawHalfLog_smooth k z))

theorem nativeWeylCorrection_smooth (j : Fin 13) (z : physicalChart) :
    ContDiffAt ℝ ∞ (nativeWeylCorrection j) z.val := by
  unfold nativeWeylCorrection
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro k _
  exact DR_smooth i (DR_smooth k (rawPrincipalCoefficient_smooth j i k z))

theorem originalZeroLeaf_smooth (j : Fin 14) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => originalZeroLeaves w j) z.val := by
  refine Fin.lastCases ?_ ?_ j
  · simpa only [originalZeroLeaves,Fin.snoc_last] using
      (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : SourceCoordinateSlice => (0 : ℝ)) z.val)
  · intro k
    simpa only [originalZeroLeaves,Fin.snoc_castSucc] using
      ((originalClassicalLeaf_smooth k z).add (nativeHalfCorrection_smooth k z)).add
        (nativeWeylCorrection_smooth k z)

theorem scalarContraction_smooth (i : Fin 3) (zp : SourceCoordinateSlice × Cotangent)
    (physical : zp.1∈physicalChart) :
    ContDiffAt ℝ ∞ (fun v => scalarContraction v.1 v.2 i) zp := by
  unfold scalarContraction
  apply ContDiffAt.sum
  intro a _
  exact (scalarMomentum_smooth zp physical a).mul
    (contDiffAt_const.inner ℝ ((scalarGradient_smooth i).contDiffAt.comp zp contDiffAt_fst))

theorem gaugeContraction_smooth (i j : Fin 3) (zp : SourceCoordinateSlice × Cotangent)
    (physical : zp.1∈physicalChart) :
    ContDiffAt ℝ ∞ (fun v => gaugeContraction v.1 v.2 i j) zp := by
  unfold gaugeContraction
  apply ContDiffAt.sum
  intro a _
  exact (electricMomentum_smooth zp physical i a).mul
    (contDiffAt_const.inner ℝ ((magneticField_smooth j).contDiffAt.comp zp contDiffAt_fst))

theorem scalarShiftLeaf_smooth (r : Fin 3) (zp : SourceCoordinateSlice × Cotangent)
    (physical : zp.1∈physicalChart) :
    ContDiffAt ℝ ∞ (fun v => scalarShiftLeaf v.1 v.2 r) zp := by
  unfold scalarShiftLeaf
  apply ContDiffAt.sum
  intro i _
  exact ((triadInverse_smooth i r ⟨zp.1,physical⟩).comp zp contDiffAt_fst).mul
    (scalarContraction_smooth i zp physical)

theorem gaugeShiftLeaf_smooth (r : Fin 3) (zp : SourceCoordinateSlice × Cotangent)
    (physical : zp.1∈physicalChart) :
    ContDiffAt ℝ ∞ (fun v => gaugeShiftLeaf v.1 v.2 r) zp := by
  unfold gaugeShiftLeaf
  apply (volume_smooth.contDiffAt.comp zp contDiffAt_fst).mul
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.mul _ (gaugeContraction_smooth i j zp physical)
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  apply ContDiffAt.sum
  intro k _
  apply ContDiffAt.mul _ ((triadInverse_smooth j k ⟨zp.1,physical⟩).comp zp contDiffAt_fst)
  apply ContDiffAt.sum
  intro l _
  exact ((triadInverse_smooth i l ⟨zp.1,physical⟩).comp zp contDiffAt_fst).mul contDiffAt_const

theorem originalFirstLeaf_smooth (j : Fin 14) (zp : SourceCoordinateSlice × Cotangent)
    (physical : zp.1∈physicalChart) :
    ContDiffAt ℝ ∞ (fun v => originalFirstLeaves v.1 v.2 j) zp := by
  fin_cases j <;> first
    | exact scalarShiftLeaf_smooth _ zp physical
    | exact gaugeShiftLeaf_smooth _ zp physical
    | exact contDiffAt_const

theorem originalPrincipalLeaf_joint_smooth (j : Fin 13) (zp : SourceCoordinateSlice × Cotangent)
    (physical : zp.1∈physicalChart) :
    ContDiffAt ℝ ∞ (fun v => originalPrincipalLeaves v.1 v.2 j) zp := by
  fin_cases j <;> first
    | exact A_smooth zp physical
    | exact S_smooth zp physical _ _
    | exact contDiffAt_const

theorem originalLeaf_smooth (d : Fin 3) (j : Fin 14) (zp : Phase)
    (physical : zp∈originalPhysicalPhase) : ContDiffAt ℝ ∞ (originalLeaf d j) zp := by
  have position : (nativePhase zp).1∈physicalChart := physical
  fin_cases d
  · exact (originalZeroLeaf_smooth j ⟨(nativePhase zp).1,position⟩).comp zp
      (nativePhase_smooth.contDiffAt.fst)
  · exact (originalFirstLeaf_smooth j (nativePhase zp) position).comp zp nativePhase_smooth.contDiffAt
  · change ContDiffAt ℝ ∞ (originalLeaf 2 j) zp
    refine Fin.lastCases ?_ ?_ j
    · rw [originalLeaf_Y_zero]
      exact contDiffAt_const
    · intro k
      have same : originalLeaf 2 (Fin.castSucc k)=fun v =>
          originalPrincipalLeaves (nativePhase v).1 (nativePhase v).2 k := by
        funext v
        exact originalLeaf_principal k v
      rw [same]
      exact (originalPrincipalLeaf_joint_smooth k (nativePhase zp) position).comp zp nativePhase_smooth.contDiffAt

theorem originalLeaf_smoothOn (d : Fin 3) (j : Fin 14) :
    ContDiffOn ℝ ∞ (originalLeaf d j) originalPhysicalPhase :=
  fun zp physical => (originalLeaf_smooth d j zp physical).contDiffWithinAt

theorem originalLeaf_jet_permutation (d : Fin 3) (j : Fin 14) (r : ℕ)
    (v : Fin r → Phase) (sigma : Equiv.Perm (Fin r)) (zp : Phase)
    (physical : zp∈originalPhysicalPhase) :
    iteratedFDeriv ℝ r (originalLeaf d j) zp (v∘sigma)=
      iteratedFDeriv ℝ r (originalLeaf d j) zp v :=
  smooth_iteratedFDeriv_perm originalPhysicalPhase_open (originalLeaf_smoothOn d j) r v sigma zp physical

theorem originalLeaf_domDomCongr (d : Fin 3) (j : Fin 14) (r : ℕ)
    (sigma : Equiv.Perm (Fin r)) (zp : Phase) (physical : zp∈originalPhysicalPhase) :
    (iteratedFDeriv ℝ r (originalLeaf d j) zp).domDomCongr sigma=
      iteratedFDeriv ℝ r (originalLeaf d j) zp :=
  smooth_domDomCongr originalPhysicalPhase_open (originalLeaf_smoothOn d j) r sigma zp physical

end LowEnergy.PreparationVacuumMoyalSymmetry
