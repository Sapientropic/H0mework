import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalGradedCurrentSource
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalCompletedSectorReturn
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceEscapeDefectFeed

/-! The complete native/coframe/matter force is read on the original core.
Its covariant momenta stay on the external legs. The unchanged source
resolvent retains its actual deficiency and boundary response. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedFullForce
open GaussCoreDifferential GaussCoreHilbert GaussDiagonalHistory GaussFockPair
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates GaussLiveMomentum
open CanonicalGradedCurrent SourceMinimalGraphParticular SourceBoundaryGram
open FullYSourceResolventGraphSplice
open GaussUnitaryHistory (HistorySpace inclusion)
open scoped Topology InnerProductSpace ContDiff Distributions

abbrev CoreEnd := QuantumTest →ₗ[ℂ] QuantumTest
abbrev force (v : Ambient) : CoreEnd := covariantForce v

def sharpForce (v : Ambient) : CoreEnd := Complex.I •
  (diagonalAction.comp (GaussMomentumAdjoint.adjoint v)-
    (GaussMomentumAdjoint.adjoint v).comp diagonalAction)

def actionForce (A P : CoreEnd) : CoreEnd := Complex.I • (A.comp P-P.comp A)

theorem force_complete (v : Ambient) :
    force v=actionForce GaussNativeForm.nativeAction (covariantMomentum v)+
      actionForce GaussCoframeForm.coframeAction (covariantMomentum v)+
      actionForce GaussMatterCore.matterAction (covariantMomentum v) := by
  ext f
  simp only [force, covariantForce, actionForce, diagonalAction, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add, smul_add, smul_sub]
  abel

theorem force_spatial (i : Fin 3) (a : SourceQuantumScalarChart.NativeLie) :
    force (CanonicalGradedCurrent.gaugeDirection i a)=fullSpatialGaugeForce i a := rfl

theorem force_weak (v : Ambient) (f g : QuantumTest) :
    sourcePair f (force v g)=Complex.I*(sourcePair (diagonalAction f) (covariantMomentum v g)-
      sourcePair (GaussMomentumAdjoint.adjoint v f) (diagonalAction g)) := by
  change inner ℂ (embed f) (embed (Complex.I •
    (diagonalAction (covariantMomentum v g)-covariantMomentum v (diagonalAction g)))) = _
  rw [map_smul, map_sub, inner_smul_right, inner_sub_right]
  change Complex.I*(sourcePair f (diagonalAction (covariantMomentum v g))-
    sourcePair f (covariantMomentum v (diagonalAction g))) = _
  rw [diagonalAction_pair f (covariantMomentum v g), GaussMomentumAdjoint.momentum_pair v f (diagonalAction g)]

theorem force_sharp_pair (v : Ambient) (f g : QuantumTest) :
    sourcePair f (force v g)=sourcePair (sharpForce v f) g := by
  rw [force_weak]
  change _ = inner ℂ (embed (Complex.I •
    (diagonalAction (GaussMomentumAdjoint.adjoint v f)-GaussMomentumAdjoint.adjoint v (diagonalAction f)))) (embed g)
  rw [map_smul, map_sub, inner_smul_left, inner_sub_left, Complex.conj_I]
  change _ = -Complex.I*(sourcePair (diagonalAction (GaussMomentumAdjoint.adjoint v f)) g-
    sourcePair (GaussMomentumAdjoint.adjoint v (diagonalAction f)) g)
  rw [← diagonalAction_pair (GaussMomentumAdjoint.adjoint v f) g,
    ← GaussMomentumAdjoint.momentum_pair v (diagonalAction f) g]
  ring

def shiftedTest (z : ℂ) (f : QuantumTest) : QuantumTest := diagonalAction f-z • f

theorem shiftedTest_original (z : ℂ) (f : QuantumTest) :
    embed (shiftedTest z f)=shift diagonal z (coreEquiv f) := by
  change embed (diagonalAction f-z • f)=
    embed (diagonalAction (coreEquiv.symm (coreEquiv f)))-z • embed f
  rw [coreEquiv.symm_apply_apply, map_sub, map_smul]

theorem force_endpoints (v : Ambient) (z w : ℂ) (f g : QuantumTest) :
    sourcePair f (force v g)=Complex.I*
      (sourcePair (shiftedTest (star z) f) (covariantMomentum v g)-
        sourcePair (GaussMomentumAdjoint.adjoint v f) (shiftedTest w g)+
        (z-w)*sourcePair f (covariantMomentum v g)) := by
  rw [force_weak]
  have p := GaussMomentumAdjoint.momentum_pair v f g
  simp only [sourcePair, shiftedTest, map_sub, map_smul, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_star] at p ⊢
  rw [← p]
  ring

theorem force_weak_bound (v : Ambient) (f g : QuantumTest) :
    ‖sourcePair f (force v g)‖ ≤ ‖embed (diagonalAction f)‖*‖embed (covariantMomentum v g)‖+
      ‖embed (GaussMomentumAdjoint.adjoint v f)‖*‖embed (diagonalAction g)‖ := by
  rw [force_weak, norm_mul, Complex.norm_I, one_mul]
  exact (norm_sub_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))

theorem resolvent_test_return (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    sameResolvent z hz (inclusion (embed (shiftedTest z f)))=inclusion (embed f) := by
  rw [shiftedTest_original]
  exact CanonicalCompletedSector.same_resolvent_shifted_core z hz (coreEquiv f)

theorem resolvent_H_test (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    sameResolvent z hz (inclusion (embed (diagonalAction f)))=
      inclusion (embed f)+z • sameResolvent z hz (inclusion (embed f)) := by
  have source := resolvent_test_return z hz f
  change sameResolvent z hz (inclusion (embed (diagonalAction f-z • f)))=inclusion (embed f) at source
  rw [map_sub, map_smul, map_sub, map_smul, map_sub, map_smul] at source
  exact sub_eq_iff_eq_add.mp source

def response (v : Ambient) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) : HistorySpace :=
  sameResolvent z hz (inclusion (embed (force v g)))

theorem response_original (v : Ambient) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    response v z hz g=Complex.I • (inclusion (embed (covariantMomentum v g))+
      z • sameResolvent z hz (inclusion (embed (covariantMomentum v g)))-
      sameResolvent z hz (inclusion (embed (covariantMomentum v (diagonalAction g))))) := by
  change sameResolvent z hz (inclusion (embed (Complex.I •
    (diagonalAction (covariantMomentum v g)-covariantMomentum v (diagonalAction g)))))=_
  simp only [map_smul, map_sub]
  have source := resolvent_H_test z hz (covariantMomentum v g)
  exact congrArg (fun x : HistorySpace => Complex.I • (x-
    sameResolvent z hz (inclusion (embed (covariantMomentum v (diagonalAction g)))))) source

theorem response_bound (v : Ambient) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    ‖response v z hz g‖ ≤ (1/|z.im|)*‖embed (force v g)‖ := by
  simpa only [response, inclusion.norm_map] using same_resolvent_bound z hz (inclusion (embed (force v g)))

theorem response_shifted_pair (v : Ambient) (z : ℂ) (hz : z.im≠0) (f g : QuantumTest) :
    inner ℂ (inclusion (embed (shiftedTest (star z) f))) (response v z hz g)=sourcePair f (force v g) := by
  rw [shiftedTest_original]
  have generated := whole_carrier_source_pair z hz (coreEquiv f) (inclusion (embed (force v g)))
  change inner ℂ (inclusion (shift diagonal (star z) (coreEquiv f))) (response v z hz g)=
    inner ℂ (inclusion (embed f)) (inclusion (embed (force v g))) at generated
  rw [inclusion.inner_map_map] at generated
  exact generated

/-- Both energy endpoints act on actual smooth source legs. No `P R` operator is postulated. -/
theorem response_endpoints (v : Ambient) (z w : ℂ) (hz : z.im≠0) (f g : QuantumTest) :
    inner ℂ (inclusion (embed (shiftedTest (star z) f))) (response v z hz g)=Complex.I*
      (sourcePair (shiftedTest (star z) f) (covariantMomentum v g)-
        sourcePair (GaussMomentumAdjoint.adjoint v f) (shiftedTest w g)+
        (z-w)*sourcePair f (covariantMomentum v g)) := by
  rw [response_shifted_pair, force_endpoints]


theorem coreShift_commutator (P : CoreEnd) (z : ℂ) (f : QuantumTest) :
    shiftedTest z (P f)=P (shiftedTest z f)+(diagonalAction (P f)-P (diagonalAction f)) := by
  rw [shiftedTest, shiftedTest, map_sub, map_smul]
  abel

/-- The exact boundary return uses the actual weighted transpose momentum. -/
theorem boundary_force_return (v : Ambient) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) (y : HistorySpace) :
    inner ℂ (inclusion (embed (sharpForce v f))) (boundaryReturn z hz y)=
      Complex.I*inner ℂ (inclusion (embed (GaussMomentumAdjoint.adjoint v (shiftedTest (star z) f))))
        (boundaryReturn z hz y) := by
  have source := boundary_source_pair_zero z hz (coreEquiv (GaussMomentumAdjoint.adjoint v f)) y
  rw [← shiftedTest_original, coreShift_commutator, map_add, map_add, inner_add_left] at source
  change inner ℂ (inclusion (embed (Complex.I •
    (diagonalAction (GaussMomentumAdjoint.adjoint v f)-GaussMomentumAdjoint.adjoint v (diagonalAction f)))))
    (boundaryReturn z hz y)=_
  simp only [map_smul, inner_smul_left, Complex.conj_I]
  linear_combination (-Complex.I)*source

theorem boundary_force_bound (v : Ambient) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) (y : HistorySpace) :
    ‖inner ℂ (inclusion (embed (sharpForce v f))) (boundaryReturn z hz y)‖ ≤
      ‖embed (sharpForce v f)‖*((1/|z.im|)*‖y‖) := by
  apply (norm_inner_le_norm _ _).trans
  rw [inclusion.norm_map]
  exact mul_le_mul_of_nonneg_left (boundary_return_bound z hz y) (norm_nonneg _)

theorem defect_shift_test (z : ℂ) (f : QuantumTest) : sourceDefect z (embed (shiftedTest z f))=0 := by
  have original : embed (shiftedTest z f) ∈ shiftedRange diagonal z := by
    rw [shiftedTest_original]
    exact (LinearMap.range (shift diagonal z)).le_topologicalClosure (LinearMap.mem_range_self _ (coreEquiv f))
  change embed (shiftedTest z f)-(shiftedRange diagonal z).starProjection (embed (shiftedTest z f))=0
  rw [Submodule.starProjection_eq_self_iff.mpr original, sub_self]

/-- The whole force's deficiency input is generated by an original shifted
momentum leg. It is retained, not replaced by a zero boundary condition. -/
theorem defect_force_input (v : Ambient) (z : ℂ) (f : QuantumTest) :
    sourceDefect z (embed (force v f))=(-Complex.I) •
      sourceDefect z (embed (covariantMomentum v (shiftedTest z f))) := by
  have source := defect_shift_test z (covariantMomentum v f)
  rw [coreShift_commutator, map_add, map_add] at source
  change sourceDefect z (embed (Complex.I •
    (diagonalAction (covariantMomentum v f)-covariantMomentum v (diagonalAction f))))=_
  rw [map_smul, map_smul, eq_neg_of_add_eq_zero_right source, smul_neg, neg_smul]

def defectResponse (v : Ambient) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) : HistorySpace :=
  sameResolvent z hz (inclusion (sourceDefect z (embed (force v g))))

theorem response_particular_split (v : Ambient) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    response v z hz g=inclusion (sourceParticular z (embed (force v g)))+defectResponse v z hz g :=
  SourceEscapeDefectFeed.source_right_particular_split z hz (embed (force v g))

theorem defectResponse_original (v : Ambient) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    defectResponse v z hz g=(-Complex.I) • sameResolvent z hz
      (inclusion (sourceDefect z (embed (covariantMomentum v (shiftedTest z g))))) := by
  rw [defectResponse, defect_force_input, map_smul, map_smul]

theorem response_defect_bound (v : Ambient) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    ‖response v z hz g-inclusion (sourceParticular z (embed (force v g)))‖ ≤
      (1/|z.im|)*‖sourceDefect z (embed (force v g))‖ := by
  rw [response_particular_split, add_sub_cancel_left]
  simpa only [defectResponse, inclusion.norm_map] using
    same_resolvent_bound z hz (inclusion (sourceDefect z (embed (force v g))))

def pairResponse (v : Ambient) (z : ℂ) (hz : z.im≠0) (f g : QuantumTest) : ℂ :=
  inner ℂ (inclusion (embed f)) (response v z hz g)

theorem pairResponse_bound (v : Ambient) (z : ℂ) (hz : z.im≠0) (f g : QuantumTest) :
    ‖pairResponse v z hz f g‖ ≤ ‖embed f‖*((1/|z.im|)*‖embed (force v g)‖) := by
  apply (norm_inner_le_norm _ _).trans
  rw [inclusion.norm_map]
  exact mul_le_mul_of_nonneg_left (response_bound v z hz g) (norm_nonneg _)

theorem pairResponse_defect_bound (v : Ambient) (z : ℂ) (hz : z.im≠0) (f g : QuantumTest) :
    ‖pairResponse v z hz f g-inner ℂ (embed f) (sourceParticular z (embed (force v g)))‖ ≤
      ‖embed f‖*((1/|z.im|)*‖sourceDefect z (embed (force v g))‖) := by
  have embedded := inclusion.inner_map_map (embed f) (sourceParticular z (embed (force v g)))
  rw [← embedded, pairResponse, ← inner_sub_right]
  apply (norm_inner_le_norm _ _).trans
  rw [inclusion.norm_map]
  exact mul_le_mul_of_nonneg_left (response_defect_bound v z hz g) (norm_nonneg _)

end LowEnergy.CanonicalGradedFullForce
