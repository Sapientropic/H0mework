import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPhysicalForce

/-! The unlocalized physical source uses the same finite occurrence and
resolvent completion. Its original minimal graph and actual defect remain
visible when the complete configuration force is consumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPhysicalResolvent
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussLiveMomentum GaussFockPair
open CanonicalPhysicalSpatial CanonicalGradedSpatialSource
open SourceMinimalGraphParticular SourceFamilyHilbert SourceFamilyOperator Filter
open GaussUnitaryHistory (HistorySpace Index sourceFilter inclusion)
open scoped Topology InnerProductSpace

def finiteResolvent (p : PhysicalMomentum) (F : Index) (z : ℂ) : H →L[ℂ] H :=
  FullYSourceResolventGraphSplice.resolvent (compression p F) z

theorem finite_bound (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z.im≠0) :
    ‖finiteResolvent p F z‖ ≤ 1/|z.im| :=
  FullYSourceResolventGraphSplice.resolvent_norm _ (compression_selfAdjoint p F) z hz

def resolventFamily (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) : Operator Index H where
  component F := finiteResolvent p F z
  bounded := ⟨1/|z.im|, by positivity, fun F x =>
    ((finiteResolvent p F z).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (finite_bound p F z hz) (norm_nonneg x))⟩

def sourceResolvent (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (resolventFamily p z hz)

theorem resolvent_original (z : ℂ) (hz : z.im≠0) :
    sourceResolvent 0 z hz=FullYSourceResolventGraphSplice.sameResolvent z hz := by
  apply lift_congr sourceFilter
  intro F
  exact congrArg (fun C : H →L[ℂ] H => FullYSourceResolventGraphSplice.resolvent C z) (compression_zero F)

theorem resolvent_bound (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (x : HistorySpace) :
    ‖sourceResolvent p z hz x‖ ≤ (1/|z.im|)*‖x‖ := by
  apply SourceBoundaryGram.lift_bound_explicit sourceFilter (resolventFamily p z hz) _ (by positivity)
  intro F g
  exact ((finiteResolvent p F z).le_opNorm g).trans
    (mul_le_mul_of_nonneg_right (finite_bound p F z hz) (norm_nonneg g))

private theorem family_equal {f g : Family H sourceFilter}
    (equal : ∀ᶠ F in (sourceFilter : Filter Index), value f F=value g F) :
    (f : HistorySpace)=(g : HistorySpace) := by
  have nonpositive : ‖f-g‖ ≤ 0 := by
    apply norm_le_of_eventually sourceFilter (f-g) 0
    filter_upwards [equal] with F hF
    change ‖value f F-value g F‖ ≤ 0
    rw [hF, sub_self, norm_zero]
  have zero : ((f-g : Family H sourceFilter) : HistorySpace)=0 := by
    apply norm_eq_zero.mp
    rw [UniformSpace.Completion.norm_coe]
    exact le_antisymm nonpositive (norm_nonneg _)
  exact sub_eq_zero.mp (by simpa only [UniformSpace.Completion.coe_sub] using zero)

theorem shifted_core_return (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (f : diagonal.domain) :
    sourceResolvent p z hz (inclusion (shift (physical p) z f))=inclusion (f : H) := by
  change lift sourceFilter (resolventFamily p z hz)
    ((SourceFamilyHilbert.constant sourceFilter (shift (physical p) z f)) : HistorySpace) =
      ((SourceFamilyHilbert.constant sourceFilter (f : H)) : HistorySpace)
  rw [lift_coe]
  apply family_equal
  filter_upwards [eventually_exact p f] with F exactCore
  change finiteResolvent p F z (physical p f-z • (f : H))=(f : H)
  rw [← exactCore]
  exact congrArg (fun A : H →L[ℂ] H => A (f : H))
    (FullYSourceResolventGraphSplice.resolvent_left _ (compression_selfAdjoint p F) z hz)

theorem finite_source_pair (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z.im≠0)
    (x : diagonal.domain) (hx : compression p F (x : H)=physical p x) (y : H) :
    inner ℂ (shift (physical p) (star z) x) (finiteResolvent p F z y)=inner ℂ (x : H) y := by
  have inverse := congrArg (fun A : H →L[ℂ] H => A y)
    (FullYSourceResolventGraphSplice.resolvent_right _ (compression_selfAdjoint p F) z hz)
  change compression p F (finiteResolvent p F z y)-z • finiteResolvent p F z y=y at inverse
  change inner ℂ (physical p x-star z • (x : H)) (finiteResolvent p F z y)=_
  have pair : inner ℂ (compression p F (x : H)) (finiteResolvent p F z y) =
      inner ℂ (x : H) (compression p F (finiteResolvent p F z y)) :=
    compression_pair p F (x : H) (finiteResolvent p F z y)
  rw [← hx, inner_sub_left, inner_smul_left, starRingEnd_apply, star_star, pair]
  rw [← inner_smul_right, ← inner_sub_right, inverse]

theorem whole_source_pair (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (x : diagonal.domain)
    (y : HistorySpace) :
    inner ℂ (inclusion (shift (physical p) (star z) x)) (sourceResolvent p z hz y) =
      inner ℂ (inclusion (x : H)) y := by
  refine UniformSpace.Completion.induction_on y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  change inner ℂ ((SourceFamilyHilbert.constant sourceFilter (shift (physical p) (star z) x)) : HistorySpace)
      (lift sourceFilter (resolventFamily p z hz) (f : HistorySpace)) =
    inner ℂ ((SourceFamilyHilbert.constant sourceFilter (x : H)) : HistorySpace) (f : HistorySpace)
  rw [lift_coe, inner_coe, inner_coe]
  apply tendsto_nhds_unique
    (pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter (shift (physical p) (star z) x))
      (act sourceFilter (resolventFamily p z hz) f))
  apply (pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter (x : H)) f).congr'
  filter_upwards [eventually_exact p x] with F exactCore
  exact (finite_source_pair p F z hz x exactCore (value f F)).symm

theorem shifted_range_return (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0)
    (r : shiftedRange (physical p) z) :
    sourceResolvent p z hz (inclusion (r : H))=inclusion (inverseOnRange (physical p) z r) := by
  refine (intoShiftedRange_dense (physical p) z).induction_on r
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x
  rw [inverseOnRange_core (physical p) (physical_pair p) z hz x]
  exact shifted_core_return p z hz x

theorem particular_split (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (x : H) :
    sourceResolvent p z hz (inclusion x)=inclusion (particular (physical p) z x)+
      sourceResolvent p z hz (inclusion (defect (physical p) z x)) := by
  let r := (shiftedRange (physical p) z).orthogonalProjectionOnto x
  have decomposition : x=(r : H)+defect (physical p) z x := by
    change x=(shiftedRange (physical p) z).starProjection x+
      (x-(shiftedRange (physical p) z).starProjection x)
    abel
  calc
    _ = sourceResolvent p z hz (inclusion (r : H)+inclusion (defect (physical p) z x)) :=
      congrArg (sourceResolvent p z hz) ((congrArg inclusion decomposition).trans (map_add inclusion _ _))
    _ = inclusion (inverseOnRange (physical p) z r)+sourceResolvent p z hz (inclusion (defect (physical p) z x)) := by
      rw [map_add, shifted_range_return]
    _ = _ := rfl

theorem particular_error (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (x : H) :
    ‖sourceResolvent p z hz (inclusion x)-inclusion (particular (physical p) z x)‖ ≤
      (1/|z.im|)*‖defect (physical p) z x‖ := by
  rw [particular_split, add_sub_cancel_left]
  simpa only [inclusion.norm_map] using resolvent_bound p z hz (inclusion (defect (physical p) z x))

def forceResponse (p : PhysicalMomentum) (v : Ambient) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) : HistorySpace :=
  sourceResolvent p z hz (inclusion (embed (CanonicalGradedFullForce.force v g)))

theorem forceResponse_bound (p : PhysicalMomentum) (v : Ambient) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    ‖forceResponse p v z hz g‖ ≤ (1/|z.im|)*‖embed (CanonicalGradedFullForce.force v g)‖ := by
  simpa only [forceResponse, inclusion.norm_map] using
    resolvent_bound p z hz (inclusion (embed (CanonicalGradedFullForce.force v g)))

theorem shifted_test_original (p : PhysicalMomentum) (z : ℂ) (f : QuantumTest) :
    embed (CanonicalPhysicalForce.shiftedTest p z f)=shift (physical p) z (coreEquiv f) := by
  change embed (physicalAction p f-z • f)=
    embed (physicalAction p (coreEquiv.symm (coreEquiv f)))-z • embed f
  rw [coreEquiv.symm_apply_apply, map_sub, map_smul]

theorem forceResponse_endpoints (p : PhysicalMomentum) (v : Ambient) (z w : ℂ) (hz : z.im≠0)
    (f g : QuantumTest) :
    inner ℂ (inclusion (embed (CanonicalPhysicalForce.shiftedTest p (star z) f)))
      (forceResponse p v z hz g)=Complex.I*
      (sourcePair (CanonicalPhysicalForce.shiftedTest p (star z) f) (covariantMomentum v g)-
        sourcePair (GaussMomentumAdjoint.adjoint v f) (CanonicalPhysicalForce.shiftedTest p w g)+
        (z-w)*sourcePair f (covariantMomentum v g)) := by
  rw [shifted_test_original, forceResponse, whole_source_pair, inclusion.inner_map_map]
  exact CanonicalPhysicalForce.physical_force_endpoints p v z w f g

theorem forceResponse_particular (p : PhysicalMomentum) (v : Ambient) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    forceResponse p v z hz g=inclusion (particular (physical p) z (embed (CanonicalGradedFullForce.force v g)))+
      sourceResolvent p z hz (inclusion (defect (physical p) z (embed (CanonicalGradedFullForce.force v g)))) :=
  particular_split p z hz _

theorem forceResponse_error (p : PhysicalMomentum) (v : Ambient) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    ‖forceResponse p v z hz g-inclusion (particular (physical p) z (embed (CanonicalGradedFullForce.force v g)))‖ ≤
      (1/|z.im|)*‖defect (physical p) z (embed (CanonicalGradedFullForce.force v g))‖ :=
  particular_error p z hz _

end LowEnergy.CanonicalPhysicalResolvent
