import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceScalarNativeComparison
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourcePhysicalHamiltonianSquare

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarRetardedGram
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open GaussCoframeForm GaussMatterCore SourceCoframeVolume SourceCoframeVolumeCurrent
open SourceScalarFlatJoint SourceScalarNativeComparison SourceScalarPairedTransport
open SourcePairedRadialFlux SourcePairedMomentumFlux SourceEscapeCurrent
open FullYSourceResolventGraphSplice SourceQuantumConfigurationHilbert SourceMinimalGraphParticular
open SourcePhysicalHamiltonianSquare
open scoped InnerProductSpace BigOperators

private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
private abbrev OriginalCore : Type := diagonal.domain

/-- Every non-scalar-kinetic term of the literal H0, including the signed spatial potential. -/
def nonScalarAction : CoreEnd :=
  gaugeKinetic+multiply potential potential_smooth+coframeAction+matterAction

theorem original_scalar_split : diagonalAction=scalarKinetic+nonScalarAction := by
  unfold diagonalAction nativeAction nonScalarAction
  abel

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

/-- Original source energy identity; no positivity is asserted for its non-scalar terms. -/
theorem original_signed_native_energy (f : QuantumTest) :
    nativeScalarEnergy f=(2/sourceTime 0)*(
      (sourcePair (volumeAction f) (nonScalarAction f)).re-
      (sourcePair (volumeAction f) (diagonalAction f)).re) := by
  have hs := actual_native_scalar_form f
  have hp : sourcePair f (volumeAction (scalarKinetic f))=
      sourcePair (volumeAction f) (scalarKinetic f) := multiply_pair _ _ _ _
  rw [hp] at hs
  have hh : sourcePair (volumeAction f) (diagonalAction f)=
      sourcePair (volumeAction f) (scalarKinetic f)+sourcePair (volumeAction f) (nonScalarAction f) := by
    rw [original_scalar_split]
    simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right]
  rw [hh,Complex.add_re,hs]
  field_simp [lapse_pos.ne']
  ring

private theorem star_im_ne (z : ℂ) (hz : z.im≠0) : (star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

def leftState (F : Index) (z : ℂ) (hz : z.im≠0) (k : OriginalCore) : QuantumTest :=
  coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)
def rightState (F : Index) (z : ℂ) (hz : z.im≠0) (g : OriginalCore) : QuantumTest :=
  coreEquiv.symm (sourceCore F z hz g)

def jointState (F : Index) (z : ℂ) (hz : z.im≠0) (g k : OriginalCore) (a b : ℂ) : QuantumTest :=
  a • leftState F z hz k+b • rightState F z hz g

def jointInput (g k : OriginalCore) (a b : ℂ) : H := a • (k : H)+b • (g : H)
def jointFrequency (F : Index) (z : ℂ) (g k : OriginalCore) (a b : ℂ) : H :=
  a • (star z • finiteResolvent F (star z) (k : H))+b • (z • finiteResolvent F z (g : H))
def jointDefect (F : Index) (z : ℂ) (hz : z.im≠0) (g k : OriginalCore) (a b : ℂ) : H :=
  a • finiteProjectionDefect F (star z) (star_im_ne z hz) k+b • finiteProjectionDefect F z hz g

/-- Both actual source equations are combined before taking any norm or real part. -/
theorem actual_joint_source_action (F : Index) (z : ℂ) (hz : z.im≠0) (g k : OriginalCore) (a b : ℂ) :
    embed (diagonalAction (jointState F z hz g k a b))=
      jointInput g k a b+jointFrequency F z g k a b+jointDefect F z hz g k a b := by
  have hp := source_core_action F (star z) (star_im_ne z hz) k
  have hq := source_core_action F z hz g
  change embed (diagonalAction (leftState F z hz k))=_ at hp
  change embed (diagonalAction (rightState F z hz g))=_ at hq
  simp only [jointState,map_add,map_smul]
  rw [hp,hq]
  simp only [jointInput,jointFrequency,jointDefect,smul_add]
  abel

/-- A signed source expression, generated with the full left/right defect and every mixed term. -/
def signedNativeCost (F : Index) (z : ℂ) (hz : z.im≠0) (g k : OriginalCore) (a b : ℂ) : ℝ :=
  let f := jointState F z hz g k a b
  (2/sourceTime 0)*((sourcePair (volumeAction f) (nonScalarAction f)).re-
    (inner ℂ (embed (volumeAction f)) (jointInput g k a b)).re-
    (inner ℂ (embed (volumeAction f)) (jointFrequency F z g k a b)).re-
    (inner ℂ (embed (volumeAction f)) (jointDefect F z hz g k a b)).re)

/-- The actual two-resolvent signed cost is the complete positive native scalar Gram. -/
theorem actual_joint_native_cost (F : Index) (z : ℂ) (hz : z.im≠0) (g k : OriginalCore) (a b : ℂ) :
    signedNativeCost F z hz g k a b=nativeScalarEnergy (jointState F z hz g k a b) := by
  have h := original_signed_native_energy (jointState F z hz g k a b)
  change _=(2/sourceTime 0)*((sourcePair (volumeAction _) (nonScalarAction _)).re-
    (inner ℂ (embed (volumeAction _)) (embed (diagonalAction _))).re) at h
  rw [actual_joint_source_action,inner_add_right,inner_add_right,Complex.add_re,Complex.add_re] at h
  dsimp only [signedNativeCost]
  exact (h.trans (by ring)).symm

/-- Arbitrary complex mixing exposes all off-diagonal Gram entries without dropping cross terms. -/
theorem actual_joint_native_square (F : Index) (z : ℂ) (hz : z.im≠0) (g k : OriginalCore) (a b : ℂ) :
    signedNativeCost F z hz g k a b=
      ∑ i : ScalarIndex,‖a • embed (GaussCoreDifferential.covariantMomentum (scalarDirection i) (leftState F z hz k))+
        b • embed (GaussCoreDifferential.covariantMomentum (scalarDirection i) (rightState F z hz g))‖^2 := by
  rw [actual_joint_native_cost]
  simp only [nativeScalarEnergy,jointState,map_add,map_smul]

/-- The same mixed source returns the original complete H0 signed square, including matter and spatial signs. -/
theorem actual_joint_hamiltonian_square (F : Index) (z : ℂ) (hz : z.im≠0) (g k : OriginalCore) (a b : ℂ) :
    SourcePhysicalHamiltonianSquare.signedCost (jointState F z hz g k a b)=
      ‖jointInput g k a b+jointFrequency F z g k a b+jointDefect F z hz g k a b‖^2 := by
  rw [←physical_hamiltonian_square,actual_joint_source_action]

/-- All scalar61 and orthogonal9 contributions survive the joint source substitution. -/
theorem actual_joint_flat_split (F : Index) (z : ℂ) (hz : z.im≠0) (g k : OriginalCore) (a b : ℂ) :
    signedNativeCost F z hz g k a b=
      (sourcePair (jointState F z hz g k a b) (flatKinetic (jointState F z hz g k a b))).re+
        orthogonalEnergy (jointState F z hz g k a b) := by
  rw [actual_joint_native_cost,actual_scalar_energy_split]

private theorem flat_native_bound (sharp : Bool) (f : QuantumTest) :
    ‖embed (flatScalarCurrent sharp f)‖^2≤rowCost sharp*nativeScalarEnergy f := by
  have h := actual_flat_current_bound sharp f
  have he := actual_scalar_energy_split f
  have hn : 0≤orthogonalEnergy f := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- The actual flat-current Gram consumes the signed source cost for every mixed pair. -/
theorem actual_joint_flat_current_bound (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) (a b : ℂ) :
    ‖a • embed (flatScalarCurrent sharp (leftState F z hz k))+
      b • embed (flatScalarCurrent sharp (rightState F z hz g))‖^2≤
        rowCost sharp*signedNativeCost F z hz g k a b := by
  rw [actual_joint_native_cost]
  have h := flat_native_bound sharp (jointState F z hz g k a b)
  simpa only [jointState,map_add,map_smul] using! h

private theorem signed_pair_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y u v : E) :
    ‖inner ℂ x u-inner ℂ v y‖^2≤(‖x‖^2+‖y‖^2)*(‖u‖^2+‖v‖^2) := by
  have ht := (norm_sub_le (inner ℂ x u) (inner ℂ v y)).trans
    (add_le_add (norm_inner_le_norm x u) (norm_inner_le_norm v y))
  have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
  nlinarith [sq_nonneg (‖x‖*‖v‖-‖y‖*‖u‖)]

def jointCurrentCost (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) (g k : OriginalCore) : ℝ :=
  rowCost (!sharp)*signedNativeCost F z hz g k 1 0+rowCost sharp*signedNativeCost F z hz g k 0 1

def radialPairSize (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g k : OriginalCore) : ℝ :=
  ‖embed (potentialAction m ell (rightState F z hz g))‖^2+
    ‖embed (potentialAction m ell (leftState F z hz k))‖^2

/-- Direct original common-current consumer, at the same F and with both complete defects. -/
theorem actual_common_signed_square (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) :
    ‖radialResponse sharp m ell F z hz g k+externalMomentum sharp m ell F z hz g k‖^2≤
      jointCurrentCost sharp F z hz g k*radialPairSize m ell F z hz g k := by
  rw [actual_joint_flat_return]
  have hp := actual_joint_flat_current_bound (!sharp) F z hz g k 1 0
  have hq := actual_joint_flat_current_bound sharp F z hz g k 0 1
  simp only [one_smul,zero_smul,add_zero,zero_add] at hp hq
  have hs := signed_pair_bound (embed (flatScalarCurrent (!sharp) (leftState F z hz k)))
    (embed (flatScalarCurrent sharp (rightState F z hz g)))
    (embed (potentialAction m ell (rightState F z hz g)))
    (embed (potentialAction m ell (leftState F z hz k)))
  exact hs.trans (mul_le_mul_of_nonneg_right (add_le_add hp hq) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- The original cofinal Gamma consumes the joint signed source square and its already-paid endpoint. -/
theorem actual_gamma_signed_square (sharp : Bool) (m ell : ℕ) (g k : OriginalCore) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, ∀ hz : z.im≠0,
      ‖SourceGammaNativeBudget.sourceGamma sharp m ell F g k z+
        Complex.I*SourceMovingJetFlux.fixedEndpointProfile sharp m ell F g k z‖^2≤
      ‖SourcePairedMomentumFlux.coefficient‖^2*
        (jointCurrentCost sharp F z hz g k*radialPairSize m ell F z hz g k) := by
  filter_upwards [actual_gamma_external_cofinal sharp m ell g k] with F hF
  intro z hz
  have he : SourceGammaNativeBudget.sourceGamma sharp m ell F g k z+
        Complex.I*SourceMovingJetFlux.fixedEndpointProfile sharp m ell F g k z=
      SourcePairedMomentumFlux.coefficient*Complex.I*
        (radialResponse sharp m ell F z hz g k+externalMomentum sharp m ell F z hz g k) := by
    rw [hF z hz]
    ring
  rw [he,norm_mul,norm_mul,Complex.norm_I,mul_one,mul_pow]
  exact mul_le_mul_of_nonneg_left (actual_common_signed_square sharp m ell F z hz g k) (sq_nonneg _)

end LowEnergy.SourceScalarRetardedGram
