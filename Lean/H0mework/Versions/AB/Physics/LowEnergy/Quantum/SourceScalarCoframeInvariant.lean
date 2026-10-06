import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarGaugeEndpoint
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCoframeScaleTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarCoframeInvariant
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceCoframeVolumeCurrent SourceCoframeScaleTransport
open SourceMixedNativeReturn SourceCutoffDilationWard
open scoped InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

private theorem quantized_adjoint (A : Matrix Mode Mode ℂ) :
    (GaussQuantumMultiplier.quantized A).adjoint=GaussQuantumMultiplier.quantized A.conjTranspose := by
  apply ContinuousLinearMap.ext
  intro psi
  apply ext_inner_left ℂ
  intro phi
  change inner ℂ phi ((GaussQuantumMultiplier.quantized A).adjoint psi)=
    inner ℂ phi (GaussQuantumMultiplier.quantized A.conjTranspose psi)
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact SourceQuantumFockGauge.quantizedFiber_adjoint A phi psi

private theorem branch_weight (sharp : Bool) (t : ℝ) (phi : Scalar) :
    Commute (fiberAmplitude t).toContinuousLinearMap (branchMap sharp phi) := by
  have hw (A : Matrix Mode Mode ℂ) :
      Commute (fiberAmplitude t).toContinuousLinearMap (GaussQuantumMultiplier.quantized A) := by
    change Commute (GaussFockWeights.weight (fun N => (Real.exp ((N+4 : ℝ)*t) : ℂ)))
      (GaussQuantumMultiplier.quantized A)
    exact GaussQuantumMultiplier.weight_commute _ A
  cases sharp
  · change Commute _ (GaussYukawaCoefficient.sourceMap phi)
    rw [GaussYukawaCoefficient.source_map_return]
    exact hw _
  · change Commute _ (GaussFullHamiltonian.adjointMap phi)
    change Commute _ (GaussYukawaCoefficient.sourceMap phi).adjoint
    rw [GaussYukawaCoefficient.source_map_return,quantized_adjoint]
    exact hw _

private theorem full_core_flow (sharp : Bool) (t : ℝ) (f : QuantumTest) :
    fullAction sharp (coreFlow t f)=coreFlow t (fullAction sharp f) := by
  apply DFunLike.ext
  intro z
  have hv (q : QuantumTest) (w : SourceCoordinateSlice) :
      fullAction sharp q w=branchMap sharp (GaussNativePotential.scalarField w) (q w) := by
    cases sharp <;> rfl
  have hs : GaussNativePotential.scalarField (SourceCoframeVolume.scale (rate t) z)=
      GaussNativePotential.scalarField z := rfl
  have hc := congrArg (fun A : FockFiber →L[ℂ] FockFiber =>
    A (f (SourceCoframeVolume.scale (rate t) z))) (branch_weight sharp t (GaussNativePotential.scalarField z)).eq.symm
  calc
    fullAction sharp (coreFlow t f) z =
        branchMap sharp (GaussNativePotential.scalarField z)
          (fiberAmplitude t (f (SourceCoframeVolume.scale (rate t) z))) := by rw [hv]; rfl
    _ = fiberAmplitude t
          (branchMap sharp (GaussNativePotential.scalarField (SourceCoframeVolume.scale (rate t) z))
            (f (SourceCoframeVolume.scale (rate t) z))) := by rw [hs]; exact hc
    _ = coreFlow t (fullAction sharp f) z := by
      change fiberAmplitude t
        (branchMap sharp (GaussNativePotential.scalarField (SourceCoframeVolume.scale (rate t) z))
          (f (SourceCoframeVolume.scale (rate t) z)))=
        fiberAmplitude t (fullAction sharp f (SourceCoframeVolume.scale (rate t) z))
      rw [hv]

private theorem inverse_core_flow (t : ℝ) :
    Commute (coreFlow t) GaussRadialDomain.inverseAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hs : GaussRadialDomain.reciprocal (SourceCoframeVolume.scale (rate t) z)=
      GaussRadialDomain.reciprocal z := rfl
  change fiberAmplitude t
      ((GaussRadialDomain.reciprocal (SourceCoframeVolume.scale (rate t) z) : ℂ) •
        f (SourceCoframeVolume.scale (rate t) z))=
    (GaussRadialDomain.reciprocal z : ℂ) •
      fiberAmplitude t (f (SourceCoframeVolume.scale (rate t) z))
  rw [hs]
  exact map_smul _ _ _

private theorem relative_commute {R : Type*} [Ring R] (a u : R) (m ell : ℕ)
    (h : Commute a u) : Commute a ((1-u)^(m+1)-(1-u)^(ell+1)) :=
  (((Commute.one_right a).sub_right h).pow_right (m+1)).sub_right
    (((Commute.one_right a).sub_right h).pow_right (ell+1))

private theorem theta_core_flow (t : ℝ) (m ell : ℕ) :
    Commute (coreFlow t) (thetaAction m ell) :=
  relative_commute (R := SourceCoframeVolumeCurrent.CoreEnd) (coreFlow t)
    GaussRadialDomain.inverseAction m ell (inverse_core_flow t)

/-- The actual full Yukawa branches and literal cutoff commute with the original coframe flow. -/
theorem actual_full_core_coframe (sharp : Bool) (m ell : ℕ) (t : ℝ) (f : QuantumTest) :
    SourceScalarDoubleEndpoint.fullInsertion sharp m ell (coreFlow t f)=
      coreFlow t (SourceScalarDoubleEndpoint.fullInsertion sharp m ell f) := by
  have htheta := LinearMap.congr_fun (theta_core_flow t m ell).eq f
  change coreFlow t (thetaAction m ell f)=thetaAction m ell (coreFlow t f) at htheta
  change fullAction sharp (thetaAction m ell (coreFlow t f))=_
  rw [←htheta,full_core_flow]
  rfl

private theorem actual_increment_coframe_commute (sharp : Bool) (m ell : ℕ) (t : ℝ) :
    Commute (SourceEscapeSeedTail.actualIncrement sharp m ell)
      (hilbertFlow t).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  refine embed_dense.induction_on
    (p := fun y : H => SourceEscapeSeedTail.actualIncrement sharp m ell (hilbertFlow t y)=
      hilbertFlow t (SourceEscapeSeedTail.actualIncrement sharp m ell y)) x ?_ ?_
  · exact isClosed_eq ((SourceEscapeSeedTail.actualIncrement sharp m ell).continuous.comp (hilbertFlow t).continuous)
      ((hilbertFlow t).continuous.comp (SourceEscapeSeedTail.actualIncrement sharp m ell).continuous)
  · intro f
    rw [hilbertFlow_on_core,literal_increment_core,literal_increment_core,hilbertFlow_on_core]
    have h := congrArg embed (actual_full_core_coframe sharp m ell t f)
    simpa only [SourceScalarDoubleEndpoint.fullInsertion,literal_full_return] using h

/-- The original bounded whole-H insertion is invariant under the true coframe unitary. -/
theorem actual_increment_coframe_invariant (sharp : Bool) (m ell : ℕ) (t : ℝ) :
    (hilbertFlow t).conjStarAlgEquiv (SourceEscapeSeedTail.actualIncrement sharp m ell)=
      SourceEscapeSeedTail.actualIncrement sharp m ell := by
  apply ContinuousLinearMap.ext
  intro x
  change hilbertFlow t (SourceEscapeSeedTail.actualIncrement sharp m ell ((hilbertFlow t).symm x))=
    SourceEscapeSeedTail.actualIncrement sharp m ell x
  have he := congrArg (fun A : H →L[ℂ] H => A ((hilbertFlow t).symm x))
    (actual_increment_coframe_commute sharp m ell t).eq
  change SourceEscapeSeedTail.actualIncrement sharp m ell (hilbertFlow t ((hilbertFlow t).symm x))=
    hilbertFlow t (SourceEscapeSeedTail.actualIncrement sharp m ell ((hilbertFlow t).symm x)) at he
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  exact he.symm

end LowEnergy.SourceScalarCoframeInvariant
