import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeDefectCurrentResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseElectricCurrentForm
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open GaussLiveMomentum SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceInverseCompressionCurrent SourceScalarDoubleCurrent SourceScalarGaugeForce SourceDilationRemainder
open SourceMixedNativeReturn SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceInverseDefectCurrentResponse
open FullYSourceResolventGraphSplice
open SourceQuantumGaugeSliceCoordinates
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] gaugeKinetic matterAction matterInsertion sourcePair state sourceRead
  SourceMixedNativeReturn.fullAction SourceMixedNativeReturn.thetaAction SourceScalarDoubleCurrent.fullInsertion

private theorem polynomial_commute (A : End) (h : Commute A GaussRadialDomain.inverseAction)
    (m ell : ℕ) : Commute A (SourceMixedNativeReturn.thetaAction m ell) := by
  unfold SourceMixedNativeReturn.thetaAction
  exact ((Commute.one_right A).sub_right h |>.pow_right _).sub_right
    ((Commute.one_right A).sub_right h |>.pow_right _)

private theorem real_local (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val)
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (hA : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val) :
    Commute (multiply c hc) (localMultiplier A hA) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (A z) (c z : ℂ) (f z)).symm

private theorem real_insertion (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) (sharp : Bool) (m ell : ℕ) :
    Commute (multiply c hc) (matterInsertion sharp m ell) := by
  have hM : Commute (multiply c hc) matterAction := by
    unfold matterAction
    apply Commute.sum_right
    intro i _
    apply Commute.sum_right
    intro b _
    exact real_local _ _ _ _
  have hY : Commute (multiply c hc) (SourceMixedNativeReturn.fullAction sharp) := by
    unfold SourceMixedNativeReturn.fullAction
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    cases sharp
    · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarField z)) (c z : ℂ) (f z)).symm
    · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z : ℂ) (f z)).symm
  have hT := polynomial_commute _ (GaussRadialHamiltonian.real_commutes c hc) m ell
  have hX : Commute (multiply c hc) (SourceScalarDoubleCurrent.fullInsertion sharp m ell) := by
    unfold SourceScalarDoubleCurrent.fullInsertion
    exact hY.mul_right hT
  unfold matterInsertion bracket
  exact (hM.mul_right hX).sub_right (hX.mul_right hM)

/-- The genuine electric force has no signed spatial contribution. -/
theorem original_electric_force (sharp : Bool) (m ell : ℕ) :
    electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell)=
      bracket gaugeKinetic (matterInsertion sharp m ell) := by
  have hs : Commute spatialAction (matterInsertion sharp m ell) := real_insertion _ _ sharp m ell
  rw [original_electric_matter_current,←matterInsertion,electricSpatial]
  unfold bracket
  linear_combination (norm := noncomm_ring) hs.eq

/-- This is a derivative of the original local matter/Yukawa coefficient, not a new current input. -/
def current (sharp : Bool) (v : Ambient) : End :=
  bracket (covariantMomentum v) (bracket matterAction (SourceMixedNativeReturn.fullAction sharp))

def windowCurrent (sharp : Bool) (m ell : ℕ) (v : Ambient) : End :=
  bracket (covariantMomentum v) (matterInsertion sharp m ell)

/-- Actual gauge directions commute with the original radial window. -/
theorem original_window_current (sharp : Bool) (m ell : ℕ) (v : Ambient) (hv : v.1=0) :
    windowCurrent sharp m ell v=SourceMixedNativeReturn.thetaAction m ell*current sharp v := by
  have ht := (polynomial_commute _ (GaussRadialHamiltonian.gauge_momentum v hv) m ell).eq
  rw [windowCurrent,original_matter_insertion_radial]
  unfold current bracket
  linear_combination (norm := noncomm_ring) ht*(matterAction*SourceMixedNativeReturn.fullAction sharp-
    SourceMixedNativeReturn.fullAction sharp*matterAction)

private theorem pair_sub_right (p q r : QuantumTest) : sourcePair p (q-r)=sourcePair p q-sourcePair p r := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_sub_left (p q r : QuantumTest) : sourcePair (p-q) r=sourcePair p r-sourcePair q r := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_add_right (p q r : QuantumTest) : sourcePair p (q+r)=sourcePair p q+sourcePair p r := by
  simp only [sourcePair,map_add,inner_add_right]

private theorem pair_sum_right {ι : Type*} [Fintype ι] (p : QuantumTest) (f : ι → QuantumTest) :
    sourcePair p (∑ i,f i)=∑ i,sourcePair p (f i) := by
  simp only [sourcePair,map_sum,inner_sum]
private theorem pair_half (p f : QuantumTest) :
    sourcePair p ((1/2 : ℂ) • f)=(1/2 : ℂ)*sourcePair p f := by
  simp only [sourcePair,map_smul,inner_smul_right]

private theorem sandwich_current (sharp : Bool) (m ell : ℕ) (v w : Ambient)
    (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (p q : QuantumTest) :
    sourcePair p (bracket (sandwich v w c hc) (matterInsertion sharp m ell) q)=
      sourcePair (covariantMomentum v p) (multiply c hc (windowCurrent sharp m ell w q))+
      sourcePair (windowCurrent (!sharp) m ell v p) (multiply c hc (covariantMomentum w q)) := by
  have hC := (real_insertion c hc sharp m ell).eq
  have hOp : bracket (sandwich v w c hc) (matterInsertion sharp m ell)=
      GaussMomentumAdjoint.adjoint v*multiply c hc*windowCurrent sharp m ell w+
      bracket (GaussMomentumAdjoint.adjoint v) (matterInsertion sharp m ell)*multiply c hc*covariantMomentum w := by
    unfold sandwich windowCurrent bracket
    change (GaussMomentumAdjoint.adjoint v*(multiply c hc*covariantMomentum w))*matterInsertion sharp m ell-
      matterInsertion sharp m ell*(GaussMomentumAdjoint.adjoint v*(multiply c hc*covariantMomentum w))=_
    linear_combination (norm := noncomm_ring) GaussMomentumAdjoint.adjoint v*hC*covariantMomentum w
  rw [hOp]
  simp only [LinearMap.add_apply,Module.End.mul_apply,pair_add_right]
  rw [GaussNativeForm.adjoint_pair]
  congr 1
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_right]
  rw [GaussNativeForm.adjoint_pair,original_matter_insertion_pair,
    original_matter_insertion_pair,GaussNativeForm.adjoint_pair]
  simp only [windowCurrent,bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_left]
  ring

/-- Both source legs carry one gauge momentum; the whole electric second-order word is consumed. -/
theorem original_electric_form (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell) q)=
      (1/2 : ℂ)*∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3,
        (sourcePair (covariantMomentum (gaugeDirection i a) p)
          (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
            (SourceMixedNativeReturn.thetaAction m ell (current sharp (gaugeDirection j a) q)))+
        sourcePair (SourceMixedNativeReturn.thetaAction m ell (current (!sharp) (gaugeDirection i a) p))
          (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
            (covariantMomentum (gaugeDirection j a) q))) := by
  rw [original_electric_force]
  have hs : bracket gaugeKinetic (matterInsertion sharp m ell)=
      (1/2 : ℂ) • ∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3,
        bracket (sandwich (gaugeDirection i a) (gaugeDirection j a)
          (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) (matterInsertion sharp m ell) := by
    simp only [gaugeKinetic,bracket,smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum,
      Finset.sum_sub_distrib,smul_sub]
  rw [hs]
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,pair_half,pair_sum_right]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [sandwich_current,original_window_current sharp m ell _ rfl,
    original_window_current (!sharp) m ell _ rfl]
  rfl

/-- The same identity directly consumes the actual nonreal-frequency sourceRead sandwich. -/
theorem actual_electric_response_form (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    inner ℂ (k : H) ((finiteResolvent F z*sourceRead F g
      (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell))*finiteResolvent F z) (g : H))=
      (1/2 : ℂ)*∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3,
        (sourcePair (covariantMomentum (gaugeDirection i a)
          (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k))
          (multiply (fun x => gaugeWeight x i j) (gaugeWeight_smooth i j)
            (SourceMixedNativeReturn.thetaAction m ell (current sharp (gaugeDirection j a) (state F z hz g))))+
        sourcePair (SourceMixedNativeReturn.thetaAction m ell (current (!sharp) (gaugeDirection i a)
          (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)))
          (multiply (fun x => gaugeWeight x i j) (gaugeWeight_smooth i j)
            (covariantMomentum (gaugeDirection j a) (state F z hz g)))) := by
  rw [actual_read_pair,original_electric_form]

end LowEnergy.SourceInverseElectricCurrentForm
