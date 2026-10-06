import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeProjectionCurrentRemainder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseGaugeSingleDefectJoin
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceScalarGaugeScale
open SourceMixedNativeReturn SourceJointScaleBudget SourceRetardedIncrement SourceMinimalGraphParticular
open SourceInverseCompressionCurrent SourceScalarDoubleCurrent SourceScalarGaugeForce SourceGaugeCoframeWard
open SourceGaugeCoframeJets FullYSourceResolventGraphSplice SourceInverseFirstCurrentGaugeJets
open SourceInverseFirstCurrentRemainder SourceInverseProjectionCurrentRemainder Filter
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] diagonalAction scalarKinetic gaugeKinetic GaussCoframeForm.coframeAction matterAction
  sourceRead state sourcePair defectAction compressionCore deltaGauge
  SourceScalarDoubleCurrent.fullInsertion SourceMixedNativeReturn.fullAction SourceMixedNativeReturn.thetaAction
  singleDefect singleDefectRemainder linearDefectJet matterInsertion matterHamiltonianCurrent
  readOrbitJet sandwichJet inverseCross inputFlux resolventJet
  cutoffEuler scaleDoubleRemainder constantAction SourceScalarForceBudget.solverOperator
  SourceScalarForceBudget.oscillatorMass wardOperator

/-- The fixed original H-current shared by both projected defect terms. -/
def firstHamiltonianCurrent (sharp : Bool) (m ell : ℕ) : End :=
  bracket diagonalAction (SourceScalarDoubleCurrent.fullInsertion sharp m ell)

/-- The actual gauge derivative of H minus the actual gauge derivative of the graded compression. -/
def gaugeDefect (F : Index) : End :=
  deltaGauge diagonalAction-
    (SourceGaugeRadialPair.gaugeEulerAction*compressionCore F-
      compressionCore F*SourceGaugeRadialPair.gaugeEulerAction)

def gaugeDefectCurrent (sharp : Bool) (m ell : ℕ) (F : Index) : End :=
  bracket (gaugeDefect F) (firstHamiltonianCurrent sharp m ell)

private theorem gauge_product (A B : End) : deltaGauge (A*B)=deltaGauge A*B+A*deltaGauge B := by
  unfold deltaGauge
  change SourceGaugeRadialPair.gaugeEulerAction*(A*B)-(A*B)*SourceGaugeRadialPair.gaugeEulerAction=
    (SourceGaugeRadialPair.gaugeEulerAction*A-A*SourceGaugeRadialPair.gaugeEulerAction)*B+
      A*(SourceGaugeRadialPair.gaugeEulerAction*B-B*SourceGaugeRadialPair.gaugeEulerAction)
  noncomm_ring

private theorem gauge_bracket (A B : End) :
    deltaGauge (bracket A B)=bracket (deltaGauge A) B+bracket A (deltaGauge B) := by
  simp only [bracket,map_sub,gauge_product]
  noncomm_ring

private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (SourceMixedNativeReturn.fullAction sharp) := by
  unfold SourceMixedNativeReturn.fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarField z)) (c z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z : ℂ) (f z)).symm

private theorem real_theta (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (m ell : ℕ) :
    Commute (multiply c hc) (SourceMixedNativeReturn.thetaAction m ell) := by
  unfold SourceMixedNativeReturn.thetaAction
  change Commute (multiply c hc) ((1-GaussRadialDomain.inverseAction)^(m+1)-(1-GaussRadialDomain.inverseAction)^(ell+1))
  rw [←SourceNativeCutoffContact.theta_action_polynomial]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)

private theorem polynomial_commute {R : Type*} [Ring R] (A B : R) (m ell : ℕ) (h : Commute A B) :
    Commute A ((1-B)^(m+1)-(1-B)^(ell+1)) :=
  ((Commute.one_right A).sub_right h |>.pow_right _).sub_right
    ((Commute.one_right A).sub_right h |>.pow_right _)

private theorem first_current_split (sharp : Bool) (m ell : ℕ) :
    firstHamiltonianCurrent sharp m ell=
      bracket (scalarKinetic+GaussCoframeForm.coframeAction) (SourceScalarDoubleCurrent.fullInsertion sharp m ell)+
        matterInsertion sharp m ell := by
  have hp : multiply potential potential_smooth*SourceScalarDoubleCurrent.fullInsertion sharp m ell=
      SourceScalarDoubleCurrent.fullInsertion sharp m ell*multiply potential potential_smooth := by
    unfold SourceScalarDoubleCurrent.fullInsertion
    exact ((real_full potential potential_smooth sharp).mul_right (real_theta potential potential_smooth m ell)).eq
  have ht : Commute gaugeKinetic (SourceMixedNativeReturn.thetaAction m ell) := by
    unfold SourceMixedNativeReturn.thetaAction
    exact polynomial_commute _ _ m ell GaussRadialHamiltonian.gauge_commutes
  have hg : gaugeKinetic*SourceScalarDoubleCurrent.fullInsertion sharp m ell=
      SourceScalarDoubleCurrent.fullInsertion sharp m ell*gaugeKinetic := by
    unfold SourceScalarDoubleCurrent.fullInsertion
    exact ((original_electric_full sharp).mul_right ht).eq
  have hH : diagonalAction=scalarKinetic+gaugeKinetic+multiply potential potential_smooth+
      GaussCoframeForm.coframeAction+matterAction := by rw [diagonalAction,nativeAction]
  rw [firstHamiltonianCurrent,hH]
  unfold matterInsertion bracket
  linear_combination (norm := noncomm_ring) hp+hg

/-- The actual gauge derivative of the original first H-current is exactly the lower matter insertion. -/
theorem original_first_current_gauge (sharp : Bool) (m ell : ℕ) :
    deltaGauge (firstHamiltonianCurrent sharp m ell)=matterInsertion sharp m ell := by
  have hi := original_insertion_gauge_scale sharp m ell
  have hW : deltaGauge (matterInsertion sharp m ell)=matterInsertion sharp m ell := by
    rw [matterInsertion,gauge_bracket,original_matter_gauge,hi]
    simp only [bracket,mul_zero,zero_mul,sub_self,add_zero]
  rw [first_current_split,map_add,gauge_bracket,map_add,original_scalar_kinetic_gauge,
    original_coframe_gauge,add_zero,hi,hW]
  simp only [bracket,zero_mul,mul_zero,sub_self,zero_add]

/-- No derivative of the finite graded compression is discarded or supplied externally. -/
theorem original_gauge_defect (F : Index) : deltaGauge (defectAction F)=gaugeDefect F := by
  unfold defectAction
  rw [map_sub]
  unfold gaugeDefect deltaGauge
  rfl

/-- Both previous defect forces are now restrictions of the same source current and its actual gauge derivative. -/
theorem original_single_defect_gauge (sharp : Bool) (m ell : ℕ) (F : Index) :
    bracket (defectAction F) (matterInsertion sharp m ell)=
      deltaGauge (singleDefect sharp m ell F)-gaugeDefectCurrent sharp m ell F := by
  have hg := gauge_bracket (defectAction F) (firstHamiltonianCurrent sharp m ell)
  rw [original_gauge_defect,original_first_current_gauge] at hg
  simpa only [singleDefect,gaugeDefectCurrent,firstHamiltonianCurrent] using!
    eq_sub_of_add_eq (add_comm _ _ |>.trans hg.symm)

attribute [local irreducible] firstHamiltonianCurrent gaugeDefect gaugeDefectCurrent

private theorem origin_conjugate (A : Op) : (mixedHilbert 0 0).conjStarAlgEquiv A=A := by
  have hu (x : H) : mixedHilbert 0 0 x=x := by
    simp only [mixedHilbert,LinearIsometryEquiv.trans_apply,coframeHilbert,mul_zero,
      SourceCoframeScaleTransport.hilbertFlow_zero,SourceGaugeScaleTransport.hilbertFlow_zero]
  apply ContinuousLinearMap.ext
  intro x
  change mixedHilbert 0 0 (A ((mixedHilbert 0 0).symm x))=A x
  have hi : (mixedHilbert 0 0).symm x=x := by
    apply (mixedHilbert 0 0).injective
    rw [LinearIsometryEquiv.apply_symm_apply,hu]
  rw [hi,hu]

private theorem map_sandwich {R : Type*} [Ring R] [Module ℂ R] [Star R]
    (e : R ≃⋆ₐ[ℂ] R) (r a : R) : e r*(e a*e r)=e (r*a*r) := by
  simp only [map_mul,mul_assoc]

private theorem sandwich_orbit (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End) (t : ℝ) :
    sandwichJet F g z A 0 0 0 t=(mixedHilbert 0 t).conjStarAlgEquiv
      (finiteResolvent F z*sourceRead F g A*finiteResolvent F z) := by
  unfold sandwichJet
  change resolventJet F z 0 0 0 t*(readOrbitJet F g A 0 0 0 t*resolventJet F z 0 0 0 t)=_
  exact (congrArg₂ (fun r a : Op => r*(a*r))
    (actual_mixed_resolvent F z hz 0 t) (actual_read_orbit F g A 0 t)).trans
      (map_sandwich _ _ _)

private theorem map_sandwich_sub {R : Type*} [Ring R] [Module ℂ R] [Star R]
    (e : R ≃⋆ₐ[ℂ] R) (r a b : R) : e (r*(a-b)*r)=e (r*a*r)-e (r*b*r) := by
  simp only [mul_sub,sub_mul,map_sub]

private theorem sandwich_sub (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0)
    (A B : End) (n : ℕ) (t : ℝ) :
    sandwichJet F g z (A-B) 0 n 0 t=sandwichJet F g z A 0 n 0 t-sandwichJet F g z B 0 n 0 t := by
  induction n generalizing t with
  | zero =>
    have hr := sandwich_orbit F g z hz (A-B) t
    have hm : sourceRead F g (A-B)=sourceRead F g A-sourceRead F g B := map_sub (sourceRead F g) A B
    have he := congrArg (fun a : Op => (mixedHilbert 0 t).conjStarAlgEquiv
      (finiteResolvent F z*a*finiteResolvent F z)) hm
    have ho := congrArg₂ (fun a b : Op => a-b) (sandwich_orbit F g z hz A t) (sandwich_orbit F g z hz B t)
    exact hr.trans (he.trans ((map_sandwich_sub _ _ _ _).trans ho.symm))
  | succ n ih =>
    have hd := (sandwich_gauge_derivative F g z A 0 n 0 t).sub (sandwich_gauge_derivative F g z B 0 n 0 t)
    exact (sandwich_gauge_derivative F g z (A-B) 0 n 0 t).unique
      (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall ih))

/-- Actual norm jets of the complete one-defect response. -/
def singleResponseJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (n : ℕ) (t : ℝ) : Op := sandwichJet F g z (singleDefect sharp m ell F) 0 n 0 t

def gaugeDefectResponseJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (n : ℕ) (t : ℝ) : Op := sandwichJet F g z (gaugeDefectCurrent sharp m ell F) 0 n 0 t

/-- This is the jet of the actual inverse/input correction, with its origin identified below. -/
def derivativeCorrectionJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (n : ℕ) (t : ℝ) : Op :=
  singleResponseJet sharp m ell F g z (n+1) t-
    sandwichJet F g z (deltaGauge (singleDefect sharp m ell F)) 0 n 0 t

private theorem inverse_cross_one (F : Index) (g : diagonal.domain) (z : ℂ)
    (hz : z.im≠0) (A : End) :
    inverseCross F g z A 0 1=sandwichJet F g z A 0 1 0 0-
      finiteResolvent F z*readOrbitJet F g A 0 1 0 0*finiteResolvent F z := by
  simp only [inverseCross,resolved_inverse_return F z hz,sandwichJet]
  rfl

/-- The new correction starts at the paid original two-inverse cross and the complete moving-input flux. -/
theorem actual_derivative_correction_origin (sharp : Bool) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    derivativeCorrectionJet sharp m ell F g z 0 0=
      inverseCross F g z (singleDefect sharp m ell F) 0 1+
      finiteResolvent F z*inputFlux F g (singleDefect sharp m ell F) 0 1*finiteResolvent F z := by
  let U := singleDefect sharp m ell F
  have hi := inverse_cross_one F g z hz U
  have ho := (sandwich_orbit F g z hz (deltaGauge U) 0).trans (origin_conjugate _)
  have hf : inputFlux F g U 0 1=readOrbitJet F g U 0 1 0 0-sourceRead F g (deltaGauge U) := by
    simp only [inputFlux,coreJet,pow_zero,pow_one,Module.End.one_apply]
  have hs := congrArg (fun a : Op => finiteResolvent F z*a*finiteResolvent F z) hf
  simp only [mul_sub,sub_mul] at hs
  change singleResponseJet sharp m ell F g z 1 0-sandwichJet F g z (deltaGauge U) 0 0 0 0=_
  unfold singleResponseJet
  dsimp only [U] at hi ho hs ⊢
  linear_combination (norm := module) -hi-hs-ho

/-- Every correction jet is an actual norm derivative, not an externally supplied field. -/
theorem actual_derivative_correction_derivative (sharp : Bool) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (z : ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt (derivativeCorrectionJet sharp m ell F g z n)
      (derivativeCorrectionJet sharp m ell F g z (n+1) t) t :=
  (sandwich_gauge_derivative F g z (singleDefect sharp m ell F) 0 (n+1) 0 t).sub
    (sandwich_gauge_derivative F g z (deltaGauge (singleDefect sharp m ell F)) 0 n 0 t)

/-- The old first defect jets and the projection defect now share one actual response family. -/
theorem actual_joined_gauge_jet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) (n : ℕ) (t : ℝ) :
    linearDefectJet sharp m ell F g z n t=
      singleResponseJet sharp m ell F g z (n+1) t-derivativeCorrectionJet sharp m ell F g z n t-
        gaugeDefectResponseJet sharp m ell F g z n t := by
  have hs := congrArg (fun A : End => sandwichJet F g z A 0 n 0 t)
    (original_single_defect_gauge sharp m ell F)
  have hl := hs.trans (sandwich_sub F g z hz (deltaGauge (singleDefect sharp m ell F))
    (gaugeDefectCurrent sharp m ell F) n t)
  simpa only [linearDefectJet,derivativeCorrectionJet,gaugeDefectResponseJet,sub_sub_cancel] using! hl

attribute [local irreducible] singleResponseJet derivativeCorrectionJet gaugeDefectResponseJet

/-- This polynomial joins Pg applied to the first source current with the original negative projection term. -/
def joinedPolynomial (J : ℕ → Op) : Op := J 3-(3 : ℂ) • J 2+(2 : ℂ) • J 1-(6 : ℂ) • J 0

def joinedRemainder (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  (1/6 : ℂ) • (joinedPolynomial (fun n => singleResponseJet sharp m ell F g z n 0)-
    gaugeFilter (fun n => derivativeCorrectionJet sharp m ell F g z n 0)-
    gaugeFilter (fun n => gaugeDefectResponseJet sharp m ell F g z n 0)-
    gaugeFilter (fun n => inverseCross F g z (matterHamiltonianCurrent sharp m ell) 0 n)-
    finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (matterHamiltonianCurrent sharp m ell) 0 n)*
      finiteResolvent F z)+
  finiteResolvent F z*(sourceRead F g
    (-(2*(GaussNativeEnergy.sourceTime 0 : ℂ)^2) • (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
      (2*(GaussNativeEnergy.sourceTime 0 : ℂ)^2) •
        (constantAction sharp SourceQuantumScalarChart.vacuum*SourceMixedNativeReturn.thetaAction m ell)-
      (1/48 : ℂ) • scaleDoubleRemainder sharp m ell)-
    (SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F)*finiteResolvent F z

/-- The full signed old remainder consumes the joined polynomial and keeps the generated gauge-defect correction. -/
theorem actual_joined_remainder (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) : singleDefectRemainder sharp m ell F g z=joinedRemainder sharp m ell F g z := by
  have h0 := actual_joined_gauge_jet sharp m ell F g z hz 0 0
  have h1 := actual_joined_gauge_jet sharp m ell F g z hz 1 0
  have h2 := actual_joined_gauge_jet sharp m ell F g z hz 2 0
  have ho : singleResponseJet sharp m ell F g z 0 0=
      finiteResolvent F z*sourceRead F g (singleDefect sharp m ell F)*finiteResolvent F z := by
    unfold singleResponseJet
    exact (sandwich_orbit F g z hz (singleDefect sharp m ell F) 0).trans (origin_conjugate _)
  simp only [singleDefectRemainder,joinedRemainder,gaugeFilter,joinedPolynomial,mul_sub,sub_mul]
  linear_combination (norm := module) (1/6 : ℂ) • h2-(1/2 : ℂ) • h1+(1/3 : ℂ) • h0+ho

/-- Same source, actual two legs, and the original cofinal cutoff order: the complete Ward now uses one joined defect current. -/
theorem actual_ward_joined_remainder (m ell : ℕ) (g k : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ (sharp : Bool) (z : ℂ), z.im≠0 →
      inner ℂ (embed k) (wardOperator sharp m ell F (coreEquiv g) z (embed g))=
        (1/6 : ℂ)*filteredProfile sharp m ell F z g k+
        inner ℂ (embed k) (joinedRemainder sharp m ell F (coreEquiv g) z (embed g)) := by
  filter_upwards [actual_ward_single_defect m ell g k] with F hF
  intro sharp z hz
  have he := congrArg (fun A : Op => inner ℂ (embed k) (A (embed g)))
    (actual_joined_remainder sharp m ell F (coreEquiv g) z hz)
  exact (hF sharp z hz).trans (congrArg (fun a : ℂ => (1/6 : ℂ)*filteredProfile sharp m ell F z g k+a) he)

end LowEnergy.SourceInverseGaugeSingleDefectJoin
