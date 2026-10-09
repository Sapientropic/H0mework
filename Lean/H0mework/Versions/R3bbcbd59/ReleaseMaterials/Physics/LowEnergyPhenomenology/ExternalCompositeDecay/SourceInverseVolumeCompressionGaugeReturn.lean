import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeCompressionGaugeBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseCompressionGaugeReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceInverseCompressionCurrent SourceGaugeCoframeWard SourceGaugeCoframeJets
open SourceInverseFirstCurrentRemainder SourceInverseFirstCurrentGaugeJets SourceInverseProjectionCurrentRemainder
open SourceInverseGaugeSingleDefectJoin SourceInverseCompressionGaugeBudget
open FullYSourceResolventGraphSplice Filter MeasureTheory SourceResolventBandLimit
open scoped InnerProductSpace ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] diagonalAction compressionCore defectAction sourceRead
  firstHamiltonianCurrent singleDefect matterInsertion matterHamiltonianCurrent
  linearDefectJet singleResponseJet derivativeCorrectionJet gaugeDefectResponseJet
  compressionFirst compressionMatter sandwichJet inverseCross inputFlux

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


/-- The source insertions use H0 twice and its matter current; the actual resolvent and input jets remain. -/
def fullGaugeCorrectionJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (n : ℕ) (t : ℝ) : Op :=
  sandwichJet F g z (bracket diagonalAction (firstHamiltonianCurrent sharp m ell)) 0 (n+1) 0 t-
    sandwichJet F g z (matterHamiltonianCurrent sharp m ell) 0 n 0 t

private theorem single_split (sharp : Bool) (m ell : ℕ) (F : Index) :
    singleDefect sharp m ell F=bracket diagonalAction (firstHamiltonianCurrent sharp m ell)-compressionFirst sharp m ell F := by
  unfold singleDefect compressionFirst firstHamiltonianCurrent defectAction bracket
  noncomm_ring
private theorem linear_split (sharp : Bool) (m ell : ℕ) (F : Index) :
    bracket (defectAction F) (matterInsertion sharp m ell)=
      matterHamiltonianCurrent sharp m ell-compressionMatter sharp m ell F := by
  unfold matterHamiltonianCurrent compressionMatter defectAction bracket
  noncomm_ring

/-- The derivative and gauge-defect corrections consume one actual full-H0 current and the paid compression current. -/
theorem actual_correction_split (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) (n : ℕ) (t : ℝ) :
    derivativeCorrectionJet sharp m ell F g z n t+gaugeDefectResponseJet sharp m ell F g z n t=
      fullGaugeCorrectionJet sharp m ell F g z n t-correctedCompressionJet sharp m ell F g z n t := by
  have hj := actual_joined_gauge_jet sharp m ell F g z hz n t
  have hS : singleResponseJet sharp m ell F g z (n+1) t=
      sandwichJet F g z (bracket diagonalAction (firstHamiltonianCurrent sharp m ell)) 0 (n+1) 0 t-
        sandwichJet F g z (compressionFirst sharp m ell F) 0 (n+1) 0 t := by
    unfold singleResponseJet
    rw [single_split,sandwich_sub F g z hz]
  have hL : linearDefectJet sharp m ell F g z n t=
      sandwichJet F g z (matterHamiltonianCurrent sharp m ell) 0 n 0 t-
        sandwichJet F g z (compressionMatter sharp m ell F) 0 n 0 t := by
    unfold SourceInverseFirstCurrentRemainder.linearDefectJet
    rw [linear_split,sandwich_sub F g z hz]
  rw [hS,hL] at hj
  unfold fullGaugeCorrectionJet correctedCompressionJet
  linear_combination (norm := module) hj

def sourceRemainder (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  (1/6 : ℂ) • (joinedPolynomial (fun n => singleResponseJet sharp m ell F g z n 0)-
    gaugeFilter (fun n => fullGaugeCorrectionJet sharp m ell F g z n 0)-
    gaugeFilter (fun n => inverseCross F g z (matterHamiltonianCurrent sharp m ell) 0 n)-
    finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (matterHamiltonianCurrent sharp m ell) 0 n)*
      finiteResolvent F z)+
  finiteResolvent F z*(sourceRead F g
    (-(2*(GaussNativeEnergy.sourceTime 0 : ℂ)^2) • (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
      (2*(GaussNativeEnergy.sourceTime 0 : ℂ)^2) •
        (constantAction sharp SourceQuantumScalarChart.vacuum*SourceMixedNativeReturn.thetaAction m ell)-
      (1/48 : ℂ) • scaleDoubleRemainder sharp m ell)-
    (SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F)*finiteResolvent F z


def paidCompression (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  (1/6 : ℂ) • gaugeFilter (fun n => correctedCompressionJet sharp m ell F g z n 0)

/-- Exact source-word removal of the complete compression correction, not an arbitrary added/subtracted response. -/
theorem actual_remainder_split (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) : joinedRemainder sharp m ell F g z=
      sourceRemainder sharp m ell F g z+paidCompression sharp m ell F g z := by
  have h0 := actual_correction_split sharp m ell F g z hz 0 0
  have h1 := actual_correction_split sharp m ell F g z hz 1 0
  have h2 := actual_correction_split sharp m ell F g z hz 2 0
  simp only [joinedRemainder,sourceRemainder,paidCompression,gaugeFilter]
  linear_combination (norm := module) -(1/6 : ℂ) • h2+(1/2 : ℂ) • h1-(1/3 : ℂ) • h0

/-- The original Ward now returns the original H0 correction and the genuinely paid compression response. -/
theorem actual_ward_source_remainder (m ell : ℕ) (g k : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (sharp : Bool) (z : ℂ),z.im≠0 →
      inner ℂ (embed k) (wardOperator sharp m ell F (coreEquiv g) z (embed g))=
        (1/6 : ℂ)*filteredProfile sharp m ell F z g k+
        inner ℂ (embed k) (sourceRemainder sharp m ell F (coreEquiv g) z (embed g))+
        inner ℂ (embed k) (paidCompression sharp m ell F (coreEquiv g) z (embed g)) := by
  filter_upwards [actual_ward_joined_remainder m ell g k] with F hF sharp z hz
  rw [hF sharp z hz,actual_remainder_split sharp m ell F (coreEquiv g) z hz]
  simp only [add_apply,inner_add_right,add_assoc]

end LowEnergy.SourceInverseCompressionGaugeReturn
