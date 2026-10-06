import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeChannelSourceJets
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseFullResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseGapWardDescent
open GaussNativeForm GaussNativeEnergy GaussFockPair GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceInverseNoetherChannelGap SourceInverseChannelSourceJets SourceJointResidualEnergy GaussAdjointHistory
open SourceScalarPositiveBulkWard SourceScalarInverseBulk SourceInverseNoetherEnergy SourcePhysicalKineticSquare
open SourceScalarPairedTransport SourceInverseFullResponse SourceScalarVirialBulk
open Filter
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction compressionCore inverseVolumeAction inverseSymmetricScale
  inverseWeightedBulkJet bulkAction sourcePair raisedDefect channelTest

def wardResponse : PairMatrix →ₗ[ℂ] PairMatrix where
  toFun P := InverseVolumeWardAlgebra.inverseWard (pairDelta Phi) (pairDelta Gauge) (pairDelta Coframe)
    (vacuumJetCoefficient : ℂ) P
  map_add' P Q := by
    simp only [InverseVolumeWardAlgebra.inverseWard,InverseVolumeWardAlgebra.mixedPolynomial,
      InverseVolumeWardAlgebra.affinePolynomial,InverseVolumeWardAlgebra.inverseLocalPolynomial,
      map_add,map_sub,map_smul,smul_add,smul_sub,smul_smul]
    module
  map_smul' c P := by
    simp only [InverseVolumeWardAlgebra.inverseWard,InverseVolumeWardAlgebra.mixedPolynomial,
      InverseVolumeWardAlgebra.affinePolynomial,InverseVolumeWardAlgebra.inverseLocalPolynomial,
      map_add,map_sub,map_smul,smul_add,smul_sub,smul_smul,RingHom.id_apply]
    module

def inversePair (F : Index) (k g : diagonal.domain) (u v : Channel F) : PairMatrix :=
  responseRead (channelTest F k u) (channelTest F g v) inverseVolumeAction

/-- Both raised defects remain in their original signed source pairing. -/
def fluxPair (F : Index) (k g : diagonal.domain) (u v : Channel F) : PairMatrix := fun A B =>
  (1/2 : ℂ)*(sourcePair (raisedDefect F A (channelTest F k u))
      (inverseVolumeAction (B (channelTest F g v)))+
    sourcePair (inverseVolumeAction (A (channelTest F k u)))
      (raisedDefect F B (channelTest F g v)))

private theorem inverse_pair (f g : QuantumTest) :
    sourcePair f (inverseVolumeAction g)=sourcePair (inverseVolumeAction f) g := by
  unfold inverseVolumeAction
  exact multiply_pair _ _ _ _

private theorem raised_channel (F : Index) (g : diagonal.domain) (u : Channel F) (A : End) :
    diagonalAction (A (channelTest F g u))=
      (channelValue F u : ℂ) • A (channelTest F g u)+raisedDefect F A (channelTest F g u) := by
  have h : raisedDefect F A (channelTest F g u)=
      diagonalAction (A (channelTest F g u))-A (compressionCore F (channelTest F g u)) := by
    simp only [raisedDefect,defectAction,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
    abel
  rw [h,actual_channel_eigen,map_smul]
  abel

private theorem channel_scale_pair (F : Index) (k g : diagonal.domain) (u v : Channel F) :
    responseRead (channelTest F k u) (channelTest F g v) inverseSymmetricScale=
      ((1/2 : ℂ)*((channelValue F u : ℂ)+(channelValue F v : ℂ))) • inversePair F k g u v+
        fluxPair F k g u v := by
  ext A B
  change sourcePair (A (channelTest F k u)) (inverseSymmetricScale (B (channelTest F g v)))=_
  rw [inverseSymmetricScale]
  simp only [LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply]
  have hs (a : ℂ) (f h : QuantumTest) : sourcePair f (a • h)=a*sourcePair f h := by
    simp only [sourcePair,map_smul,inner_smul_right]
  have ha (f h j : QuantumTest) : sourcePair f (h+j)=sourcePair f h+sourcePair f j := by
    simp only [sourcePair,map_add,inner_add_right]
  rw [hs,ha,diagonalAction_pair,inverse_pair,raised_channel,raised_channel]
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,
    inner_smul_right,Complex.conj_ofReal,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  change _=((1/2 : ℂ)*((channelValue F u : ℂ)+(channelValue F v : ℂ)))*
    sourcePair (A (channelTest F k u)) (inverseVolumeAction (B (channelTest F g v)))+
    fluxPair F k g u v A B
  have hi := inverse_pair (A (channelTest F k u)) (B (channelTest F g v))
  have hfl := inverse_pair (raisedDefect F A (channelTest F k u)) (B (channelTest F g v))
  have hfr := inverse_pair (A (channelTest F k u)) (raisedDefect F B (channelTest F g v))
  simp only [sourcePair] at hi hfl hfr
  unfold fluxPair
  simp only [sourcePair]
  rw [←hi,←hfl,←hfr]
  ring

/-- The original source Ward polynomial is applied before estimating any cross-spectral bulk pairing. -/
theorem actual_bulk_ward_pair (F : Index) (k g : diagonal.domain) (u v : Channel F) (A B : End) :
    sourcePair (A (channelTest F k u)) (bulkAction (B (channelTest F g v)))=
      wardResponse
        (((1/2 : ℂ)*((channelValue F u : ℂ)+(channelValue F v : ℂ))) • inversePair F k g u v+
          fluxPair F k g u v) A B := by
  have h := original_response_ward (channelTest F k u) (channelTest F g v) inverseSymmetricScale A B
  rw [original_inverse_bulk_symmetric_jet] at h
  rw [←bulkAction] at h
  change sourcePair (A (channelTest F k u)) (bulkAction (B (channelTest F g v)))=
    InverseVolumeWardAlgebra.inverseWard (pairDelta Phi) (pairDelta Gauge) (pairDelta Coframe)
      (vacuumJetCoefficient : ℂ) _ A B
  rw [←channel_scale_pair]
  exact h

private theorem inverse_jet_pair (F : Index) (k g : diagonal.domain) (u v : Channel F)
    (hk : channelTest F (iterate 2 k) u=(channelValue F u : ℂ)^2 • channelTest F k u)
    (hg : channelTest F (iterate 2 g) v=(channelValue F v : ℂ)^2 • channelTest F g v) :
    inversePair F (iterate 2 k) g u v-inversePair F k (iterate 2 g) u v=
      (((channelValue F u : ℂ)^2-(channelValue F v : ℂ)^2)) • inversePair F k g u v := by
  ext A B
  change sourcePair (A (channelTest F (iterate 2 k) u)) (inverseVolumeAction (B (channelTest F g v)))-
    sourcePair (A (channelTest F k u)) (inverseVolumeAction (B (channelTest F (iterate 2 g) v)))=
      ((channelValue F u : ℂ)^2-(channelValue F v : ℂ)^2)*
        sourcePair (A (channelTest F k u)) (inverseVolumeAction (B (channelTest F g v)))
  rw [hk,hg]
  have hp (a : ℂ) (f h : QuantumTest) : sourcePair (a • f) h=star a*sourcePair f h := by
    simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
  have hq (a : ℂ) (f h : QuantumTest) : sourcePair f (a • h)=a*sourcePair f h := by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [map_smul,map_smul,map_smul,hp,hq]
  have hu : star ((channelValue F u : ℂ)^2)=(channelValue F u : ℂ)^2 := by simp
  rw [hu]
  ring

/-- Squared spectral values become fixed original H0² sources on one common event; the full raised-defect Ward flux remains. -/
theorem actual_gap_ward_source_descent (k g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (u v : Channel F) (A B : End),
      (Complex.I/2)*((channelValue F u : ℂ)-(channelValue F v : ℂ))*
        sourcePair (A (channelTest F k u)) (bulkAction (B (channelTest F g v)))=
      (Complex.I/4)*(wardResponse (inversePair F (iterate 2 k) g u v-inversePair F k (iterate 2 g) u v)) A B+
        (Complex.I/2)*((channelValue F u : ℂ)-(channelValue F v : ℂ))*(wardResponse (fluxPair F k g u v)) A B := by
  filter_upwards [actual_channel_source_jet 2 k,actual_channel_source_jet 2 g] with F hk hg u v A B
  rw [actual_bulk_ward_pair,inverse_jet_pair F k g u v (hk u) (hg v)]
  simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- The actual diagonal source current consumes the same source-jet descent at every transition. -/
theorem actual_current_source_descent (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (u v : Channel F) (T : End),
      currentPair F T (channelTest F g u) (channelTest F g v)=
        (Complex.I/4)*(wardResponse (inversePair F (iterate 2 g) g u v-inversePair F g (iterate 2 g) u v)) T T+
        (Complex.I/2)*((channelValue F u : ℂ)-(channelValue F v : ℂ))*(wardResponse (fluxPair F g g u v)) T T := by
  filter_upwards [actual_gap_ward_source_descent g g] with F hF u v T
  rw [actual_channel_gap]
  exact hF u v T T

/-- The full source profile is evaluated from fixed H0² inputs plus the retained Ward flux. -/
def descentPair (F : Index) (z : ℂ) (g : diagonal.domain) (T : End) : ℂ :=
  ∑ u : Channel F,∑ v : Channel F,
    star (((channelValue F u : ℂ)-z)⁻¹)*((channelValue F v : ℂ)-z)⁻¹*
      ((Complex.I/4)*(wardResponse (inversePair F (iterate 2 g) g u v-inversePair F g (iterate 2 g) u v)) T T+
        (Complex.I/2)*((channelValue F u : ℂ)-(channelValue F v : ℂ))*(wardResponse (fluxPair F g g u v)) T T)

theorem actual_retarded_source_descent (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (z : ℂ) (hz : z.im≠0) (T : End),
      (raisedNoetherCurrent F T (state F z hz g) : ℂ)=descentPair F z g T := by
  filter_upwards [actual_current_source_descent g] with F hF z hz T
  rw [actual_current_gap_expansion]
  unfold descentPair
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [←actual_channel_gap,hF]

open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory

def descentCurrent (F : Index) (μ : ℝ) (g k : diagonal.domain) (T : End) : ℝ :=
  ∫ w : ℝ,‖finiteResolvent F (star (line μ w)) (k : H)‖^2*(descentPair F (line μ w) g T).re

theorem actual_current_descent_integral (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (μ : ℝ) (_hμ : 0<μ) (k : diagonal.domain) (T : End),
      gapCurrent F μ g k T=descentCurrent F μ g k T := by
  filter_upwards [actual_retarded_source_descent g] with F hF μ hμ k T
  unfold gapCurrent descentCurrent
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => by
    have hz : (line μ w).im≠0 := by simpa only [line_im] using hμ.ne'
    have he := (actual_current_gap_expansion F (line μ w) hz g T).symm.trans (hF _ hz T)
    exact congrArg (fun c : ℂ => ‖finiteResolvent F (star (line μ w)) (k : H)‖^2*c.re) he)

theorem actual_original_source_descent_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        SourceFourPoleEnergyClosed.closedJointCost sharp m ell F μ (g : H) (k : H) ≤
          ε+(4*SourceScalarSignedInverseReturn.formPrice sharp/μ)*
            descentCurrent F μ g k (SourceScalarInverseRetardedBudget.theta m ell) := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_original_gap_budget sharp μ hμ g k ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell,actual_current_descent_integral g] with F hF hD
  simpa only [hD μ hμ k] using hF

end LowEnergy.SourceInverseGapWardDescent
