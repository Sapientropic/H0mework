import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeCompressionCurrent
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceGaugeCoframeWard
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseFirstCurrentGaugeJets
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceMixedNativeReturn SourceJointScaleBudget SourceRetardedIncrement SourceMinimalGraphParticular
open SourceInverseCompressionCurrent SourceScalarDoubleCurrent SourceGaugeCoframeWard
open SourceGaugeCoframeJets FullYSourceResolventGraphSplice
open scoped InnerProductSpace
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
private local instance realStarModule : StarModule ℝ Op where
  star_smul r A := by
    change star ((r : ℂ) • A)=(r : ℂ) • star A
    rw [star_smul,Complex.star_def,Complex.conj_ofReal]
attribute [local irreducible] GaussDiagonalHistory.diagonalAction sourceRead
  matterInsertion matterHamiltonianCurrent state sourcePair defectAction compressionCore firstRetardedCurrent
  SourceScalarDoubleCurrent.fullInsertion SourceScalarDoubleCurrent.electricMatterCurrent
  SourceScalarGaugeScale.deltaGauge SourceHamiltonianScaleJet.scaleDerivative
  SourceMixedNativeReturn.fullAction SourceMixedNativeReturn.thetaAction cutoffEuler scaleDoubleRemainder constantAction
  SourceScalarForceBudget.solverOperator SourceScalarForceBudget.oscillatorMass
  SourceScalarDoubleCurrent.oscillatorForce SourceScalarDoubleCurrent.compressedOscillatorForce
  SourceGaugeCoframeWard.wardOperator

private theorem compression_core_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem read_compression (F : Index) (seed : diagonal.domain) (A : End) (x : H) :
    sourceRead F seed A (GaussGradedCompression.compression F x)=
      embed (A (coreEquiv.symm ⟨GaussGradedCompression.compression F x,compression_mem_core F x⟩)) := by
  have hm : GaussGradedCompression.compression F x∈inputSpan F seed :=
    Submodule.mem_sup_left (compression_mem_support F x)
  have hp := (inputSpan F seed).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨GaussGradedCompression.compression F x,hm⟩
  unfold sourceRead coreRead
  change embed (A (coreEquiv.symm (Submodule.inclusion (input_span_core F seed)
    ((inputSpan F seed).orthogonalProjectionOnto (GaussGradedCompression.compression F x)))))=_
  rw [hp]
  rfl

/-- Compression enters its actual finite core first; the auxiliary reader seed has no effect. -/
theorem original_after_compression_seed (F : Index) (seed : diagonal.domain) (A : End) :
    sourceRead F seed A*GaussGradedCompression.compression F=
      sourceRead F (0 : diagonal.domain) A*GaussGradedCompression.compression F := by
  apply ContinuousLinearMap.ext
  intro x
  exact (read_compression F seed A x).trans (read_compression F 0 A x).symm

/-- The source map W C_F is bounded because C_F has its generated finite core range. -/
def afterCompression (sharp : Bool) (m ell : ℕ) (F : Index) : Op :=
  sourceRead F (0 : diagonal.domain) (matterInsertion sharp m ell)*GaussGradedCompression.compression F

/-- The real adjoint completion retains the escaped input leg of C_F W. -/
def wholeCurrent (sharp : Bool) (m ell : ℕ) (F : Index) : Op :=
  -star (afterCompression (!sharp) m ell F)-afterCompression sharp m ell F

def wholeResponse (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) : Op :=
  finiteResolvent F z*wholeCurrent sharp m ell F*finiteResolvent F z

attribute [local irreducible] afterCompression wholeCurrent wholeResponse

private theorem after_compression_core (sharp : Bool) (m ell : ℕ) (F : Index) (f : QuantumTest) :
    afterCompression sharp m ell F (embed f)=embed (matterInsertion sharp m ell (compressionCore F f)) := by
  rw [afterCompression]
  unfold compressionCore
  exact read_compression F 0 (matterInsertion sharp m ell) (embed f)

private theorem compression_pair (F : Index) (p q : QuantumTest) :
    sourcePair p (compressionCore F q)=sourcePair (compressionCore F p) q := by
  simp only [sourcePair,compression_core_embed]
  exact (GaussGradedCompression.compression_pair F (embed p) (embed q)).symm

/-- The whole-H operator agrees with the original graded commutator on both arbitrary core legs. -/
theorem original_whole_current_pair (sharp : Bool) (m ell : ℕ) (F : Index) (p q : QuantumTest) :
    inner ℂ (embed p) (wholeCurrent sharp m ell F (embed q))=
      sourcePair p (bracket (compressionCore F) (matterInsertion sharp m ell) q) := by
  rw [wholeCurrent]
  simp only [sub_apply,neg_apply,inner_sub_right,inner_neg_right,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,after_compression_core]
  have hW := original_matter_insertion_pair sharp m ell (compressionCore F p) q
  have hC := compression_pair F p (matterInsertion sharp m ell q)
  have h := hC.trans hW
  simp only [sourcePair] at h
  simp only [sourcePair,bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub,inner_sub_right]
  linear_combination -h

private theorem finite_pair (F : Index) (z : ℂ) (hz : z.im ≠ 0) (k f : H) :
    inner ℂ k (finiteResolvent F z f)=inner ℂ (finiteResolvent F (star z) k) f := by
  have hs : (star z).im ≠ 0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have hk := congrArg (fun A : Op => A k)
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) (star z) hs)
  have hf := congrArg (fun A : Op => A f)
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change GaussGradedCompression.compression F (finiteResolvent F (star z) k)-
    star z • finiteResolvent F (star z) k=k at hk
  change GaussGradedCompression.compression F (finiteResolvent F z f)-z • finiteResolvent F z f=f at hf
  have hp : inner ℂ (GaussGradedCompression.compression F (finiteResolvent F (star z) k))
      (finiteResolvent F z f)=inner ℂ (finiteResolvent F (star z) k)
        (GaussGradedCompression.compression F (finiteResolvent F z f)) :=
    (GaussGradedCompression.compression_selfAdjoint F).isSymmetric _ _
  calc
    _=inner ℂ (GaussGradedCompression.compression F (finiteResolvent F (star z) k)-
      star z • finiteResolvent F (star z) k) (finiteResolvent F z f) := congrArg (fun x => inner ℂ x _) hk.symm
    _=inner ℂ (finiteResolvent F (star z) k)
      (GaussGradedCompression.compression F (finiteResolvent F z f)-z • finiteResolvent F z f) := by
      simp only [inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right]
      exact congrArg₂ (fun a b : ℂ => a-b) hp
        (congrArg (fun c : ℂ => c*inner ℂ (finiteResolvent F (star z) k) (finiteResolvent F z f))
          (show (starRingEnd ℂ) (star z)=z from star_star z))
    _=_ := congrArg (fun x => inner ℂ _ x) hf

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g : H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem joined_core (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (g k : diagonal.domain) :
    firstRetardedCurrent sharp m ell F z hz g k=
      sourcePair (state F (star z)
        (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
        (bracket (compressionCore F) (matterInsertion sharp m ell) (state F z hz g)) := by
  rw [firstRetardedCurrent,matterHamiltonianCurrent,defectAction]
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
  have pl (p q r : QuantumTest) : sourcePair (p-q) r=sourcePair p r-sourcePair q r := by
    simp only [sourcePair,map_sub,inner_sub_left]
  have pr (p q r : QuantumTest) : sourcePair p (q-r)=sourcePair p q-sourcePair p r := by
    simp only [sourcePair,map_sub,inner_sub_right]
  simp only [pl,pr,diagonalAction_pair,compression_pair]
  ring

/-- No reader seed or moving-core approximation remains in the actual weak response. -/
theorem actual_whole_response (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im ≠ 0) (g k : diagonal.domain) :
    inner ℂ (k : H) (wholeResponse sharp m ell F z (g : H))=
      firstRetardedCurrent sharp m ell F z hz g k := by
  rw [wholeResponse]
  change inner ℂ (k : H) (finiteResolvent F z
    (wholeCurrent sharp m ell F (finiteResolvent F z (g : H))))=_
  rw [finite_pair F z hz]
  let hs : (star z).im ≠ 0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  rw [←state_embed F z hz g,←state_embed F (star z) hs k,original_whole_current_pair]
  exact (joined_core sharp m ell F z hz g k).symm

private def productJet (A B : ℕ → ℝ → Op) : ℕ → ℕ → ℕ → ℝ → Op
  | 0,i,j,t => A i t*B j t
  | n+1,i,j,t => productJet A B n (i+1) j t+productJet A B n i (j+1) t

private theorem product_derivative (A B : ℕ → ℝ → Op)
    (ha : ∀ n t,HasDerivAt (A n) (A (n+1) t) t)
    (hb : ∀ n t,HasDerivAt (B n) (B (n+1) t) t) (n i j : ℕ) (t : ℝ) :
    HasDerivAt (productJet A B n i j) (productJet A B (n+1) i j t) t := by
  induction n generalizing i j with
  | zero => exact (ha i t).mul (hb j t)
  | succ n ih => exact (ih (i+1) j).add (ih i (j+1))

def afterJet (sharp : Bool) (m ell : ℕ) (F : Index) (n : ℕ) (t : ℝ) : Op :=
  productJet (fun j s => readOrbitJet F 0 (matterInsertion sharp m ell) 0 j 0 s)
    (fun j s => compressionJet F 0 j 0 s) n 0 0 t

def wholeJet (sharp : Bool) (m ell : ℕ) (F : Index) (n : ℕ) (t : ℝ) : Op :=
  -star (afterJet (!sharp) m ell F n t)-afterJet sharp m ell F n t

def responseJet (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (n : ℕ) (t : ℝ) : Op :=
  productJet (fun j s => resolventJet F z 0 j 0 s)
    (fun j s => productJet (wholeJet sharp m ell F)
      (fun r u => resolventJet F z 0 r 0 u) j 0 0 s) n 0 0 t

private theorem after_derivative (sharp : Bool) (m ell : ℕ) (F : Index) (n : ℕ) (t : ℝ) :
    HasDerivAt (afterJet sharp m ell F n) (afterJet sharp m ell F (n+1) t) t :=
  product_derivative _ _
    (fun j s => read_orbit_gauge_derivative F 0 (matterInsertion sharp m ell) 0 j 0 s)
    (fun j s => compression_gauge_derivative F 0 j 0 s) n 0 0 t

private theorem whole_derivative (sharp : Bool) (m ell : ℕ) (F : Index) (n : ℕ) (t : ℝ) :
    HasDerivAt (wholeJet sharp m ell F n) (wholeJet sharp m ell F (n+1) t) t :=
  (after_derivative (!sharp) m ell F n t).star.neg.sub (after_derivative sharp m ell F n t)

/-- Actual norm derivatives retain both inverse legs and all first-current projection crosses. -/
theorem actual_response_gauge_derivative (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (n : ℕ) (t : ℝ) :
    HasDerivAt (responseJet sharp m ell F z n) (responseJet sharp m ell F z (n+1) t) t :=
  product_derivative _ _ (fun j s => resolvent_gauge_derivative F z 0 j 0 s)
    (fun j s => product_derivative _ _ (whole_derivative sharp m ell F)
      (fun r u => resolvent_gauge_derivative F z 0 r 0 u) j 0 0 s) n 0 0 t

private theorem after_orbit (sharp : Bool) (m ell : ℕ) (F : Index) (t : ℝ) :
    afterJet sharp m ell F 0 t=(mixedHilbert 0 t).conjStarAlgEquiv (afterCompression sharp m ell F) := by
  simp only [afterJet,productJet,actual_read_orbit,actual_mixed_compression]
  rw [←map_mul,afterCompression]

private theorem whole_orbit (sharp : Bool) (m ell : ℕ) (F : Index) (t : ℝ) :
    wholeJet sharp m ell F 0 t=(mixedHilbert 0 t).conjStarAlgEquiv (wholeCurrent sharp m ell F) := by
  simp only [wholeJet,after_orbit,wholeCurrent,map_sub,map_neg,map_star]

/-- This is the conjugation of the whole generated current, with no source-input anchor. -/
theorem actual_response_orbit (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im ≠ 0) (t : ℝ) :
    responseJet sharp m ell F z 0 t=
      (mixedHilbert 0 t).conjStarAlgEquiv (wholeResponse sharp m ell F z) := by
  simp only [responseJet,productJet,whole_orbit,actual_mixed_resolvent F z hz]
  rw [←map_mul,←map_mul,wholeResponse]
  congr 1

private theorem inverse_flow_core (t : ℝ) (f : QuantumTest) :
    (mixedHilbert 0 t).symm (embed f)=embed (SourceGaugeScaleTransport.coreFlow (-t) f) := by
  apply (mixedHilbert 0 t).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simp only [mixedHilbert,LinearIsometryEquiv.trans_apply,coframeHilbert,mul_zero,
    SourceCoframeScaleTransport.hilbertFlow_zero,SourceGaugeScaleTransport.hilbertFlow_on_core]
  rw [SourceGaugeScaleTransport.coreFlow_add,add_neg_cancel,SourceGaugeScaleTransport.coreFlow_zero]

private theorem orbit_pair (B : Op) (t : ℝ) (g k : QuantumTest) :
    inner ℂ (embed k) ((mixedHilbert 0 t).conjStarAlgEquiv B (embed g))=
      inner ℂ (embed (SourceGaugeScaleTransport.coreFlow (-t) k))
        (B (embed (SourceGaugeScaleTransport.coreFlow (-t) g))) := by
  have h := (mixedHilbert 0 t).inner_map_map ((mixedHilbert 0 t).symm (embed k))
    (B ((mixedHilbert 0 t).symm (embed g)))
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  change inner ℂ (embed k) ((mixedHilbert 0 t).conjStarAlgEquiv B (embed g))=_ at h
  simpa only [inverse_flow_core] using h

def profile (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (g k : QuantumTest) (n : ℕ) (t : ℝ) : ℂ :=
  inner ℂ (embed k) (responseJet sharp m ell F z n t (embed g))

/-- Every transformed input remains the same source test under the paid gauge flow. -/
theorem actual_profile_orbit (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im ≠ 0) (g k : QuantumTest) (t : ℝ) :
    profile sharp m ell F z g k 0 t=
      inner ℂ (embed (SourceGaugeScaleTransport.coreFlow (-t) k))
        (wholeResponse sharp m ell F z (embed (SourceGaugeScaleTransport.coreFlow (-t) g))) := by
  rw [profile,actual_response_orbit sharp m ell F z hz]
  exact orbit_pair _ t g k

set_option backward.isDefEq.respectTransparency.types false in
private theorem profile_derivative (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (g k : QuantumTest) (n : ℕ) (t : ℝ) :
    HasDerivAt (profile sharp m ell F z g k n) (profile sharp m ell F z g k (n+1) t) t := by
  have hA : HasDerivAt (fun s => responseJet sharp m ell F z n s (embed g))
      (responseJet sharp m ell F z (n+1) t (embed g)) t :=
    ((ContinuousLinearMap.apply ℂ H (embed g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (actual_response_gauge_derivative sharp m ell F z n t)
  have h := (hasDerivAt_const t (embed k)).inner ℂ hA
  simpa only [inner_zero_left,zero_add,add_zero,profile] using! h

private theorem negative_flow (f : QuantumTest) (t : ℝ) :
    HasDerivAt (fun s : ℝ => embed (SourceGaugeScaleTransport.coreFlow (-s) f))
      (-embed (SourceGaugeScaleTransport.coreFlow (-t) (G f))) t := by
  simpa only [neg_smul,one_smul] using!
    (SourceGaugeScaleTransport.strong_core_derivative f (-t)).scomp t ((hasDerivAt_id t).neg)

private theorem pullback_derivative (B : Op) (g k : QuantumTest) (t : ℝ) :
    HasDerivAt (fun s : ℝ => inner ℂ (embed (SourceGaugeScaleTransport.coreFlow (-s) k))
      (B (embed (SourceGaugeScaleTransport.coreFlow (-s) g))))
      (-inner ℂ (embed (SourceGaugeScaleTransport.coreFlow (-t) k))
        (B (embed (SourceGaugeScaleTransport.coreFlow (-t) (G g))))-
      inner ℂ (embed (SourceGaugeScaleTransport.coreFlow (-t) (G k)))
        (B (embed (SourceGaugeScaleTransport.coreFlow (-t) g)))) t := by
  have hg := (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (negative_flow g t)
  have h := (negative_flow k t).inner ℂ hg
  simp only [map_neg,inner_neg_left,inner_neg_right] at h
  exact h.congr_deriv (by abel)

/-- The first gauge jet has two fixed source-generator legs; no finite reader changes with g. -/
theorem actual_profile_first (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im ≠ 0) (g k : QuantumTest) (t : ℝ) :
    profile sharp m ell F z g k 1 t=
      -profile sharp m ell F z (G g) k 0 t-profile sharp m ell F z g (G k) 0 t := by
  have h := (pullback_derivative (wholeResponse sharp m ell F z) g k t).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => actual_profile_orbit sharp m ell F z hz g k s))
  have hu := (profile_derivative sharp m ell F z g k 0 t).unique h
  rw [actual_profile_orbit sharp m ell F z hz (G g) k t,
    actual_profile_orbit sharp m ell F z hz g (G k) t]
  exact hu

/-- The second jet retains the mixed coefficient two between the actual fixed source derivatives. -/
theorem actual_profile_second (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im ≠ 0) (g k : QuantumTest) (t : ℝ) :
    profile sharp m ell F z g k 2 t=
      profile sharp m ell F z (G (G g)) k 0 t+
      2*profile sharp m ell F z (G g) (G k) 0 t+profile sharp m ell F z g (G (G k)) 0 t := by
  have hd := (profile_derivative sharp m ell F z (G g) k 0 t).neg.sub
    (profile_derivative sharp m ell F z g (G k) 0 t)
  have h := hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => actual_profile_first sharp m ell F z hz g k s))
  have hu := (profile_derivative sharp m ell F z g k 1 t).unique h
  rw [actual_profile_first sharp m ell F z hz (G g) k t,
    actual_profile_first sharp m ell F z hz g (G k) t] at hu
  exact hu.trans (by ring)

private theorem profile_origin (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im ≠ 0) (g k : QuantumTest) :
    profile sharp m ell F z g k 0 0=
      inner ℂ (embed k) (wholeResponse sharp m ell F z (embed g)) := by
  rw [actual_profile_orbit sharp m ell F z hz]
  simp only [neg_zero,SourceGaugeScaleTransport.coreFlow_zero]

def gaugeFilter {V : Type*} [AddCommGroup V] [Module ℂ V] (J : ℕ → V) : V :=
  J 2-(3 : ℂ) • J 1+(2 : ℂ) • J 0

/-- This is the actual source polynomial from the lowered mixed force, applied to the complete response orbit. -/
def filteredProfile (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (g k : QuantumTest) : ℂ :=
  gaugeFilter (fun n => profile sharp m ell F z g k n 0)

/-- All six paid source currents appear in one exact gauge-filtered response. -/
theorem actual_filtered_profile (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im ≠ 0) (g k : QuantumTest) :
    filteredProfile sharp m ell F z g k=
      inner ℂ (embed k) (wholeResponse sharp m ell F z (embed (G (G g))))+
      2*inner ℂ (embed (G k)) (wholeResponse sharp m ell F z (embed (G g)))+
      inner ℂ (embed (G (G k))) (wholeResponse sharp m ell F z (embed g))+
      3*inner ℂ (embed k) (wholeResponse sharp m ell F z (embed (G g)))+
      3*inner ℂ (embed (G k)) (wholeResponse sharp m ell F z (embed g))+
      2*inner ℂ (embed k) (wholeResponse sharp m ell F z (embed g)) := by
  rw [filteredProfile,gaugeFilter,actual_profile_second sharp m ell F z hz,
    actual_profile_first sharp m ell F z hz]
  simp only [profile_origin sharp m ell F z hz,smul_eq_mul]
  ring

open MeasureTheory SourceResolventBandLimit
open scoped ENNReal

private def rightJet (g : QuantumTest) : Fin 6 → QuantumTest :=
  ![G (G g),(2 : ℂ) • G g,g,(3 : ℂ) • G g,(3 : ℂ) • g,(2 : ℂ) • g]
private def leftJet (k : QuantumTest) : Fin 6 → QuantumTest := ![k,G k,G (G k),k,G k,k]

private theorem filtered_sum (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im ≠ 0) (g k : QuantumTest) :
    filteredProfile sharp m ell F z g k=
      ∑ i : Fin 6,inner ℂ (embed (leftJet k i)) (wholeResponse sharp m ell F z (embed (rightJet g i))) := by
  rw [actual_filtered_profile sharp m ell F z hz]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,rightJet,leftJet,Matrix.cons_val_zero,
    Matrix.cons_val_succ,map_smul,inner_smul_right]
  ring

private theorem whole_continuous (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g k : QuantumTest) :
    Continuous (fun w : ℝ => inner ℂ (embed k) (wholeResponse sharp m ell F (line μ w) (embed g))) := by
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  unfold wholeResponse
  exact continuous_const.inner (((hr.mul continuous_const).mul hr).clm_apply continuous_const)

private theorem whole_tail (sharp : Bool) (μ : ℝ) (hμ : 0 < μ) (g k : QuantumTest) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal
        (‖inner ℂ (embed k) (wholeResponse sharp m ell F (line μ w) (embed g))‖^2)) ≤ ENNReal.ofReal ε := by
  have he (m ell : ℕ) (F : Index) (w : ℝ) :
      firstRetardedCurrent sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') (coreEquiv g) (coreEquiv k)=
      inner ℂ (embed k) (wholeResponse sharp m ell F (line μ w) (embed g)) :=
    (actual_whole_response sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') (coreEquiv g) (coreEquiv k)).symm
  simpa only [he] using! actual_first_retarded_tail sharp μ hμ (coreEquiv g) (coreEquiv k)

private theorem sum_six_square (v : Fin 6 → ℂ) : ‖∑ i,v i‖^2 ≤ 6*∑ i,‖v i‖^2 := by
  have ht := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Finset.univ v) 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin 6 => ‖v i‖) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hc
  exact ht.trans (hc.trans_eq (by ring))

/-- The gauge polynomial consumes six generated fixed source jets; the same threshold handles every actual F. -/
theorem actual_filtered_profile_tail (sharp : Bool) (μ : ℝ) (hμ : 0 < μ) (g k : QuantumTest) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖filteredProfile sharp m ell F (line μ w) g k‖^2)) ≤ ENNReal.ofReal ε := by
  classical
  intro ε hε
  choose Ns hNs using (fun i : Fin 6 => whole_tail sharp μ hμ (rightJet g i) (leftJet k i)
    (ε/36) (by positivity))
  refine ⟨Finset.univ.sup Ns,fun m hm ell hell F => ?_⟩
  let row (i : Fin 6) (w : ℝ) :=
    inner ℂ (embed (leftJet k i)) (wholeResponse sharp m ell F (line μ w) (embed (rightJet g i)))
  have hrow (i : Fin 6) : (∫⁻ w : ℝ,ENNReal.ofReal (‖row i w‖^2)) ≤ ENNReal.ofReal (ε/36) :=
    hNs i m ((Finset.le_sup (Finset.mem_univ i)).trans hm) ell hell F
  have hmrow (i : Fin 6) : Measurable (fun w : ℝ => ENNReal.ofReal (‖row i w‖^2)) :=
    ((whole_continuous sharp m ell F μ hμ (rightJet g i) (leftJet k i)).norm.pow 2).measurable.ennreal_ofReal
  have he (w : ℝ) : filteredProfile sharp m ell F (line μ w) g k=∑ i : Fin 6,row i w :=
    filtered_sum sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal 6*(∑ i : Fin 6,ENNReal.ofReal (‖row i w‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [he,←ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖row i w‖),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
      exact ENNReal.ofReal_le_ofReal (sum_six_square (fun i => row i w))
    _=ENNReal.ofReal 6*∑ i : Fin 6,(∫⁻ w : ℝ,ENNReal.ofReal (‖row i w‖^2)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum Finset.univ (fun i _ => hmrow i)]
    _ ≤ ENNReal.ofReal 6*∑ _i : Fin 6,ENNReal.ofReal (ε/36) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hrow i)) (by positivity)
    _=ENNReal.ofReal ε := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      calc
        _=ENNReal.ofReal 6*(ENNReal.ofReal 6*ENNReal.ofReal (ε/36)) := by norm_num
        _=ENNReal.ofReal ε := by
          rw [←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6),
            ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
          congr 1
          ring

attribute [local irreducible] afterJet wholeJet responseJet profile filteredProfile
  SourceGaugeCoframeWard.sandwichJet SourceGaugeCoframeWard.readOrbitJet
  SourceGaugeCoframeJets.resolventJet SourceGaugeCoframeJets.compressionJet
  SourceGaugeCoframeWard.inverseCross SourceGaugeCoframeWard.inputFlux

private theorem core_ext {x y : H} (h : ∀ p : QuantumTest,inner ℂ (embed p) x=inner ℂ (embed p) y) : x=y := by
  apply ext_inner_left ℂ
  intro a
  exact SourceCoframeScaleTransport.embed_dense.induction_on a
    (isClosed_eq (by fun_prop) (by fun_prop)) h

private theorem whole_current_core (sharp : Bool) (m ell : ℕ) (F : Index) (q : QuantumTest) :
    wholeCurrent sharp m ell F (embed q)=
      embed (bracket (compressionCore F) (matterInsertion sharp m ell) q) := by
  apply core_ext
  intro p
  simpa only [sourcePair] using! original_whole_current_pair sharp m ell F p q

private theorem source_read_current (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    sourceRead F g (bracket (compressionCore F) (matterInsertion sharp m ell))=
      wholeCurrent sharp m ell F*(inputSpan F g).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  let q := coreEquiv.symm (Submodule.inclusion (input_span_core F g)
    ((inputSpan F g).orthogonalProjectionOnto x))
  have hq : embed q=(inputSpan F g).starProjection x :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hc := whole_current_core sharp m ell F q
  rw [hq] at hc
  unfold sourceRead coreRead
  change embed (bracket (compressionCore F) (matterInsertion sharp m ell) q)=
    wholeCurrent sharp m ell F ((inputSpan F g).starProjection x)
  exact hc.symm

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

private theorem sandwich_origin (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im ≠ 0) (A : End) :
    sandwichJet F g z A 0 0 0 0=finiteResolvent F z*sourceRead F g A*finiteResolvent F z := by
  have hr := (actual_mixed_resolvent F z hz 0 0).trans (origin_conjugate _)
  have ha := (actual_read_orbit F g A 0 0).trans (origin_conjugate _)
  unfold sandwichJet
  change resolventJet F z 0 0 0 0*(readOrbitJet F g A 0 0 0 0*resolventJet F z 0 0 0 0)=_
  rw [hr,ha,mul_assoc]

/-- These are the actual first-order projection/defect response jets, before any estimate. -/
def firstProjectionCross (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) (n : ℕ) : Op :=
  sandwichJet F g z (matterHamiltonianCurrent sharp m ell) 0 n 0 0-responseJet sharp m ell F z n 0

/-- The origin retains the two linear defects and the escaped input, with no double-defect term. -/
theorem actual_first_projection_origin (sharp : Bool) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (z : ℂ) (hz : z.im ≠ 0) :
    firstProjectionCross sharp m ell F g z 0=
      finiteResolvent F z*(sourceRead F g (bracket (defectAction F) (matterInsertion sharp m ell))-
        wholeCurrent sharp m ell F*(1-(inputSpan F g).starProjection))*finiteResolvent F z := by
  have hs : matterHamiltonianCurrent sharp m ell=
      bracket (compressionCore F) (matterInsertion sharp m ell)+
        bracket (defectAction F) (matterInsertion sharp m ell) := by
    rw [matterHamiltonianCurrent,defectAction]
    unfold bracket
    noncomm_ring
  let R := finiteResolvent F z
  have hR := (actual_response_orbit sharp m ell F z hz 0).trans (origin_conjugate _)
  have hS := sandwich_origin F g z hz (matterHamiltonianCurrent sharp m ell)
  have h0 := congrArg₂ (fun a b : Op => a-b) hS hR
  have hread := congrArg (sourceRead F g) hs
  simp only [map_add] at hread
  have hread' := hread.trans (congrArg₂ (fun a b : Op => a+b)
    (source_read_current sharp m ell F g) rfl)
  have h1 := congrArg₂ (fun a b : Op => a-b)
    (congrArg (fun A : Op => R*A*R) hread')
    (show wholeResponse sharp m ell F z=R*wholeCurrent sharp m ell F*R by unfold wholeResponse; rfl)
  exact h0.trans (h1.trans (by
    dsimp only [R]
    simp only [mul_add,add_mul,mul_sub,sub_mul,mul_one,mul_assoc]
    abel))

private theorem inverse_cross_return (F : Index) (g : diagonal.domain) (z : ℂ)
    (hz : z.im ≠ 0) (A : End) (n : Fin 3) :
    inverseCross F g z A 0 n=sandwichJet F g z A 0 n 0 0-
      finiteResolvent F z*readOrbitJet F g A 0 n 0 0*finiteResolvent F z := by
  fin_cases n <;> simp only [inverseCross,resolved_inverse_return F z hz,sandwichJet] <;> rfl

private theorem read_filter (F : Index) (g : diagonal.domain) (A : End) :
    sourceRead F g (SourceScalarGaugeScale.deltaGauge (SourceScalarGaugeScale.deltaGauge A)-
      (3 : ℂ) • SourceScalarGaugeScale.deltaGauge A+(2 : ℂ) • A)=
    gaugeFilter (fun n => readOrbitJet F g A 0 n 0 0)-gaugeFilter (fun n => inputFlux F g A 0 n) := by
  simp only [gaugeFilter,inputFlux,coreJet,pow_zero,pow_succ,Module.End.one_apply,
    Module.End.mul_apply,map_add,map_sub,map_smul]
  module

/-- Every untouched projection, inverse and input jet of the lowered source current remains explicit. -/
def firstSourceCorrections (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  gaugeFilter (firstProjectionCross sharp m ell F g z)-
    gaugeFilter (fun n => inverseCross F g z (matterHamiltonianCurrent sharp m ell) 0 n)-
    finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (matterHamiltonianCurrent sharp m ell) 0 n)*
      finiteResolvent F z

private theorem sandwich_smul {R : Type*} [Ring R] [Algebra ℂ R] (r b : R) (c : ℂ) :
    r*(c • b)*r=c • (r*b*r) := by
  simp only [mul_smul_comm,smul_mul_assoc]

/-- The literal mixed-force response equals its paid gauge-current orbit plus all generated corrections. -/
theorem actual_electric_response (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im ≠ 0) :
    finiteResolvent F z*sourceRead F g
      (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell))*finiteResolvent F z=
      (1/6 : ℂ) • (gaugeFilter (fun n => responseJet sharp m ell F z n 0)+
        firstSourceCorrections sharp m ell F g z) := by
  let J := matterHamiltonianCurrent sharp m ell
  let R := finiteResolvent F z
  have hx0 : inverseCross F g z J 0 0=sandwichJet F g z J 0 0 0 0-
      finiteResolvent F z*readOrbitJet F g J 0 0 0 0*finiteResolvent F z := inverse_cross_return F g z hz J 0
  have hx1 : inverseCross F g z J 0 1=sandwichJet F g z J 0 1 0 0-
      finiteResolvent F z*readOrbitJet F g J 0 1 0 0*finiteResolvent F z := inverse_cross_return F g z hz J 1
  have hx2 : inverseCross F g z J 0 2=sandwichJet F g z J 0 2 0 0-
      finiteResolvent F z*readOrbitJet F g J 0 2 0 0*finiteResolvent F z := inverse_cross_return F g z hz J 2
  have hr := congrArg (fun A : Op => R*A*R) (read_filter F g J)
  simp only [mul_sub,sub_mul] at hr
  have hx := congrArg₂ (fun a b : Op => a+(2 : ℂ) • b)
    (congrArg₂ (fun a b : Op => a-(3 : ℂ) • b) hx2 hx1) hx0
  have hX : gaugeFilter (fun n => inverseCross F g z J 0 n)=
      gaugeFilter (fun n => sandwichJet F g z J 0 n 0 0)-
        R*gaugeFilter (fun n => readOrbitJet F g J 0 n 0 0)*R := by
    exact hx.trans (by
      dsimp only [gaugeFilter,R]
      simp only [mul_add,mul_sub,add_mul,sub_mul,mul_smul_comm,smul_mul_assoc]
      module)
  have hP : gaugeFilter (fun n => sandwichJet F g z J 0 n 0 0)=
      gaugeFilter (fun n => responseJet sharp m ell F z n 0)+
        gaugeFilter (firstProjectionCross sharp m ell F g z) := by
    simp only [gaugeFilter,firstProjectionCross,J]
    module
  have hret : R*sourceRead F g (SourceScalarGaugeScale.deltaGauge (SourceScalarGaugeScale.deltaGauge J)-
      (3 : ℂ) • SourceScalarGaugeScale.deltaGauge J+(2 : ℂ) • J)*R=
      gaugeFilter (fun n => responseJet sharp m ell F z n 0)+firstSourceCorrections sharp m ell F g z := by
    unfold firstSourceCorrections
    dsimp only [R,J] at hr hX hP ⊢
    linear_combination (norm := module) hr+hX+hP
  have hs := congrArg (fun A : End => R*sourceRead F g A*R)
    (original_electric_matter_first_current sharp m ell)
  have hsmul (c : ℂ) (A : End) : R*sourceRead F g (c • A)*R=c • (R*sourceRead F g A*R) := by
    have hm : sourceRead F g (c • A)=c • sourceRead F g A := map_smul (sourceRead F g) c A
    exact (congrArg (fun B : Op => R*B*R) hm).trans (sandwich_smul R (sourceRead F g A) c)
  exact hs.trans ((hsmul (1/6) _).trans (congrArg (fun A : Op => (1/6 : ℂ) • A) hret))

/-- These are precisely the other terms of the original balanced force, including Hardy and full projection flux. -/
def remainingForces (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) : Op :=
  sourceRead F g (-(2*(GaussNativeEnergy.sourceTime 0 : ℂ)^2) •
      (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
    (2*(GaussNativeEnergy.sourceTime 0 : ℂ)^2) •
      (constantAction sharp SourceQuantumScalarChart.vacuum*SourceMixedNativeReturn.thetaAction m ell)-
    (1/48 : ℂ) • scaleDoubleRemainder sharp m ell)-doubleProjectionFlux sharp m ell F g-
    (SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F

private theorem balanced_split (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    SourceScalarForceBudget.balancedForce sharp m ell F g=
      sourceRead F g (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell))+
        remainingForces sharp m ell F g := by
  simp only [SourceScalarForceBudget.balancedForce,compressedOscillatorForce,oscillatorForce,
    remainingForces,map_add,map_sub,map_smul]
  module

/-- The original complete Ward operator consumes the new paid first-current filter without dropping any remaining force. -/
theorem actual_complete_ward_reduction (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im ≠ 0) :
    wardOperator sharp m ell F g z=
      (1/6 : ℂ) • (gaugeFilter (fun n => responseJet sharp m ell F z n 0)+
        firstSourceCorrections sharp m ell F g z)+
      finiteResolvent F z*remainingForces sharp m ell F g*finiteResolvent F z := by
  let R := finiteResolvent F z
  have hb := congrArg (fun A : Op => R*A*R) (balanced_split sharp m ell F g)
  have hb' : R*SourceScalarForceBudget.balancedForce sharp m ell F g*R=
      R*sourceRead F g (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell))*R+
        R*remainingForces sharp m ell F g*R := hb.trans (by noncomm_ring)
  exact (actual_balanced_ward sharp m ell F g z hz).symm.trans
    (hb'.trans (congrArg₂ (fun A B : Op => A+B)
      (actual_electric_response sharp m ell F g z hz) rfl))

end LowEnergy.SourceInverseFirstCurrentGaugeJets
