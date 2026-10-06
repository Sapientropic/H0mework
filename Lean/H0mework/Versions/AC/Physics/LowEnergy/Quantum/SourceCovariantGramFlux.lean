import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCoframeQuarticCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceCovariantGramFlux
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceCoframeCovariantAction SourceCoframeCovariantCurrent SourceCoframeQuarticCurrent
open SourceMatterContactNative SourceContactTimeBalance SourceContactCurrentBudget
open GaussCoframeForm
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem gram_real (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute gramAction (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  rw [show (gramAction*(multiply c hc)) f z=gramAction (multiply c hc f) z from rfl,
    original_contact_gram_value]
  change gramFiber z ((c z : ℂ) • f z)=(c z : ℂ) • gramAction f z
  rw [map_smul,original_contact_gram_value]

private abbrev metric := metricAction

private theorem metric_pair (i j : Fin 6) (f g : QuantumTest) :
    sourcePair f (metric i j g)=sourcePair (metric j i f) g := by
  rw [show metric i j=metric j i from by
    apply LinearMap.ext
    intro q
    apply DFunLike.ext
    intro z
    change (GaussCoframeKinetic.coefficient i j z : ℂ) • q z=(GaussCoframeKinetic.coefficient j i z : ℂ) • q z
    rw [GaussCoframeKinetic.coefficient_symmetric]]
  exact multiply_pair _ _ f g

private theorem covariant_adjoint_pair (i : Fin 6) (f g : QuantumTest) :
    sourcePair f (covariantAdjoint i g)=sourcePair (covariantMomentum i f) g := by
  rw [←GaussNativeForm.pair_conjugate (covariantAdjoint i g) f,
    ←original_covariant_pair,GaussNativeForm.pair_conjugate]

private theorem covariant_kinetic_pair (f g : QuantumTest) :
    sourcePair f (covariantKinetic g)=sourcePair (covariantKinetic f) g := by
  simp only [covariantKinetic,LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum,sum_inner]
  change (∑ i : Fin 6,∑ j : Fin 6,sourcePair f (covariantAdjoint i (metric i j (covariantMomentum j g))))=
    ∑ i : Fin 6,∑ j : Fin 6,sourcePair (covariantAdjoint i (metric i j (covariantMomentum j f))) g
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [covariant_adjoint_pair,metric_pair,original_covariant_pair]

private theorem metric_gram_pair (i j : Fin 6) (f g : QuantumTest) :
    sourcePair f (metric i j (gramAction g))=sourcePair (metric j i (gramAction f)) g := by
  rw [metric_pair,original_contact_gram_pair]
  have h := LinearMap.congr_fun (gram_real (GaussCoframeKinetic.coefficient j i)
    (GaussCoframeKinetic.coefficient_smooth j i)).eq f
  change gramAction (metric j i f)=metric j i (gramAction f) at h
  rw [h]

private def principal (f : QuantumTest) : ℂ :=
  ∑ i : Fin 6,∑ j : Fin 6,sourcePair (covariantMomentum i f) (metric i j (gramAction (covariantMomentum j f)))

private theorem principal_real (f : QuantumTest) : (principal f).im=0 := by
  have he : star (principal f)=principal f := by
    change starRingEnd ℂ (principal f)=principal f
    simp only [principal,map_sum,GaussNativeForm.pair_conjugate]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (metric_gram_pair i j (covariantMomentum i f) (covariantMomentum j f)).symm
  have h := congrArg Complex.im he
  simp only [Complex.star_def,Complex.conj_im] at h
  linarith

/-- All original 36 coframe metric terms become a first-order covariant-momentum / zero-order Gram-jet pairing. -/
def covariantFlux (f : QuantumTest) : ℝ :=
  -(∑ i : Fin 6,∑ j : Fin 6,sourcePair (covariantMomentum i f) (metric i j (covariantGramJet j f))).re

attribute [local irreducible] gramAction covariantGramJet

private theorem kinetic_gram_form (f : QuantumTest) :
    sourcePair f (covariantKinetic (gramAction f))=principal f+(-Complex.I)*
      ∑ i : Fin 6,∑ j : Fin 6,sourcePair (covariantMomentum i f) (metric i j (covariantGramJet j f)) := by
  simp only [covariantKinetic,LinearMap.sum_apply,sourcePair,map_sum,inner_sum]
  change (∑ i : Fin 6,∑ j : Fin 6,sourcePair f ((covariantAdjoint i*metric i j*covariantMomentum j) (gramAction f)))=_
  have ht (i j : Fin 6) : sourcePair f ((covariantAdjoint i*metric i j*covariantMomentum j) (gramAction f))=
      sourcePair (covariantMomentum i f) (metric i j (gramAction (covariantMomentum j f)))+
        (-Complex.I)*sourcePair (covariantMomentum i f) (metric i j (covariantGramJet j f)) := by
    change sourcePair f (covariantAdjoint i (metric i j (covariantMomentum j (gramAction f))))=_
    rw [covariant_adjoint_pair,original_covariant_gram_momentum]
    simp only [map_add,map_smul,sourcePair,inner_add_right,inner_smul_right]
  simp_rw [ht]
  simp only [Finset.sum_add_distrib,Finset.mul_sum,principal,sourcePair]

/-- The original kinetic half-current contains no second derivative of the external state. -/
theorem original_covariant_kinetic_flux (f : QuantumTest) :
    (sourcePair f ((covariantKinetic*gramAction-gramAction*covariantKinetic) f)).im/2=covariantFlux f := by
  have he : sourcePair f ((covariantKinetic*gramAction-gramAction*covariantKinetic) f)=
      sourcePair f (covariantKinetic (gramAction f))-star (sourcePair f (covariantKinetic (gramAction f))) := by
    simp only [LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right]
    change sourcePair f (covariantKinetic (gramAction f))-sourcePair f (gramAction (covariantKinetic f))=_
    rw [original_contact_gram_pair,←GaussNativeForm.pair_conjugate (covariantKinetic f) (gramAction f),←covariant_kinetic_pair]
    rfl
  rw [he]
  simp only [Complex.sub_im,Complex.star_def,Complex.conj_im]
  rw [kinetic_gram_form]
  simp only [Complex.add_im,Complex.mul_im,Complex.I_re,
    zero_mul,Complex.neg_im,Complex.I_im,neg_mul,one_mul,principal_real,zero_add,covariantFlux]
  ring

open GaussDiagonalHistory GaussUnitaryHistory SourceMatterForceTimeBudget SourceBulkTwoTime SourceScalarPositiveBulkWard
open SourceScalarSignedInverseReturn SourceFourPoleEnergyClosed SourceScalarInverseRetardedBudget
open FullYSourceResolventGraphSplice SourceResolventBandLimit Filter MeasureTheory

def localFlux (f : QuantumTest) : ℝ :=
  (sourcePair f (((quarticAction+GaussMatterCore.matterAction)*gramAction-
    gramAction*(quarticAction+GaussMatterCore.matterAction)) f)).im/2

def interactingCurrent (F : Index) (T : End) (q : QuantumTest) : ℝ :=
  (sourcePair (raisedDefect F T q) (gramAction (T q))).im-covariantFlux (T q)-localFlux (T q)

/-- The exact source current uses covariant first derivatives and the genuine four-operator interaction. -/
theorem original_interacting_current (F : Index) (T : End) (q : QuantumTest) :
    contactCurrent F T q=interactingCurrent F T q := by
  have hr : reducedCurrent=(covariantKinetic*gramAction-gramAction*covariantKinetic)+
      ((quarticAction+GaussMatterCore.matterAction)*gramAction-
        gramAction*(quarticAction+GaussMatterCore.matterAction)) := by
    rw [original_reduced_quartic_current]
    noncomm_ring
  rw [contactCurrent,hr]
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right,Complex.add_im,interactingCurrent,localFlux]
  have hf := original_covariant_kinetic_flux (T q)
  simp only [sourcePair] at hf
  linarith

/-- Both original joint-cost branches consume the same source current with the full compression defect retained. -/
theorem actual_original_interacting_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (hgap : 3*sourceTime 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε+
          (4*Real.pi*formPrice sharp*μ⁻¹^2*‖(k : H)‖^2/(μ-3*sourceTime 0))*
            (otherTime F μ (theta m ell) g+(9/μ)*
              ∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*interactingCurrent F (theta m ell) (coreTime F g t)) := by
  simpa only [contactCurrentTime,original_interacting_current] using
    actual_original_contact_current_budget sharp μ hμ hgap g k

end LowEnergy.SourceCovariantGramFlux
