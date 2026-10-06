import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceContactMixedFlux

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceContactFullFlux
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceMatterContactNative SourceMatterContactCoframe SourceContactCoframeJet SourceContactMixedFlux GaussMatterCore
open GaussCoframeCore GaussCoframeForm GaussQuantumMultiplier
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem number_value (f : QuantumTest) (z : SourceCoordinateSlice) :
    number f z=SourceQuantumFockGauge.fiberNumber (f z) := by
  apply PiLp.ext
  intro w
  exact (number_apply f z w).trans (SourceQuantumFockGauge.fiberNumber_apply (f z) w).symm

private theorem number_gram (z : SourceCoordinateSlice) : Commute SourceQuantumFockGauge.fiberNumber (gramFiber z) := by
  have hc (k : Fin 3) (a : LieIndex) : Commute SourceQuantumFockGauge.fiberNumber (contactMap k z (lieBasis a)) := by
    simp only [contactMap,LinearMap.sum_apply,LinearMap.smul_apply]
    apply Commute.sum_right
    intro b _
    exact (number_commute (matrixTerm b (lieBasis a))).smul_right _
  apply Commute.sum_right
  intro k _
  apply Commute.sum_right
  intro a _
  exact (hc k a).mul_right (hc k a)

private theorem number_action_gram : Commute number gramAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change number (gramAction f) z=gramAction (number f) z
  rw [number_value,original_contact_gram_value,original_contact_gram_value,number_value]
  exact congrArg (fun A : FiberEnd => A (f z)) (number_gram z).eq

private theorem real_gram (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (multiply c hc) gramAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (c z : ℂ) • gramAction f z=gramAction (multiply c hc f) z
  rw [original_contact_gram_value,original_contact_gram_value]
  exact ((gramFiber z).map_smul (c z : ℂ) (f z)).symm

/-- Original number and volume terms generate no contact-Gram current. -/
theorem original_number_volume_contact :
    Commute numberShift gramAction ∧ Commute (multiply volumePotential volumePotential_smooth) gramAction := by
  refine ⟨?_,real_gram _ _⟩
  have hm := real_gram numberCoefficient numberCoefficient_smooth
  change Commute ((1/2 : ℂ) • (number*multiply numberCoefficient numberCoefficient_smooth+
    multiply numberCoefficient numberCoefficient_smooth*number)) gramAction
  exact ((number_action_gram.mul_left hm).add_left (hm.mul_left number_action_gram)).smul_left _

def mixedTotal (f : QuantumTest) : ℝ :=
  mixedFlux 1 5 (currentCoefficient 0) (currentCoefficient_smooth 0) f+
  mixedFlux 3 3 (currentCoefficient 1) (currentCoefficient_smooth 1) f+
  mixedFlux 3 4 (fun z => -currentCoefficient 0 z) (fun z => (currentCoefficient_smooth 0 z).neg) f+
  mixedFlux 4 3 (currentCoefficient 2) (currentCoefficient_smooth 2) f

def spinTotal (f : QuantumTest) : ℝ := ∑ a : Fin 7,spinFlux a f
def matterFlux (f : QuantumTest) : ℝ := (sourcePair (matterAction f) (gramAction f)).im

def halfCurrent (A : End) (f : QuantumTest) : ℝ :=
  (sourcePair f ((A*gramAction-gramAction*A) f)).im/2

private theorem half_add (A B : End) (f : QuantumTest) :
    halfCurrent (A+B) f=halfCurrent A f+halfCurrent B f := by
  simp only [halfCurrent,add_mul,mul_add,LinearMap.sub_apply,LinearMap.add_apply,sourcePair,map_sub,map_add,
    inner_sub_right,inner_add_right,Complex.sub_im,Complex.add_im]
  ring
private theorem half_sum {ι : Type*} [Fintype ι] (A : ι → End) (f : QuantumTest) :
    halfCurrent (∑ i,A i) f=∑ i,halfCurrent (A i) f := by
  simp only [halfCurrent,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib,LinearMap.sum_apply,
    sourcePair,map_sum,inner_sum,Complex.im_sum,Finset.sum_div]
private theorem half_zero {A : End} (h : Commute A gramAction) (f : QuantumTest) : halfCurrent A f=0 := by
  rw [halfCurrent,h.eq,sub_self]
  simp only [LinearMap.zero_apply,sourcePair,map_zero,inner_zero_right,Complex.zero_im,zero_div]
private theorem half_matter (f : QuantumTest) : halfCurrent matterAction f=matterFlux f := by
  simp only [halfCurrent,LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right]
  change (sourcePair f (matterAction (gramAction f))-sourcePair f (gramAction (matterAction f))).im/2=_
  rw [matter_pair f (gramAction f),original_contact_gram_pair f (matterAction f),←GaussNativeForm.pair_conjugate (matterAction f) (gramAction f)]
  simp only [Complex.sub_im,Complex.conj_im,matterFlux]
  ring

/-- All four original mixed terms and all seven spin squares have explicit first-order / finite-CAR currents. -/
theorem original_full_lower_flux (f : QuantumTest) :
    halfCurrent coframeRemainder f=mixedTotal f+spinTotal f+matterFlux f := by
  simp only [coframeRemainder,half_add,half_sum,
    half_zero original_number_volume_contact.1,half_zero original_number_volume_contact.2,
    half_matter,add_zero,spinTotal]
  have hm : halfCurrent currentAction f=mixedTotal f := by
    simp only [currentAction,half_add]
    simp only [halfCurrent,original_mixed_contact_flux,mixedTotal]
  rw [hm]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact original_spin_square_contact_flux a f

open SourceContactTimeBalance SourceContactCurrentBudget SourceScalarPositiveBulkWard
open GaussDiagonalHistory GaussUnitaryHistory SourceMatterForceTimeBudget SourceBulkTwoTime
open SourceScalarSignedInverseReturn SourceFourPoleEnergyClosed SourceScalarInverseRetardedBudget
open FullYSourceResolventGraphSplice SourceResolventBandLimit Filter MeasureTheory

def fullCurrent (F : Index) (T : End) (q : QuantumTest) : ℝ :=
  (sourcePair (raisedDefect F T q) (gramAction (T q))).im-
    kineticFlux (T q)-mixedTotal (T q)-spinTotal (T q)-matterFlux (T q)

/-- The full source current keeps the original compression defect and no unnamed coframe/spin commutator. -/
theorem original_contact_full_flux (F : Index) (T : End) (q : QuantumTest) :
    contactCurrent F T q=fullCurrent F T q := by
  rw [original_contact_first_order,firstOrderCurrent]
  change _-kineticFlux (T q)-halfCurrent coframeRemainder (T q)=_
  rw [original_full_lower_flux,fullCurrent]
  ring

/-- Both original joint-cost branches consume the complete source flux on the same cutoff/cofinal-F event. -/
theorem actual_original_full_flux_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (hgap : 3*sourceTime 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε+
          (4*Real.pi*formPrice sharp*μ⁻¹^2*‖(k : H)‖^2/(μ-3*sourceTime 0))*
            (otherTime F μ (theta m ell) g+(9/μ)*
              ∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*fullCurrent F (theta m ell) (coreTime F g t)) := by
  simpa only [contactCurrentTime,original_contact_full_flux] using
    actual_original_contact_current_budget sharp μ hμ hgap g k

end LowEnergy.SourceContactFullFlux
