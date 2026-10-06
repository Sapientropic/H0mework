import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceContactCurrentBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceContactCoframeJet
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceMatterContactNative SourceMatterContactCoframe GaussMatterCore
open GaussCoframeCore GaussCoframeKinetic GaussHistoryHilbert SourcePhysicalKineticSquare SourceQuantumScalarChart
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem coefficient_smooth (k b : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (coframeGram k b) z.val :=
  ContDiffAt.sum (fun i _ => (triadInverse_smooth i k z).mul (triadInverse_smooth i b z))

private theorem column_smooth (k : Fin 3) (a : LieIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => contactMap k w (lieBasis a)) z.val := by
  simp only [contactMap,LinearMap.sum_apply,LinearMap.smul_apply]
  exact ContDiffAt.sum (fun b _ => (coefficient_smooth k b z).smul contDiffAt_const)

private theorem fiber_smooth (z : physicalChart) : ContDiffAt ℝ ∞ gramFiber z.val :=
  ContDiffAt.sum (fun k _ => ContDiffAt.sum (fun a _ => (column_smooth k a z).mul (column_smooth k a z)))

private theorem jet_smooth (i : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => fderiv ℝ gramFiber w (coframeDirection i)) z.val :=
  ((fiber_smooth z).fderiv_right (by simp)).clm_apply contDiffAt_const

/-- The actual derivative of the original finite CAR/coframe Gram, acting at order zero. -/
def gramJet (i : Fin 6) : End :=
  localMultiplier (fun w => fderiv ℝ gramFiber w (coframeDirection i)) (jet_smooth i)

/-- Original coframe momentum differentiates only the Gram coefficient in its commutator. -/
theorem original_contact_coframe_momentum (i : Fin 6) (f : QuantumTest) :
    momentum i (gramAction f)=gramAction (momentum i f)+(-Complex.I) • gramJet i f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have hG := ((fiber_smooth ⟨z,hz⟩).differentiableAt (by simp)).hasFDerivAt
    have hr := (ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ).hasFDerivAt.comp z hG
    have hd := (hr.clm_apply (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
    change fderiv ℝ (fun w => gramFiber w (f w)) z=_ at hd
    have he : (gramAction f : SourceCoordinateSlice → FockFiber)=fun w => gramFiber w (f w) :=
      funext (original_contact_gram_value f)
    change (-Complex.I) • derivative (coframeDirection i) (gramAction f) z=
      gramAction (momentum i f) z+(-Complex.I) • gramJet i f z
    rw [derivative_apply,he,hd,original_contact_gram_value]
    change (-Complex.I) • (gramFiber z (fderiv ℝ f z (coframeDirection i))+
      (fderiv ℝ gramFiber z (coframeDirection i)) (f z))=
      gramFiber z ((-Complex.I) • derivative (coframeDirection i) f z)+
        (-Complex.I) • (fderiv ℝ gramFiber z (coframeDirection i)) (f z)
    rw [derivative_apply,map_smul,smul_add]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

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

private def metric (i j : Fin 6) : End :=
  multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)

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

private theorem metric_gram_pair (i j : Fin 6) (f g : QuantumTest) :
    sourcePair f (metric i j (gramAction g))=sourcePair (metric j i (gramAction f)) g := by
  rw [metric_pair,original_contact_gram_pair]
  have h := LinearMap.congr_fun (gram_real (GaussCoframeKinetic.coefficient j i)
    (GaussCoframeKinetic.coefficient_smooth j i)).eq f
  change gramAction (metric j i f)=metric j i (gramAction f) at h
  rw [h]

private def principal (f : QuantumTest) : ℂ :=
  ∑ i : Fin 6,∑ j : Fin 6,sourcePair (momentum i f) (metric i j (gramAction (momentum j f)))

private theorem principal_real (f : QuantumTest) : (principal f).im=0 := by
  have he : star (principal f)=principal f := by
    change starRingEnd ℂ (principal f)=principal f
    simp only [principal,map_sum,GaussNativeForm.pair_conjugate]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (metric_gram_pair i j (momentum i f) (momentum j f)).symm
  have h := congrArg Complex.im he
  simp only [Complex.star_def,Complex.conj_im] at h
  linarith

/-- All original 36 coframe metric terms become a first-order momentum / zero-order Gram-jet pairing. -/
def kineticFlux (f : QuantumTest) : ℝ :=
  -(∑ i : Fin 6,∑ j : Fin 6,sourcePair (momentum i f) (metric i j (gramJet j f))).re

attribute [local irreducible] gramAction gramJet

private theorem kinetic_gram_form (f : QuantumTest) :
    sourcePair f (kinetic (gramAction f))=principal f+(-Complex.I)*
      ∑ i : Fin 6,∑ j : Fin 6,sourcePair (momentum i f) (metric i j (gramJet j f)) := by
  simp only [kinetic,LinearMap.sum_apply,sourcePair,map_sum,inner_sum]
  change (∑ i : Fin 6,∑ j : Fin 6,sourcePair f (term i j (gramAction f)))=_
  have ht (i j : Fin 6) : sourcePair f (term i j (gramAction f))=
      sourcePair (momentum i f) (metric i j (gramAction (momentum j f)))+
        (-Complex.I)*sourcePair (momentum i f) (metric i j (gramJet j f)) := by
    change sourcePair f (adjoint i (metric i j (momentum j (gramAction f))))=_
    rw [GaussCoframeKinetic.adjoint_pair,original_contact_coframe_momentum]
    simp only [map_add,map_smul,sourcePair,inner_add_right,inner_smul_right]
  simp_rw [ht]
  simp only [Finset.sum_add_distrib,Finset.mul_sum,principal,sourcePair]

/-- The original kinetic half-current contains no second derivative of the external state. -/
theorem original_contact_kinetic_flux (f : QuantumTest) :
    (sourcePair f ((kinetic*gramAction-gramAction*kinetic) f)).im/2=kineticFlux f := by
  have he : sourcePair f ((kinetic*gramAction-gramAction*kinetic) f)=
      sourcePair f (kinetic (gramAction f))-star (sourcePair f (kinetic (gramAction f))) := by
    simp only [LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right]
    change sourcePair f (kinetic (gramAction f))-sourcePair f (gramAction (kinetic f))=_
    rw [original_contact_gram_pair,←GaussNativeForm.pair_conjugate (kinetic f) (gramAction f),←kinetic_pair]
    rfl
  rw [he]
  simp only [Complex.sub_im,Complex.star_def,Complex.conj_im]
  rw [kinetic_gram_form]
  simp only [Complex.add_im,Complex.mul_im,Complex.I_re,
    zero_mul,Complex.neg_im,Complex.I_im,neg_mul,one_mul,principal_real,zero_add,kineticFlux]
  ring

open GaussCoframeForm SourceContactTimeBalance SourceContactCurrentBudget
open GaussDiagonalHistory GaussUnitaryHistory SourceMatterForceTimeBudget
open SourceBulkTwoTime SourceScalarSignedInverseReturn SourceFourPoleEnergyClosed
open SourceScalarInverseRetardedBudget FullYSourceResolventGraphSplice SourceResolventBandLimit
open Filter MeasureTheory

def coframeRemainder : End := currentAction+(∑ a : Fin 7,spinSquare a)+numberShift+
  multiply volumePotential volumePotential_smooth+matterAction

def firstOrderCurrent (F : Index) (T : End) (q : QuantumTest) : ℝ :=
  (sourcePair (SourceScalarPositiveBulkWard.raisedDefect F T q) (gramAction (T q))).im-
    kineticFlux (T q)-(sourcePair (T q) ((coframeRemainder*gramAction-gramAction*coframeRemainder) (T q))).im/2

/-- The exact current consumed by the full cost now uses first coframe derivatives in all kinetic terms. -/
theorem original_contact_first_order (F : Index) (T : End) (q : QuantumTest) :
    contactCurrent F T q=firstOrderCurrent F T q := by
  have h : reducedCurrent=(kinetic*gramAction-gramAction*kinetic)+
      (coframeRemainder*gramAction-gramAction*coframeRemainder) := by
    unfold reducedCurrent coframeRemainder coframeAction
    noncomm_ring
  rw [contactCurrent,h]
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right,Complex.add_im,firstOrderCurrent]
  have hf := original_contact_kinetic_flux (T q)
  simp only [sourcePair] at hf
  linarith

/-- The same original mu/cutoff/cofinal-F cost reads the generated first-order current directly. -/
theorem actual_original_first_order_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (hgap : 3*sourceTime 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε+
          (4*Real.pi*formPrice sharp*μ⁻¹^2*‖(k : H)‖^2/(μ-3*sourceTime 0))*
            (otherTime F μ (theta m ell) g+(9/μ)*
              ∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*firstOrderCurrent F (theta m ell) (coreTime F g t)) := by
  simpa only [contactCurrentTime,original_contact_first_order] using
    actual_original_contact_current_budget sharp μ hμ hgap g k

end LowEnergy.SourceContactCoframeJet
