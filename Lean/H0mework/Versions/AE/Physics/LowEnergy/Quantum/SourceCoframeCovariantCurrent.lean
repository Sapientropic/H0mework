import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceCoframeCovariantSquare

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
noncomputable section
namespace LowEnergy.SourceCoframeCovariantCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoframeCore GaussCoframeForm SourceCoframeSpinConnection SourceCoframeCovariantAction SourceCoframeCovariantSquare
open SourceMatterContactNative SourceContactCoframeJet SourceContactTimeBalance SourceContactCurrentBudget SourceContactFullFlux
open GaussDiagonalHistory GaussUnitaryHistory SourceMatterForceTimeBudget SourceBulkTwoTime SourceScalarPositiveBulkWard
open SourceScalarSignedInverseReturn SourceFourPoleEnergyClosed SourceScalarInverseRetardedBudget
open FullYSourceResolventGraphSplice SourceResolventBandLimit Filter MeasureTheory
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def covariantGramJet (i : Fin 6) : End := gramJet i+
  Complex.I • (connectionAction i*gramAction-gramAction*connectionAction i)

/-- The actual connection and the coframe derivative of the Gram combine before any estimate. -/
theorem original_covariant_gram_momentum (i : Fin 6) (f : QuantumTest) :
    SourceCoframeCovariantAction.covariantMomentum i (gramAction f)=
      gramAction (SourceCoframeCovariantAction.covariantMomentum i f)+(-Complex.I) • covariantGramJet i f := by
  simp only [SourceCoframeCovariantAction.covariantMomentum,LinearMap.add_apply,
    original_contact_coframe_momentum,map_add,covariantGramJet,LinearMap.smul_apply,LinearMap.sub_apply,
    Module.End.mul_apply,smul_add,smul_sub,smul_smul]
  norm_num
  module

/-- The combined Gram jet is an original zero-order finite CAR multiplier. -/
theorem original_covariant_gram_value (i : Fin 6) (f : QuantumTest) (z : SourceCoordinateSlice) :
    covariantGramJet i f z=(fderiv ℝ gramFiber z (coframeDirection i)) (f z)+Complex.I •
      ((connectionFiber i z*gramFiber z-gramFiber z*connectionFiber i z) (f z)) := by
  change gramJet i f z+Complex.I • (connectionAction i (gramAction f) z-gramAction (connectionAction i f) z)=_
  rw [original_contact_gram_value]
  change (fderiv ℝ gramFiber z (coframeDirection i)) (f z)+Complex.I •
    (connectionFiber i z (gramAction f z)-gramFiber z (connectionFiber i z (f z)))=_
  rw [original_contact_gram_value]
  rfl

def covariantCurrent (F : Index) (T : End) (q : QuantumTest) : ℝ :=
  (sourcePair (raisedDefect F T q) (gramAction (T q))).im-
    (sourcePair (T q) (((covariantKinetic+spinRemainder+GaussMatterCore.matterAction)*gramAction-
      gramAction*(covariantKinetic+spinRemainder+GaussMatterCore.matterAction)) (T q))).im/2

/-- The original time current consumes the complete covariant differential action and its explicit signed local remainder. -/
theorem original_covariant_current (F : Index) (T : End) (q : QuantumTest) :
    contactCurrent F T q=covariantCurrent F T q := by
  have h : reducedCurrent=(covariantKinetic+spinRemainder+GaussMatterCore.matterAction)*gramAction-
      gramAction*(covariantKinetic+spinRemainder+GaussMatterCore.matterAction) := by
    rw [reducedCurrent,original_coframe_covariant]
    simp only [add_mul,mul_add]
    rw [original_number_volume_contact.1.eq,original_number_volume_contact.2.eq]
    abel
  simp only [contactCurrent,covariantCurrent,h]

/-- Same mu, both branches, and the full shared cutoff/cofinal-F event consume this source-generated current. -/
theorem actual_original_covariant_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (hgap : 3*sourceTime 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε+
          (4*Real.pi*formPrice sharp*μ⁻¹^2*‖(k : H)‖^2/(μ-3*sourceTime 0))*
            (otherTime F μ (theta m ell) g+(9/μ)*
              ∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*covariantCurrent F (theta m ell) (coreTime F g t)) := by
  simpa only [contactCurrentTime,original_covariant_current] using
    actual_original_contact_current_budget sharp μ hμ hgap g k

end LowEnergy.SourceCoframeCovariantCurrent
