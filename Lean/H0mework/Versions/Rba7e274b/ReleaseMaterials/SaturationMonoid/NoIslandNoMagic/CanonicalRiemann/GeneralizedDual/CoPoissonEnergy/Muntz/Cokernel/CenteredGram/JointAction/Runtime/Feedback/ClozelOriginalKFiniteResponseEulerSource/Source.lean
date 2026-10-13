import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKResponseCofinalSourceAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteResponseEulerSource
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

namespace Prior
export OriginalKResponseCofinalSourceAction (actualU actualV actual_source_step actual_source_increment actual_source_residual)
end Prior
namespace Profile
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward.ResponseProfile (etaRaw etaSlope eta_continuous eta_derivative eta_slope_continuous eta_read)
end Profile
namespace EulerPaid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalCommonInverseForcing.InverseEuler (meanZeroRaw_continuous meanZeroRaw_hasDerivAt state_derivative_continuous meanZero_source_ward eulerState eulerState_add returnEuler endpointReaction)
end EulerPaid
local notation "μq" => volume.restrict (symmetricInterval q)

def actualURaw : Nat→ℝ→ℂ
 | 0=>fun _=>0
 | n+1=>Profile.etaRaw+burnolMeanZeroFourierRaw (Prior.actualV n)

def actualUSlope : Nat→ℝ→ℂ
 | 0=>fun _=>0
 | n+1=>Profile.etaSlope+OriginalRieszSource.Constructor.fourierDerivative
   (Prior.actualV n : BurnolQuarterIntervalL2)

def actualVRaw (n : Nat) : ℝ→ℂ:=burnolMeanZeroFourierRaw (Prior.actualU n)
def actualVSlope (n : Nat) : ℝ→ℂ:=OriginalRieszSource.Constructor.fourierDerivative
 (Prior.actualU n : BurnolQuarterIntervalL2)

/-- Actual finite source raw is generated from the same endpoint source and true Fourier material map. -/
theorem actual_U_raw_continuous (n : Nat) : Continuous (actualURaw n) :=by
 cases n with
 | zero=>exact continuous_const
 | succ n=>exact Profile.eta_continuous.add (EulerPaid.meanZeroRaw_continuous _)

theorem actual_U_slope_continuous (n : Nat) : Continuous (actualUSlope n) :=by
 cases n with
 | zero=>exact continuous_const
 | succ n=>exact Profile.eta_slope_continuous.add (EulerPaid.state_derivative_continuous _)

theorem actual_U_derivative (n : Nat) (x : ℝ) :
 HasDerivAt (actualURaw n) (actualUSlope n x) x :=by
 cases n with
 | zero=>exact hasDerivAt_const x 0
 | succ n=>exact (Profile.eta_derivative x).add (EulerPaid.meanZeroRaw_hasDerivAt _ x)

theorem actual_U_raw_source (n : Nat) :
 (Prior.actualU n : BurnolQuarterIntervalL2)=ᵐ[μq] actualURaw n :=by
 cases n with
 | zero=>
  change (0:BurnolQuarterIntervalL2)=ᵐ[μq] (fun _=>0)
  exact Lp.coeFn_zero _ _ _
 | succ n=>
  have source:=Prior.actual_source_step n
  change Prior.actualU (n+1)=OriginalRieszSource.Response.eta+
   burnolMeanZeroTruncatedFourier (Prior.actualV n) at source
  have read:=congrArg (fun state:BurnolQuarterMeanZeroCarrier=>(state:BurnolQuarterIntervalL2)) source
  rw [read]
  filter_upwards [Lp.coeFn_add (OriginalRieszSource.Response.eta:BurnolQuarterIntervalL2)
   (burnolMeanZeroTruncatedFourier (Prior.actualV n):BurnolQuarterIntervalL2),
   Profile.eta_read,burnolMeanZeroFourier_ae_raw (Prior.actualV n)] with x addition eta fourier
  change ((OriginalRieszSource.Response.eta:BurnolQuarterIntervalL2)+
   (burnolMeanZeroTruncatedFourier (Prior.actualV n):BurnolQuarterIntervalL2)) x=
   Profile.etaRaw x+burnolMeanZeroFourierRaw (Prior.actualV n) x
  rw [addition,Pi.add_apply,eta,fourier]

theorem actual_V_raw_continuous (n : Nat) : Continuous (actualVRaw n) :=
 EulerPaid.meanZeroRaw_continuous _
theorem actual_V_slope_continuous (n : Nat) : Continuous (actualVSlope n) :=
 EulerPaid.state_derivative_continuous _
theorem actual_V_derivative (n : Nat) (x : ℝ) :
 HasDerivAt (actualVRaw n) (actualVSlope n x) x :=
 EulerPaid.meanZeroRaw_hasDerivAt _ x
theorem actual_V_raw_source (n : Nat) :
 (Prior.actualV n : BurnolQuarterIntervalL2)=ᵐ[μq] actualVRaw n :=
 burnolMeanZeroFourier_ae_raw _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteResponseEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
