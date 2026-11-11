import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "F" => fourierL2
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "P0" => Constructor.zeroMean
local notation "μ" => burnolQuarterMeanCoefficient
local notation "C" => CenteredCountingDual.forward
local notation "B" => CenteredCountingDual.reverse

def exterior (value:BurnolL2):BurnolL2 := value-E (Rq value)

def reverseConstant (N:ℕ):M :=
  P0 (Rq (DualSource.source N (E (intervalConstant q))))

/-- The reverse Fourier action crosses the physical cutoff in both slots. -/
def oppositeContact (N:ℕ) (state:M):M :=
  P0 (Rq (F (exterior (FiniteForcing.source N (E (state:Hq))))-
    DualSource.source N (exterior (F (E (state:Hq))))))-
    μ (Rq (F (E (state:Hq)))) • reverseConstant N+
    μ (Rq (FiniteForcing.source N (E (state:Hq)))) • CenteredCountingDual.constantFourier

private theorem reverse_fourier (N:ℕ) (seed:BurnolL2):
    DualSource.source N (F seed)=F (FiniteForcing.source N seed):=by
  have channel (a:ℝ):ContinuousChannels.channel 1 a (F seed)=
      F (ContinuousChannels.channel (-1) a seed):=by
    simp only [ContinuousChannels.channel,one_mul,neg_one_mul,map_smul,
      fourierL2_burnolMultiplicativeDilation,neg_neg]
  have integer (n:ℕ):ContinuousChannels.channel 1 n (F seed)=
      F (Channels.sourceChannel n seed):=by
    simpa only [ContinuousChannels.channel,Channels.sourceChannel,one_mul,neg_one_mul]
      using channel n
  unfold DualSource.source FiniteForcing.source ContinuousChannels.normalization
  simp_rw [integer,channel]
  rw [map_sub,map_sum]
  congr 1
  exact fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable (-1) N seed)

private theorem dual_linear (N:ℕ) (x y:BurnolL2) (z:ℂ):
    DualSource.source N (x-z • y)=DualSource.source N x-z • DualSource.source N y:=by
  simp only [CountingDual.dual_eq_adjoint,map_sub,map_smul]

theorem actual_opposite_commutator (N:ℕ) (state:M):
    B N (S state)-S (C N state)=oppositeContact N state:=by
  have centered (value:Hq):(P0 value:Hq)=value-μ value • intervalConstant q:=
    Constructor.zeroMean_read value
  have reverseSplit:
      B N (S state)=P0 (Rq (DualSource.source N (E (Rq (F (E (state:Hq)))))))-
        μ (Rq (F (E (state:Hq)))) • reverseConstant N:=by
    change P0 (Rq (DualSource.source N (E (P0 (Rq (F (E (state:Hq)))):Hq))))=_
    rw [centered,map_sub,map_smul,dual_linear,
      map_sub,map_smul,map_sub,map_smul]
    rfl
  have forwardSplit:
      S (C N state)=P0 (Rq (F (E (Rq (FiniteForcing.source N (E (state:Hq)))))))-
        μ (Rq (FiniteForcing.source N (E (state:Hq)))) • CenteredCountingDual.constantFourier:=by
    change P0 (Rq (F (E (C N state:Hq))))=_
    rw [CenteredCountingDual.forward,centered,map_sub,map_smul,map_sub,map_smul,
      map_sub,map_smul,map_sub,map_smul]
    rfl
  have outside:
      F (exterior (FiniteForcing.source N (E (state:Hq))))-
        DualSource.source N (exterior (F (E (state:Hq))))=
      DualSource.source N (E (Rq (F (E (state:Hq)))))-
        F (E (Rq (FiniteForcing.source N (E (state:Hq))))):=by
    unfold exterior
    rw [map_sub,CountingDual.dual_eq_adjoint,map_sub,
      ← CountingDual.dual_eq_adjoint,← CountingDual.dual_eq_adjoint,reverse_fourier]
    abel
  rw [reverseSplit,forwardSplit,oppositeContact,outside,map_sub,map_sub]
  abel

/-- Both actual source actions generate the complete inverse-exchange forcing. -/
theorem actual_original_joint_forcing (N:ℕ) (positive:0<N)
    (c:BurnolCompletedMellinCoordinate):
    burnolMeanZeroOneMinusSquare (C N (burnolRieszSingleFourierSource c))=
      CountingJointEnergy.forcing N c+
        S (oppositeContact N (burnolRieszSingleFourierSource c)):=by
  have first:=(CountingJointEnergy.original_equations N positive c).1
  have target:=actual_opposite_commutator N (burnolRieszSingleFourierSource c)
  change B N (Constructor.returnState c)-S (C N (burnolRieszSingleFourierSource c))=_ at target
  change C N (burnolRieszSingleFourierSource c)-S (S (C N (burnolRieszSingleFourierSource c)))=_
  calc
    _=(C N (burnolRieszSingleFourierSource c)-S (B N (Constructor.returnState c)))+
      S (B N (Constructor.returnState c)-S (C N (burnolRieszSingleFourierSource c))):=by
        rw [map_sub]
        abel
    _=CountingJointEnergy.forcing N c+
        S (oppositeContact N (burnolRieszSingleFourierSource c)):=by rw [first,target]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.OppositeCounting.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
