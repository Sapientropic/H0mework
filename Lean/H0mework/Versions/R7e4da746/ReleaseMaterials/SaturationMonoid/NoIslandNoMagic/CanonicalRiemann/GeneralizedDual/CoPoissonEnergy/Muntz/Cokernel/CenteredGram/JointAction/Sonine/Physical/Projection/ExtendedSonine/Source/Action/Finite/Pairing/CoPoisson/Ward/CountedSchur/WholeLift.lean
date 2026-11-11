import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.Limit


set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
open Complex Filter MeasureTheory Set
open OriginalRieszSource OriginalRieszSourceGreen
open scoped Topology InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open OriginalKDirectRCofinalOutsideVolterraSource
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "Q" => Constructor.zeroMean
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "ell" => CenteredCountingDual.logarithm
local notation "C" => CenteredCountingDual.forward
local notation "D" => CenteredCountingDual.reverse
local notation "h" => hPowerBColumn
local notation "k" => hPowerBSecond
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
open private reverse_mean from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingEnergy
open private h_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.Response
open private fourier_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy

/-- The whole source is restored from its actual support and original ordinary mean, with no new material input. -/
theorem reverse_source_complete (N:ℕ) (positive:0<N) (state:M)
    (even:reflectRestricted q (state:Hq)=state) :
    DualSource.source N (E (state:Hq))=
      E ((D N state:Hq)+(2*inner ℂ ell state) • intervalConstant q) := by
  have support:=CenteredCountingDualSupport.source_support state even N positive
  rw [support]
  congr 1
  change Rq (DualSource.source N (E (state:Hq)))=
    (Q (Rq (DualSource.source N (E (state:Hq)))):Hq)+(2*inner ℂ ell state) • intervalConstant q
  rw [Constructor.zeroMean_read,reverse_mean N positive state]
  module

def reverseWholeValue (state limit:M) : BurnolL2 :=
  E ((limit:Hq)+(2*inner ℂ ell state) • intervalConstant q)

def forwardWholeValue (state:M) : BurnolL2 :=
  limUnder atTop (fun N:ℕ=>FiniteForcing.source N (E (state:Hq)))

private theorem reverse_whole_tendsto (state:M) (even:reflectRestricted q (state:Hq)=state)
    (limit:M) (actual:Tendsto (fun N:ℕ=>D N state) atTop (𝓝 limit)) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (state:Hq))) atTop (𝓝 (reverseWholeValue state limit)) := by
  have embedded: Tendsto (fun N:ℕ=>(D N state:Hq)) atTop (𝓝 (limit:Hq)):=
    continuous_subtype_val.tendsto limit |>.comp actual
  have source:=((E).continuous.tendsto _).comp
    (embedded.add_const ((2*inner ℂ ell state) • intervalConstant q))
  apply source.congr'
  filter_upwards [eventually_ge_atTop 1] with N positive
  exact (reverse_source_complete N (by omega) state even).symm

/-- Paid full difference normality consumes the actual reverse source; no projection estimate is transferred. -/
private theorem forward_whole_tendsto (state:M) (limit:BurnolL2)
    (actual:Tendsto (fun N:ℕ=>DualSource.source N (E (state:Hq))) atTop (𝓝 limit)) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (state:Hq))) atTop (𝓝 (forwardWholeValue state)) := by
  have cauchy:CauchySeq (fun N:ℕ=>FiniteForcing.source N (E (state:Hq))) := by
    have original:=actual.cauchySeq
    rw [Metric.cauchySeq_iff] at original ⊢
    intro epsilon positive
    obtain ⟨N,after⟩:=original epsilon positive
    refine ⟨N,?_⟩
    intro m hm n hn
    simpa only [dist_eq_norm,CountingDual.difference_norm] using after m hm n hn
  exact cauchy.tendsto_limUnder

private theorem second_even (coordinate:BurnolCompletedMellinCoordinate) :
    reflectRestricted q (k coordinate:Hq)=k coordinate := by
  change reflectRestricted q (-(S (h coordinate):Hq))= -(S (h coordinate):Hq)
  rw [map_neg,fourier_even _ (h_even coordinate)]

/-- The same second foot gains its complete ambient reverse response, including its nonzero mean. -/
theorem second_reverse_whole_tendsto (coordinate:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta coordinate.value=0) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (k coordinate:Hq))) atTop
      (𝓝 (reverseWholeValue (k coordinate) (secondLimit coordinate))) :=
  reverse_whole_tendsto (k coordinate) (second_even coordinate) (secondLimit coordinate)
    (actual_counted_feet_tendsto coordinate zero).2

/-- This is the independently defined forward action on that literal same second input. -/
theorem second_forward_whole_tendsto (coordinate:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta coordinate.value=0) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (k coordinate:Hq))) atTop
      (𝓝 (forwardWholeValue (k coordinate))) :=
  forward_whole_tendsto (k coordinate) _ (second_reverse_whole_tendsto coordinate zero)

def thirdQuarterValue (coordinate:BurnolCompletedMellinCoordinate) : M :=
  S (Q (Rq (forwardWholeValue (k coordinate))))+oppositeLimit (k coordinate)

private theorem third_quarter_tendsto (coordinate:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta coordinate.value=0) :
    Tendsto (fun N:ℕ=>D N (S (k coordinate))) atTop (𝓝 (thirdQuarterValue coordinate)) := by
  have first:=(((S).comp ((Q).comp Rq)).continuous.tendsto _).comp
    (second_forward_whole_tendsto coordinate zero)
  have generated:=first.add (oppositeSource_tendsto (k coordinate))
  apply generated.congr'
  filter_upwards with N
  have source:=oppositeSource_action N (k coordinate) (second_even coordinate)
  change S (C N (k coordinate))+oppositeSource N (k coordinate)=D N (S (k coordinate))
  rw [source]
  module

/-- The second application uses the same h-derived S foot and generated crossing source. -/
theorem third_reverse_whole_tendsto (coordinate:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta coordinate.value=0) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (S (k coordinate):Hq))) atTop
      (𝓝 (reverseWholeValue (S (k coordinate)) (thirdQuarterValue coordinate))) :=
  reverse_whole_tendsto (S (k coordinate)) (fourier_even _ (second_even coordinate))
    (thirdQuarterValue coordinate) (third_quarter_tendsto coordinate zero)

theorem third_forward_whole_tendsto (coordinate:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta coordinate.value=0) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (S (k coordinate):Hq))) atTop
      (𝓝 (forwardWholeValue (S (k coordinate)))) :=
  forward_whole_tendsto (S (k coordinate)) _ (third_reverse_whole_tendsto coordinate zero)

/-- The original h source equation identifies its complete missing first-foot source. -/
theorem whole_first_input (coordinate:BurnolCompletedMellinCoordinate) :
    E (h coordinate:Hq)=E (SingularCounting.centeredPower coordinate:Hq)-E (S (k coordinate):Hq) := by
  have source:=(h_power_B_source coordinate).1
  have native:=congrArg (fun state:M=>E (state:Hq)) source
  change E ((h coordinate:Hq)+(S (k coordinate):Hq))=E (SingularCounting.centeredPower coordinate:Hq) at native
  rw [map_add] at native
  linear_combination (norm:=module) native

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
