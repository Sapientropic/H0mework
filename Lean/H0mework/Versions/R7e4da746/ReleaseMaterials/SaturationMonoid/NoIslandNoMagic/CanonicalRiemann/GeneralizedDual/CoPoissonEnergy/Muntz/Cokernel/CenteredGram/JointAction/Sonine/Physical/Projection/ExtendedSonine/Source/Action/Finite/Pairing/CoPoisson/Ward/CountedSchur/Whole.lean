import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.PowerWhole
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CurrentRegularPrice


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
local notation "F" => fourierL2
local notation "h" => hPowerBColumn
local notation "k" => hPowerBSecond
local notation "W" => hPowerPhysicalCorrection
local notation "ell" => CenteredCountingDual.logarithm
local notation "C" => CenteredCountingDual.forward
local notation "D" => CenteredCountingDual.reverse
local notation "b" => burnolAmbientMeanZeroFirstCorrection
local notation "d" => burnolAmbientMeanZeroSecondCorrection
local notation "X" => burnolAmbientMeanZeroPosition
local notation "Y" => burnolAmbientMeanZeroFourier
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
open private forward_mean from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingEnergy
open private forward_fourier from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CenteredCountingDual
open private forward_even reverse_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
open private h_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.Response
open private second_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.WholeLift
open private extension_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
open private evenPart_of_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
open private extension_price fourier_extension_price from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CurrentRegularPrice

def firstWholeValue (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
  forwardWholeValue (SingularCounting.centeredPower c)-forwardWholeValue (S (k c))
def firstReverseWholeValue (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
  limUnder atTop (fun N:ℕ=>DualSource.source N (E (h c:Hq)))

/-- Complete first-foot convergence is generated from the literal original source equation, not supplied. -/
theorem first_forward_whole_tendsto (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (h c:Hq))) atTop (𝓝 (firstWholeValue c)) := by
  have generated:=(PowerWhole.actual_forward_power_tendsto c zero).sub (third_forward_whole_tendsto c zero)
  apply generated.congr'
  filter_upwards with N
  rw [whole_first_input]
  simp only [←CountingDual.sourceCLM_apply,map_sub]

theorem first_reverse_whole_tendsto (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (h c:Hq))) atTop (𝓝 (firstReverseWholeValue c)) := by
  have cauchy:CauchySeq (fun N:ℕ=>DualSource.source N (E (h c:Hq))) := by
    have actual:=(first_forward_whole_tendsto c zero).cauchySeq
    rw [Metric.cauchySeq_iff] at actual ⊢
    intro epsilon positive
    obtain ⟨N,after⟩:=actual epsilon positive
    refine ⟨N,?_⟩
    intro m hm n hn
    simpa only [dist_eq_norm,CountingDual.difference_norm] using after m hm n hn
  exact cauchy.tendsto_limUnder

def spatialTailValue (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
  firstWholeValue c-E (Rq (firstWholeValue c))

/-- The previously unseen spatial outside component is retained as an actual same-source limit. -/
theorem first_spatial_tail_tendsto (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    Tendsto (fun N:ℕ=>CountingEnergy.outside N (h c)) atTop (𝓝 (spatialTailValue c)) := by
  have actual:=first_forward_whole_tendsto c zero
  exact actual.sub (((E).continuous.tendsto _).comp (((Rq).continuous.tendsto _).comp actual))

theorem first_quarter_read (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    Q (Rq (firstWholeValue c))=firstLimit c := by
  have whole:=(((Q).comp Rq).continuous.tendsto _).comp (first_forward_whole_tendsto c zero)
  exact tendsto_nhds_unique whole (actual_counted_feet_tendsto c zero).1

private theorem forward_source_complete (N:ℕ) (state:M) :
    FiniteForcing.source N (E (state:Hq))=
      E (C N state:Hq)+(2*CountingEnergy.head N state) • ConstantDual.seed+CountingEnergy.outside N state := by
  have core:E (Rq (FiniteForcing.source N (E (state:Hq))))=
      E (C N state:Hq)+(2*CountingEnergy.head N state) • ConstantDual.seed := by
    change _=E (Q (Rq (FiniteForcing.source N (E (state:Hq)))):Hq)+_
    rw [Constructor.zeroMean_read,forward_mean,map_sub,map_smul]
    change _=E (Rq (FiniteForcing.source N (E (state:Hq))))-
      (2*CountingEnergy.head N state) • ConstantDual.seed+(2*CountingEnergy.head N state) • ConstantDual.seed
    module
  calc
    _=E (Rq (FiniteForcing.source N (E (state:Hq))))+CountingEnergy.outside N state := by
      unfold CountingEnergy.outside
      module
    _=_ := by rw [core]

private theorem wave_formula (c:BurnolCompletedMellinCoordinate) : W c=E (h c:Hq)+F (E (k c:Hq)) := by
  have even:reflectL2 (E (h c:Hq)+F (E (k c:Hq)))=E (h c:Hq)+F (E (k c:Hq)) := by
    rw [map_add,←fourierL2_reflectL2_commute,extension_even _ (h_even c),extension_even _ (second_even c)]
  exact evenPart_of_even _ even

/-- Both whole legs are the actual action of the original finite counting source on its original power correction. -/
theorem wave_source (N:ℕ) (c:BurnolCompletedMellinCoordinate) :
    FiniteForcing.source N (W c)=FiniteForcing.source N (E (h c:Hq))+F (DualSource.source N (E (k c:Hq))) := by
  rw [wave_formula,←CountingDual.sourceCLM_apply,map_add,CountingDual.sourceCLM_apply,
    CountingDual.sourceCLM_apply,forward_fourier]

def waveValue (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
  firstWholeValue c+F (reverseWholeValue (k c) (secondLimit c))
def particleSource (N:ℕ) (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (F).symm (FiniteForcing.source N (W c))
def particleValue (c:BurnolCompletedMellinCoordinate) : BurnolL2 := (F).symm (waveValue c)

theorem wave_tendsto (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (W c)) atTop (𝓝 (waveValue c)) := by
  have actual:=(first_forward_whole_tendsto c zero).add
    ((F).continuous.tendsto _ |>.comp (second_reverse_whole_tendsto c zero))
  exact actual.congr' (Eventually.of_forall (fun N=>(wave_source N c).symm))

theorem particle_tendsto (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    Tendsto (fun N:ℕ=>particleSource N c) atTop (𝓝 (particleValue c)) :=
  ((F).symm.continuous.tendsto _).comp (wave_tendsto c zero)

private theorem inverse_extension_price (state:M) (even:reflectRestricted q (state:Hq)=state) (value:BurnolL2) :
    inner ℂ ((F).symm (E (state:Hq))) value=inner ℂ state (Y value) := by
  have same:(F).symm (E (state:Hq))=F (E (state:Hq)) := by
    apply (F).injective
    rw [(F).apply_symm_apply,fourierL2_fourierL2,extension_even _ even]
  rw [same]
  exact fourier_extension_price state even value

/-- The full same-source two-foot read retains both ordinary means and the spatial outside. -/
theorem complete_two_foot_read (N:ℕ) (positive:0<N) (first second:M)
    (firstEven:reflectRestricted q (first:Hq)=first)
    (secondEven:reflectRestricted q (second:Hq)=second) (value:BurnolL2) :
    inner ℂ ((F).symm (FiniteForcing.source N (E (first:Hq)+F (E (second:Hq))))) value=
      (inner ℂ (C N first) (Y value)+inner ℂ (D N second) (X value))+
      star (2*CountingEnergy.head N first)*inner ℂ ((F).symm ConstantDual.seed) value+
      star (2*inner ℂ ell second)*inner ℂ ConstantDual.seed value+
      inner ℂ ((F).symm (CountingEnergy.outside N first)) value := by
  have source:(F).symm (FiniteForcing.source N (E (first:Hq)+F (E (second:Hq))))=
      (F).symm (FiniteForcing.source N (E (first:Hq)))+DualSource.source N (E (second:Hq)) := by
    rw [←CountingDual.sourceCLM_apply,map_add,CountingDual.sourceCLM_apply,
      CountingDual.sourceCLM_apply,forward_fourier,map_add,(F).symm_apply_apply]
  rw [source,forward_source_complete,reverse_source_complete N positive second secondEven]
  simp only [map_add,map_smul,inner_add_left]
  have firstPrice:=inverse_extension_price (C N first) (forward_even N first firstEven) value
  have secondPrice:=extension_price (D N second) (reverse_even N second secondEven) value
  change _+ (inner ℂ (E (D N second:Hq)) value+
    inner ℂ ((2*inner ℂ ell second) • ConstantDual.seed) value)=_
  rw [firstPrice,secondPrice]
  simp only [inner_smul_left,starRingEnd_apply]
  ring

/-- Full finite read before any limit: the two ordinary unit fields and the actual spatial outside remain. -/
theorem complete_particle_read (N:ℕ) (positive:0<N) (a:BurnolCompletedMellinCoordinate) (value:BurnolL2) :
    inner ℂ (particleSource N a) value=
      (star (FiniteForcing.coefficient (star a.value) N)*inner ℂ (SingularCounting.centeredPower a) (d value)+
       inner ℂ (logSource a+rankSource (S (h a))) (d value)-inner ℂ (oppositeSource N (h a)) (b value))+
      star (2*CountingEnergy.head N (h a))*inner ℂ ((F).symm ConstantDual.seed) value+
      star (2*inner ℂ ell (k a))*inner ℂ ConstantDual.seed value+
      inner ℂ ((F).symm (CountingEnergy.outside N (h a))) value := by
  rw [particleSource,wave_formula,complete_two_foot_read N positive _ _ (h_even a) (second_even a)]
  have priced:=actual_B2_read N a value
  rw [←resolvedFirst_actual N positive a,←resolvedSecond_actual N positive a]
  linear_combination priced

/-- The fixed original K/paired action is consumed without dropping the source coefficient or complete tail. -/
theorem complete_fixed_read (N:ℕ) (positive:0<N) (c:BurnolCompletedMellinCoordinate) :
    inner ℂ (particleSource N (barC c)) (OriginalKPairedBEulerJunctionSource.sourceAction c)=
      (star (FiniteForcing.coefficient (star (barC c).value) N)*OriginalWholeDebtRJointMobiusContactClosureSource.finitePrice c c+
       inner ℂ (logSource (barC c)+rankSource (S (h (barC c)))) (OriginalKPairedBEulerJunctionSource.sourceSecond c)-
       inner ℂ (oppositeSource N (h (barC c))) (OriginalKPairedBEulerJunctionSource.sourceFirst c))+
      star (2*CountingEnergy.head N (h (barC c)))*inner ℂ ((F).symm ConstantDual.seed) (OriginalKPairedBEulerJunctionSource.sourceAction c)+
      star (2*inner ℂ ell (k (barC c)))*inner ℂ ConstantDual.seed (OriginalKPairedBEulerJunctionSource.sourceAction c)+
      inner ℂ ((F).symm (CountingEnergy.outside N (h (barC c)))) (OriginalKPairedBEulerJunctionSource.sourceAction c) :=
  complete_particle_read N positive (barC c) (OriginalKPairedBEulerJunctionSource.sourceAction c)

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
