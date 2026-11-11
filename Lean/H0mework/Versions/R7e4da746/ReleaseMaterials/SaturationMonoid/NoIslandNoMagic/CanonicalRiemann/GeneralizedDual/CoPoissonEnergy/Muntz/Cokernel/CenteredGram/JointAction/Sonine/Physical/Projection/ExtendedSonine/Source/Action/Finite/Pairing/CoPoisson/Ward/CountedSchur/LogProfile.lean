import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.LogWeight
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.SourceJet

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.LogProfile
open Complex Filter MeasureTheory Set
open OriginalRieszSource
open scoped Topology InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open OriginalCommonInverseForcing.InverseEuler
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "F" => fourierL2
local notation "H" => burnolUnitCountingPrimitiveL2
local notation "h" => SourceJet.first
local notation "k" => SourceJet.second
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
open private first_even second_reflection from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.SourceJet
open private fourier_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
open private forward_fourier from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CenteredCountingDual
open private fourier_raw_even_of_fixed from H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.ExteriorRaw

def originalMean (a:BurnolCompletedMellinCoordinate) (j:ℕ) : ℂ :=
  burnolQuarterMeanCoefficient (SourceJet.rawColumn a j)
def powerProgramme (a:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 :=
  InfiniteWeightedProgram.program (deriv (weight (LogWeight.raw a j))) H
def returnProgramme (state:M) : BurnolL2 :=
  InfiniteWeightedProgram.program (deriv (weight (burnolMeanZeroFourierRaw state))) H

private theorem raw_measurable (a:BurnolCompletedMellinCoordinate) (j:ℕ) : Measurable (LogWeight.raw a j) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x outside
  have power:ContinuousAt (fun y:ℝ=>((|y|:ℝ):ℂ)^(star a.value-1)) x :=
    (Complex.continuousAt_ofReal_cpow_const |x| _ (Or.inr (abs_ne_zero.mpr outside))).comp continuous_abs.continuousAt
  have logarithm:ContinuousAt (fun y:ℝ=>(Real.log |y|:ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp ((Real.continuousAt_log (abs_ne_zero.mpr outside)).comp continuous_abs.continuousAt)
  exact (power.mul (logarithm.pow j)).continuousWithinAt
private theorem raw_read (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    (SourceJet.rawColumn a j:ℝ→ℂ)=ᵐ[μq] LogWeight.raw a j :=
  SourceJet.rawColumn_profile a j
private theorem raw_even (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    ∀x∈symmetricInterval q,LogWeight.raw a j |x|=LogWeight.raw a j x := by
  intro x _
  simp only [LogWeight.raw,SingularCounting.powerRaw,abs_abs]

theorem power_forward (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (SourceJet.rawColumn a j))) atTop (𝓝 (powerProgramme a j)) := by
  obtain ⟨hd,hcont,hdom,hhead⟩:=LogWeight.actual_inputs a j
  exact actual_compact_forward _ _ (raw_read a j) (raw_even a j) hd hcont
    ((raw_measurable a j).comp measurable_inv |>.div Complex.continuous_ofReal.measurable) hdom hhead

theorem power_reverse (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (SourceJet.rawColumn a j))) atTop (𝓝 (poissonPair (powerProgramme a j))) := by
  obtain ⟨hd,hcont,hdom,hhead⟩:=LogWeight.actual_inputs a j
  exact actual_compact_reverse _ _ (raw_read a j) (raw_even a j) hd hcont hdom hhead

theorem power_realizes (a:BurnolCompletedMellinCoordinate) (j:ℕ) (test:SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (E (SourceJet.rawColumn a j)) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (powerProgramme a j)) test := by
  obtain ⟨hd,hcont,hdom,hhead⟩:=LogWeight.actual_inputs a j
  exact actual_compact_realizes _ _ (raw_read a j) (raw_even a j) hd hcont hdom hhead test

private theorem return_raw_even (state:M) (even:reflectRestricted q (state:Hq)=state) :
    ∀x∈symmetricInterval q,burnolMeanZeroFourierRaw state |x|=burnolMeanZeroFourierRaw state x := by
  intro x _
  by_cases positive:0≤x
  · rw [abs_of_nonneg positive]
  · rw [abs_of_neg (lt_of_not_ge positive)]
    unfold burnolMeanZeroFourierRaw
    rw [fourier_raw_even_of_fixed _ even x]
private theorem return_inputs (state:M) (even:reflectRestricted q (state:Hq)=state) :
    (∀u:ℝ,4≤u→HasDerivAt (weight (burnolMeanZeroFourierRaw state)) (deriv (weight (burnolMeanZeroFourierRaw state)) u) u)∧
      ContinuousOn (deriv (weight (burnolMeanZeroFourierRaw state))) (Ici 4)∧
      Measurable (weight (burnolMeanZeroFourierRaw state))∧
      IntegrableOn (InfiniteWeightedProgram.weight (deriv (weight (burnolMeanZeroFourierRaw state)))) (Ioi 4)∧
      Tendsto (fun u:ℝ=>Real.sqrt u*‖weight (burnolMeanZeroFourierRaw state) u‖) atTop (𝓝 0) :=
  actual_compact_c1_inputs (S state:Hq) (burnolMeanZeroFourierRaw state)
    (Constructor.fourierDerivative (state:Hq)) (burnolMeanZeroFourier_ae_raw state)
    (return_raw_even state even) (meanZeroRaw_continuous state).measurable
    (meanZeroRaw_continuous state).continuousOn (state_derivative_continuous state).continuousOn
    (fun x _ _=>meanZeroRaw_hasDerivAt state x)

private theorem return_forward (state:M) (even:reflectRestricted q (state:Hq)=state) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (S state:Hq))) atTop (𝓝 (returnProgramme state)) := by
  obtain ⟨hd,hcont,hmeas,hdom,hhead⟩:=return_inputs state even
  exact actual_compact_forward _ _ (burnolMeanZeroFourier_ae_raw state) (return_raw_even state even) hd hcont hmeas hdom hhead
private theorem return_reverse (state:M) (even:reflectRestricted q (state:Hq)=state) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (S state:Hq))) atTop (𝓝 (poissonPair (returnProgramme state))) := by
  obtain ⟨hd,hcont,_hmeas,hdom,hhead⟩:=return_inputs state even
  exact actual_compact_reverse _ _ (burnolMeanZeroFourier_ae_raw state) (return_raw_even state even) hd hcont hdom hhead
private theorem return_realizes (state:M) (even:reflectRestricted q (state:Hq)=state) (test:SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (E (S state:Hq)) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (returnProgramme state)) test := by
  obtain ⟨hd,hcont,_hmeas,hdom,hhead⟩:=return_inputs state even
  exact actual_compact_realizes _ _ (burnolMeanZeroFourier_ae_raw state) (return_raw_even state even) hd hcont hdom hhead test

/-- The original BI block supplies this same-input decomposition, retaining its ordinary mean. -/
theorem first_source (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    E (h a j:Hq)=E (SourceJet.rawColumn a j)-originalMean a j • ConstantDual.seed+E (S (S (h a j)):Hq) := by
  have native:=(SourceJet.source_blocks a j).1
  rw [SourceJet.second,map_neg] at native
  have solved:h a j=SourceJet.column a j+S (S (h a j)) := by linear_combination (norm:=module) native
  calc
    _=E (SourceJet.column a j:Hq)+E (S (S (h a j)):Hq) := by
      simpa only [Submodule.coe_add,map_add] using congrArg (fun state:M=>E (state:Hq)) solved
    _=_ := by
      change E (Constructor.zeroMean (SourceJet.rawColumn a j):Hq)+_= _
      rw [Constructor.zeroMean_read,map_sub,map_smul]
      rfl

def firstProgramme (a:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 :=
  powerProgramme a j-originalMean a j • ConstantForward.value+returnProgramme (S (h a j))
def firstReverseProgramme (a:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 :=
  poissonPair (powerProgramme a j)-originalMean a j • ConstantDual.value+poissonPair (returnProgramme (S (h a j)))
def secondProgramme (a:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 := -returnProgramme (h a j)
def secondReverseProgramme (a:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 := -poissonPair (returnProgramme (h a j))

theorem actual_first_forward (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (h a j:Hq))) atTop (𝓝 (firstProgramme a j)) := by
  have parts:=((power_forward a j).sub (ConstantForward.original_tendsto.const_smul (originalMean a j))).add
    (return_forward (S (h a j)) (fourier_even _ (first_even a j)))
  apply parts.congr'
  filter_upwards with N
  rw [first_source a j]
  simp only [←CountingDual.sourceCLM_apply,map_add,map_sub,map_smul]

theorem actual_first_reverse (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (h a j:Hq))) atTop (𝓝 (firstReverseProgramme a j)) := by
  have parts:=((power_reverse a j).sub (ConstantDual.original_tendsto.const_smul (originalMean a j))).add
    (return_reverse (S (h a j)) (fourier_even _ (first_even a j)))
  apply parts.congr'
  filter_upwards with N
  rw [first_source a j]
  simp only [CountingDual.dual_eq_adjoint,map_add,map_sub,map_smul]

theorem actual_second_forward (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E (k a j:Hq))) atTop (𝓝 (secondProgramme a j)) := by
  have parts:=(return_forward (h a j) (first_even a j)).neg
  apply parts.congr'
  filter_upwards with N
  simp only [SourceJet.second,Submodule.coe_neg,map_neg,←CountingDual.sourceCLM_apply]

theorem actual_second_reverse (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>DualSource.source N (E (k a j:Hq))) atTop (𝓝 (secondReverseProgramme a j)) := by
  have parts:=(return_reverse (h a j) (first_even a j)).neg
  apply parts.congr'
  filter_upwards with N
  simp only [SourceJet.second,Submodule.coe_neg,map_neg,CountingDual.dual_eq_adjoint]

theorem actual_first_realizes (a:BurnolCompletedMellinCoordinate) (j:ℕ) (test:SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (E (h a j:Hq)) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (firstProgramme a j)) test := by
  rw [←burnolRemainderSourceReadCLM_apply,first_source a j]
  simp only [map_add,map_sub,map_smul]
  simp only [burnolRemainderSourceReadCLM_apply]
  rw [power_realizes a j test,ConstantForward.original_realizes test,
    return_realizes (S (h a j)) (fourier_even _ (first_even a j)) test]
  simp only [firstProgramme,map_add,map_sub,map_smul,add_apply,sub_apply,smul_apply,smul_eq_mul]
  simp only [Lp.toTemperedDistributionCLM_apply]

theorem actual_second_realizes (a:BurnolCompletedMellinCoordinate) (j:ℕ) (test:SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (E (k a j:Hq)) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (secondProgramme a j)) test := by
  rw [←burnolRemainderSourceReadCLM_apply]
  simp only [SourceJet.second,Submodule.coe_neg,map_neg]
  rw [burnolRemainderSourceReadCLM_apply,return_realizes (h a j) (first_even a j) test]
  simp only [secondProgramme,map_neg,neg_apply]

def waveProgramme (a:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 :=
  firstProgramme a j+F (secondReverseProgramme a j)
def particleProgramme (a:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 :=
  (F).symm (waveProgramme a j)

/-- The whole wave is the existing same-input finite programme, before any physical projection. -/
theorem actual_wave_tendsto (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (fun N:ℕ=>FiniteForcing.source N (SourceJet.wholeWave a j)) atTop (𝓝 (waveProgramme a j)) := by
  have parts:=(actual_first_forward a j).add (((F).continuous.tendsto _).comp (actual_second_reverse a j))
  apply parts.congr'
  filter_upwards with N
  simp only [SourceJet.wholeWave,←CountingDual.sourceCLM_apply,map_add]
  simp only [CountingDual.sourceCLM_apply,forward_fourier,Function.comp_apply]

theorem actual_particle_tendsto (a:BurnolCompletedMellinCoordinate) (j:ℕ) :
    Tendsto (SourceJet.wholeParticle a j) atTop (𝓝 (particleProgramme a j)) :=
  ((F).symm.continuous.tendsto _).comp ((actual_wave_tendsto a j).comp (tendsto_add_atTop_nat 1))

/-- The complete already-generated finite bill is consumed with its actual whole source limit. -/
theorem actual_complete_read (a:BurnolCompletedMellinCoordinate) (j:ℕ) (value:BurnolL2) :
    Tendsto (fun N:ℕ=>SourceJet.countedRead a j N value+
      inner ℂ (SourceJet.logSource a j+rankSource (S (h a j))) (burnolAmbientMeanZeroSecondCorrection value)-
      inner ℂ (oppositeSource (N+1) (h a j)) (burnolAmbientMeanZeroFirstCorrection value)+
      SourceJet.wholeInventory a j N value) atTop (𝓝 (inner ℂ (particleProgramme a j) value)) := by
  have actual:=(actual_particle_tendsto a j).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=value))
  exact actual.congr' (Eventually.of_forall (fun N=>SourceJet.complete_counted_read a j N value))

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.LogProfile
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
