import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutLog
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.PaCoefficient
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.PositiveKernelEven
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCrossParameterRAdjointSource.PaCoefficientActionSource
open OriginalGamma.Source.KGamma OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutLog
open scoped InnerProductSpace Topology
open private sourceLogWeight_memLp from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaCoefficientActionSource
open private gamma_pair_fourier from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
open private Gamma_unique from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open private forward_reflect from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
local notation "q" => (1/4 : ℝ)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

private theorem positive_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (sourceLogKernel coordinate : ℝ → ℂ)=ᵐ[volume] (Ioc q 4).indicator (sourceLogWeight coordinate) := by
  have raw := (sourceLogWeight_memLp coordinate).coeFn_toLp
  filter_upwards [raw,volume.ae_ne q] with u read apart
  change sourceLogKernel coordinate u=(Icc q 4).indicator (sourceLogWeight coordinate) u at read
  rw [read]
  by_cases inside : u∈Icc q (4 : ℝ)
  · have strict : q<u := lt_of_le_of_ne inside.1 apart.symm
    rw [indicator_of_mem inside,indicator_of_mem (show u∈Ioc q (4 : ℝ) from ⟨strict,inside.2⟩)]
  · rw [indicator_of_notMem inside,indicator_of_notMem (fun member => inside (Ioc_subset_Icc_self member))]

private theorem weight_conjugate (coordinate : BurnolCompletedMellinCoordinate)
    (u : ℝ) (positive : 0<u) :
    sourceLogWeight coordinate u= -(4 : ℂ)*(u : ℂ)^(-(barC coordinate).value)*(Real.log (u/q) : ℂ) := by
  have argument : (u : ℂ).arg≠Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg positive.le]
    exact ne_of_lt Real.pi_pos
  have power := Complex.cpow_conj (u : ℂ) (-coordinate.value) argument
  rw [Complex.conj_ofReal] at power
  unfold sourceLogWeight
  simp only [star_mul,star_neg,star_ofNat,Complex.star_def,Complex.conj_ofReal]
  rw [←power]
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,starRingEnd_apply,star_neg]
  ring

private theorem full_raw (coordinate : BurnolCompletedMellinCoordinate) (u : ℝ) :
    (Ioc q 4).indicator (sourceLogWeight coordinate) u+
      (Ioc q 4).indicator (sourceLogWeight coordinate) (-u)=logRaw (barC coordinate) u := by
  unfold logRaw
  by_cases active : q < |u| ∧ |u|≤4
  · rw [if_pos active]
    by_cases sign : 0≤u
    · have positive : 0<u := by rw [abs_of_nonneg sign] at active; linarith [active.1]
      have member : u∈Ioc q (4 : ℝ) := by simpa only [mem_Ioc,abs_of_nonneg sign] using active
      have absent : -u∉Ioc q (4 : ℝ) := fun lower => by linarith [lower.1]
      rw [indicator_of_mem member,indicator_of_notMem absent,add_zero,
        weight_conjugate coordinate u positive,abs_of_nonneg sign]
    · have negative : u<0 := lt_of_not_ge sign
      have member : -u∈Ioc q (4 : ℝ) := by simpa only [mem_Ioc,abs_of_neg negative] using active
      have absent : u∉Ioc q (4 : ℝ) := fun lower => by linarith [lower.1]
      rw [indicator_of_notMem absent,indicator_of_mem member,zero_add,
        weight_conjugate coordinate (-u) (by linarith),abs_of_neg negative]
  · have absent : u∉Ioc q (4 : ℝ) := by
      intro inside
      have positive : 0<u := by linarith [inside.1]
      exact active (by simpa only [mem_Ioc,abs_of_pos positive] using inside)
    have negativeAbsent : -u∉Ioc q (4 : ℝ) := by
      intro inside
      have negative : u<0 := by linarith [inside.1]
      exact active (by simpa only [mem_Ioc,abs_of_neg negative] using inside)
    rw [if_neg active,indicator_of_notMem absent,indicator_of_notMem negativeAbsent,add_zero]

/-- Only the even extension is identified as a whole field; the original positive source is unchanged. -/
theorem actual_log_kernel_even_extension (coordinate : BurnolCompletedMellinCoordinate) :
    sourceLogKernel coordinate+reflectL2 (sourceLogKernel coordinate)=logValue (barC coordinate) := by
  have raw := positive_raw coordinate
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (sourceLogKernel coordinate) (reflectL2 (sourceLogKernel coordinate)),
    Lp.coeFn_compMeasurePreserving (sourceLogKernel coordinate) negMeasurePreserving,
    raw,negMeasurePreserving.quasiMeasurePreserving.ae raw,actual_log_raw (barC coordinate)]
    with u sum reflected positive negative whole
  rw [sum,Pi.add_apply]
  change reflectL2 (sourceLogKernel coordinate) u=sourceLogKernel coordinate (-u) at reflected
  rw [reflected,positive,negative,whole]
  exact full_raw coordinate u

/-- The one-half and conjugate parameter are paid at the actual even reader. -/
theorem actual_positive_log_kernel_even_read (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (even : reflectL2 value=value) :
    inner ℂ (sourceLogKernel coordinate) value=
      (1/2 : ℂ)*inner ℂ (logValue (barC coordinate)) value := by
  have reflected : inner ℂ (reflectL2 (sourceLogKernel coordinate)) value=
      inner ℂ (sourceLogKernel coordinate) value := by
    calc
      _=inner ℂ (reflectL2 (sourceLogKernel coordinate)) (reflectL2 value) := by rw [even]
      _=_ := reflectL2.inner_map_map _ _
  have full := congrArg (fun kernel : BurnolL2 => inner ℂ kernel value) (actual_log_kernel_even_extension coordinate)
  rw [inner_add_left,reflected] at full
  linear_combination (1/2 : ℂ)*full

theorem actual_original_Gamma_kernel_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (actualGammaKernel coordinate)=actualGammaKernel coordinate := by
  have source := actual_gamma_original_kernel coordinate
  have doubled := gamma_pair_fourier _ _ (gamma_pair_fourier _ _ source)
  have kernelEven : reflectL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)=
      (burnolCompletedMellinRieszVector coordinate : BurnolL2) :=
    mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector coordinate).property.2
  rw [fourierL2_fourierL2,fourierL2_fourierL2,kernelEven] at doubled
  exact Gamma_unique _ _ _ doubled source

/-- The exact same-N original Gamma counting field supplies its own even qualification. -/
theorem actual_finite_Gamma_counted_even (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    reflectL2 (fourierL2 (CountingDual.sourceCLM N (actualGammaKernel coordinate)))=
      fourierL2 (CountingDual.sourceCLM N (actualGammaKernel coordinate)) := by
  change reflectL2 (fourierL2 (FiniteForcing.source N (actualGammaKernel coordinate)))=_
  rw [←fourierL2_reflectL2_commute,forward_reflect,actual_original_Gamma_kernel_even,CountingDual.sourceCLM_apply]

theorem actual_finite_positive_log_kernel_read (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    inner ℂ (sourceLogKernel coordinate) (fourierL2 (CountingDual.sourceCLM N (actualGammaKernel coordinate)))=
      (1/2 : ℂ)*inner ℂ (logValue (barC coordinate))
        (fourierL2 (CountingDual.sourceCLM N (actualGammaKernel coordinate))) :=
  actual_positive_log_kernel_even_read coordinate _ (actual_finite_Gamma_counted_even coordinate N)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.PositiveKernelEven
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
