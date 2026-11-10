import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedStaticNativeConstraint
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonCurrentNumerator
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedDampingPrincipal

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedN3IRNumerator
open CanonicalGradedSpatialSource ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedUniformMaterialCoefficients ActualDressedPhysicalRayNumerator
open LowEnergy.GaussComposite.ActualDressedVisiblePole
open ActualSourcePreparedEMEnclosure ActualSourcePreparedN3EMConsumer
open ActualCompositeFieldCurrent ActualEMResponseSplit PhysicalN3SourceEnergy
open scoped Matrix BigOperators
attribute [local irreducible] commonClearedPencil commonDenominator correctedGreen

/-- The original corrected pencil is contracted with both actual N3 currents
before clock or spatial coefficients are extracted. -/
def sourceN3CurrentNumerator (fieldEvent detector source : DressedEvent) (n : PhysicalMomentum)
    (dLeg sLeg : CompositeLeg) (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) : Parameters :=
  commonDenominator fieldEvent n *
    dotProduct (fun i => MvPolynomial.C (physicalN3PoleCurrent detector dLeg dPoles i))
      ((commonClearedPencil fieldEvent n).adjugate *ᵥ
        (fun j => MvPolynomial.C (physicalN3PoleCurrent source sLeg sPoles j)))

private theorem evaluate_constant_read (H : Matrix (Fin 289) (Fin 289) Parameters)
    (v : Fin 3 → ℂ) (fd fs : Fin 289 → ℂ) :
    MvPolynomial.eval v (dotProduct (fun i => MvPolynomial.C (fd i))
      (H *ᵥ (fun j => MvPolynomial.C (fs j)))) =
      dotProduct fd ((H.map (MvPolynomial.eval v)) *ᵥ fs) := by
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, MvPolynomial.eval_C, Matrix.map_apply]

theorem source_n3_current_numerator_eval (fieldEvent detector source : DressedEvent)
    (epsilon sigma : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) :
    MvPolynomial.eval (irValues epsilon sigma 0)
      (sourceN3CurrentNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles) =
      MvPolynomial.eval (irValues epsilon sigma 0) (commonDenominator fieldEvent n) *
        emCurrentObservation
          (((commonClearedPencil fieldEvent n).map (MvPolynomial.eval (irValues epsilon sigma 0))).adjugate)
          (physicalN3PoleCurrent detector dLeg dPoles) (physicalN3PoleCurrent source sLeg sPoles) := by
  unfold sourceN3CurrentNumerator
  rw [map_mul, evaluate_constant_read]
  have mapped := (MvPolynomial.eval (irValues epsilon sigma 0)).map_adjugate (commonClearedPencil fieldEvent n)
  have matrix_map (H : Matrix (Fin 289) (Fin 289) Parameters) :
      (MvPolynomial.eval (irValues epsilon sigma 0)).mapMatrix H =
        H.map (MvPolynomial.eval (irValues epsilon sigma 0)) := by
    ext i j
    rfl
  rw [matrix_map, matrix_map] at mapped
  rw [mapped]
  rfl

theorem source_prepared_n3_read_clear (fieldEvent detector source : DressedEvent)
    (epsilon sigma : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (positive : 0 < sigma)
    (regular : correctedDet fieldEvent epsilon 0 sigma n ≠ 0) :
    MvPolynomial.eval (irValues epsilon sigma 0) (commonDeterminant fieldEvent n) *
      sourcePreparedN3Read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles =
      MvPolynomial.eval (irValues epsilon sigma 0)
        (sourceN3CurrentNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles) := by
  rw [source_n3_current_numerator_eval]
  have green := actual_common_green_adjugate fieldEvent epsilon sigma 0 n positive regular
  rw [← source_prepared_full_green_original fieldEvent epsilon sigma n positive regular] at green
  have read := congrArg (fun G : Matrix (Fin 289) (Fin 289) ℂ =>
    emCurrentObservation G (physicalN3PoleCurrent detector dLeg dPoles)
      (physicalN3PoleCurrent source sLeg sPoles)) green
  simpa only [sourcePreparedN3Read, emCurrentObservation, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul] using read

theorem source_prepared_n3_read_fraction (fieldEvent detector source : DressedEvent)
    (epsilon sigma : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (positive : 0 < sigma)
    (regular : correctedDet fieldEvent epsilon 0 sigma n ≠ 0) :
    sourcePreparedN3Read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles =
      MvPolynomial.eval (irValues epsilon sigma 0)
        (sourceN3CurrentNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles) /
      MvPolynomial.eval (irValues epsilon sigma 0) (commonDeterminant fieldEvent n) := by
  apply (eq_div_iff (actual_common_determinant_nonzero fieldEvent epsilon sigma 0 n positive regular)).mpr
  exact (mul_comm _ _).trans
    (source_prepared_n3_read_clear fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles positive regular)


open ActualDressedZeroDamping ActualDressedEMTensorClock LowEnergy.ActualDressedVisiblePole Polynomial Filter Set
open scoped Topology

def sourceN3DampingFraction (fieldEvent detector source : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) : RatFunc ℂ :=
  readFraction (dampingSlice epsilon
    (sourceN3CurrentNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles))
      (dampingDeterminant fieldEvent epsilon n)

theorem source_prepared_n3_damping_fraction (fieldEvent detector source : DressedEvent)
    (epsilon sigma : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (positive : 0 < sigma)
    (chart : (dampingDeterminant fieldEvent epsilon n).eval (sigma : ℂ) ≠ 0) :
    let R := sourceN3DampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles
    sourcePreparedN3Read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles =
      R.num.eval (sigma : ℂ)/R.denom.eval (sigma : ℂ) := by
  have commonRegular : MvPolynomial.eval (irValues epsilon sigma 0) (commonDeterminant fieldEvent n) ≠ 0 := by
    rw [← damping_slice_eval]
    exact chart
  have regular := actual_common_chart_original fieldEvent epsilon sigma 0 n positive commonRegular
  have read := source_prepared_n3_read_fraction fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles positive regular
  refine read.trans ?_
  change _ = (readFraction (dampingSlice epsilon
    (sourceN3CurrentNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles))
      (dampingSlice epsilon (commonDeterminant fieldEvent n))).num.eval (sigma : ℂ) / _
  rw [← damping_slice_eval, ← damping_slice_eval]
  exact (reduced_read_at_regular _ _ (sigma : ℂ) chart).symm

private theorem positive_complex_punctured :
    Tendsto (fun sigma : ℝ => (sigma : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero] using (ne_of_gt positive)

/-- The actual two-current scalar generates its own clock pole order and
leading coefficient; no full-matrix balance or zero-order target is supplied. -/
theorem source_prepared_n3_damping_order_return (fieldEvent detector source : DressedEvent)
    (epsilon : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (nonzero : dampingDeterminant fieldEvent epsilon n ≠ 0) :
    let R := sourceN3DampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles
    Tendsto (fun sigma : ℝ => (sigma : ℂ)^poleOrder R 0 *
      sourcePreparedN3Read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles)
      (𝓝[>] 0) (𝓝 (leadingPoleCoefficient R 0)) := by
  let R := sourceN3DampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles
  have base := (pole_order_limit R 0).comp positive_complex_punctured
  simp only [Function.comp_def, sub_zero] at base
  apply Tendsto.congr' ?_ base
  have inclusion : Ioi (0 : ℝ) ⊆ ({0}ᶜ) := by
    intro sigma positive
    simpa only [mem_compl_iff, mem_singleton_iff] using (ne_of_gt positive)
  have chart := (source_static_punctured_chart _ nonzero).filter_mono (nhdsWithin_mono 0 inclusion)
  filter_upwards [chart, self_mem_nhdsWithin] with sigma regular positive
  exact congrArg (fun v : ℂ => (sigma : ℂ)^poleOrder R 0*v)
    (source_prepared_n3_damping_fraction fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles positive regular).symm

/-- Every negative clock power and the source analytic remainder are kept in
the complete actual N3 read, including mixed/residual contributions. -/
theorem source_prepared_n3_damping_principal (fieldEvent detector source : DressedEvent)
    (epsilon sigma : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (positive : 0 < sigma)
    (chart : (dampingDeterminant fieldEvent epsilon n).eval (sigma : ℂ) ≠ 0)
    (order : 0 < poleOrder (sourceN3DampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles) 0) :
    let R := sourceN3DampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles
    sourcePreparedN3Read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles =
      (∑ k ∈ Finset.range (poleOrder R 0), principalCoefficient R 0 k*(sigma : ℂ)^k/(sigma : ℂ)^poleOrder R 0) +
        (analyticNumerator R 0).eval (sigma : ℂ)/(rootRemainder R 0).eval (sigma : ℂ) := by
  let R := sourceN3DampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles
  have reduced := reduced_denominator_at_regular
    (dampingSlice epsilon (sourceN3CurrentNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles))
    (dampingDeterminant fieldEvent epsilon n) (sigma : ℂ) chart
  have remainder : (rootRemainder R 0).eval (sigma : ℂ) ≠ 0 := by
    intro zero
    have factor := congrArg (Polynomial.eval (sigma : ℂ)) (denominator_root_factor R 0)
    simp only [eval_mul, zero, mul_zero] at factor
    exact reduced factor.symm
  have away : (sigma : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  have root : 0 ∈ visibleRoots R := (visible_root_iff R 0).mpr
    ((rootMultiplicity_pos (RatFunc.denom_ne_zero R)).mp order)
  have complete := complete_principal_part R 0 (sigma : ℂ) away remainder
  rw [principal_negative_powers R 0 (sigma : ℂ) root] at complete
  exact (source_prepared_n3_damping_fraction fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles positive chart).trans
    (by simpa only [sub_zero] using complete)

end LowEnergy.GaussComposite.ActualSourcePreparedN3IRNumerator
