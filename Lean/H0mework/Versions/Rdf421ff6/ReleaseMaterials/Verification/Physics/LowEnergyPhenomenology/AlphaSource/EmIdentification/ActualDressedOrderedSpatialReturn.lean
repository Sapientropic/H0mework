import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedClockCoefficientReturn
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedOrderedStatic
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open ActualDressedEMTensorClock ActualDressedZeroDamping ActualCompositeFieldCurrent Filter Set
open scoped Matrix Topology
attribute [local irreducible] commonEMTensorNumerator commonDeterminant correctedEMTensor

private theorem real_punctured_complex :
    Tendsto (fun eps : ℝ => (eps : ℂ)) (nhdsWithin 0 ({0}ᶜ)) (nhdsWithin 0 ({0}ᶜ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with eps different
  simpa only [mem_compl_iff,mem_singleton_iff,Complex.ofReal_eq_zero] using different

private theorem fourth_spatial_limit (R : RatFunc ℂ) (bounded : poleOrder R 0≤4) :
    Tendsto (fun eps : ℝ => -(eps : ℂ)^4*(R.num.eval (eps : ℂ)/R.denom.eval (eps : ℂ)))
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (-staticEntryCoefficient R)) := by
  suffices result : Tendsto (fun eps : ℝ => (eps : ℂ)^4*(R.num.eval (eps : ℂ)/R.denom.eval (eps : ℂ)))
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (staticEntryCoefficient R)) by
    simpa only [neg_mul] using result.neg
  have base := (pole_order_limit R 0).comp real_punctured_complex
  simp only [Function.comp_def,sub_zero] at base
  by_cases exactOrder : poleOrder R 0=4
  · simpa only [staticEntryCoefficient,exactOrder,if_true] using base
  · have lower : poleOrder R 0<4 := lt_of_le_of_ne bounded exactOrder
    have positive : 0<4-poleOrder R 0 := Nat.sub_pos_of_lt lower
    have extra := (Complex.continuous_ofReal.continuousAt.tendsto.pow (4-poleOrder R 0)).mono_left
      (show nhdsWithin (0 : ℝ) ({0}ᶜ)≤𝓝 0 from inf_le_left)
    have zeroLimit : Tendsto (fun eps : ℝ => (eps : ℂ)^(4-poleOrder R 0))
        (nhdsWithin 0 ({0}ᶜ)) (𝓝 0) := by
      simpa only [Complex.ofReal_zero,zero_pow positive.ne'] using extra
    have combined := zeroLimit.mul base
    simp only [zero_mul] at combined
    rw [staticEntryCoefficient,if_neg exactOrder]
    convert combined using 1
    funext eps
    rw [← mul_assoc,← pow_add,Nat.sub_add_cancel bounded]

def ClockFinite (event : DressedEvent) (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : Prop :=
  (∀mu nu, X^sourceClockOrder event n∣irClockEMNumerator event n mu nu) ∧
    X^sourceClockOrder event n∣irClockProbeNumerator event n pd ps dL dR sL sR

def sourceOrderedEMCoefficient (event : DressedEvent) (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun mu nu => -staticEntryCoefficient (zeroClockEMFraction event n mu nu)

def sourceOrderedProbeCoefficient (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  -staticEntryCoefficient (zeroClockProbeFraction event n pd ps dL dR sL sR)

/-- The spatial normalization is exactly the original kappa-square factor at kappa=epsilon squared. -/
theorem ordered_spatial_weight (eps : ℝ) : -(eps : ℂ)^4=-((eps^2 : ℝ) : ℂ)^2 := by
  push_cast
  ring

theorem actual_ordered_em_return (event : DressedEvent) (n : PhysicalMomentum)
    (nonzero : irClockDeterminant event n≠0)
    (factors : ∀mu nu, X^sourceClockOrder event n∣irClockEMNumerator event n mu nu)
    (bounded : ∀mu nu, poleOrder (zeroClockEMFraction event n mu nu) 0≤4) :
    (∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
      Tendsto (fun sigma : ℝ => correctedEMTensor event eps 0 sigma n)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockEMRead event eps n))) ∧
    Tendsto (fun eps : ℝ => -(eps : ℂ)^4 • zeroClockEMRead event eps n)
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (sourceOrderedEMCoefficient event n)) := by
  constructor
  · filter_upwards [source_ordered_original_chart event n nonzero] with eps chart
    apply tendsto_pi_nhds.2
    intro mu
    apply tendsto_pi_nhds.2
    intro nu
    exact actual_zero_clock_em_entry event eps n chart.1 mu nu (factors mu nu)
  · apply tendsto_pi_nhds.2
    intro mu
    apply tendsto_pi_nhds.2
    intro nu
    exact fourth_spatial_limit _ (bounded mu nu)

/-- Zero damping is paid first, with the complete four-piece prepared probe; the spatial coefficient is read only afterwards. -/
theorem actual_ordered_probe_return (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (nonzero : irClockDeterminant event n≠0)
    (factor : X^sourceClockOrder event n∣irClockProbeNumerator event n pd ps dL dR sL sR)
    (bounded : poleOrder (zeroClockProbeFraction event n pd ps dL dR sL sR) 0≤4) :
    (∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
      Tendsto (fun sigma : ℝ => correctedProbeRead event eps 0 sigma n pd ps dL dR sL sR)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockProbeRead event eps n pd ps dL dR sL sR))) ∧
    Tendsto (fun eps : ℝ => -(eps : ℂ)^4*zeroClockProbeRead event eps n pd ps dL dR sL sR)
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (sourceOrderedProbeCoefficient event n pd ps dL dR sL sR)) := by
  constructor
  · filter_upwards [source_ordered_original_chart event n nonzero] with eps chart
    exact actual_zero_clock_probe event eps n pd ps dL dR sL sR chart.1 factor
  · exact fourth_spatial_limit _ bounded

private theorem specialized_clock_pole (N D : (ℂ[X])[X]) (m j : ℕ) (less : j < m)
    (dFactor : X^m∣D) (eps : ℝ) (dRegular : (D.coeff m).eval (eps : ℂ)≠0)
    (nRegular : (N.coeff j).eval (eps : ℂ)≠0) :
    0<poleOrder (readFraction (clockSpecialize eps N) (clockSpecialize eps D)) 0 := by
  let Ne := clockSpecialize eps N
  let De := clockSpecialize eps D
  let R := readFraction Ne De
  have nCoefficient : Ne.coeff j≠0 := by simpa only [Ne,clockSpecialize,coe_mapRingHom,coeff_map,coe_evalRingHom] using nRegular
  have dCoefficient : De.coeff m≠0 := by simpa only [De,clockSpecialize,coe_mapRingHom,coeff_map,coe_evalRingHom] using dRegular
  have nNonzero : Ne≠0 := fun zero => nCoefficient (by rw [zero,coeff_zero])
  have dNonzero : De≠0 := fun zero => dCoefficient (by rw [zero,coeff_zero])
  have mappedFactor : X^m∣De := by
    have mapped := (_root_.map_dvd (clockSpecialize eps)) dFactor
    simpa only [De,map_pow,clockSpecialize,coe_mapRingHom,Polynomial.map_X] using mapped
  have dOrder : m≤De.rootMultiplicity 0 := by
    apply (le_rootMultiplicity_iff dNonzero).mpr
    simpa only [map_zero,sub_zero] using mappedFactor
  have nOrder : Ne.rootMultiplicity 0≤j := by
    rw [rootMultiplicity_eq_natTrailingDegree']
    exact natTrailingDegree_le_of_ne_zero nCoefficient
  by_contra positive
  have zeroOrder : R.denom.rootMultiplicity 0=0 := Nat.eq_zero_of_not_pos positive
  have cross := reduced_cross_identity Ne De dNonzero
  have rightNonzero : Ne*R.denom≠0 := mul_ne_zero nNonzero (RatFunc.denom_ne_zero R)
  have leftNonzero : R.num*De≠0 := by rw [cross]; exact rightNonzero
  have lower := le_rootMultiplicity_mul 0 leftNonzero
  have same : (R.num*De).rootMultiplicity 0=Ne.rootMultiplicity 0 := by
    rw [cross,rootMultiplicity_mul rightNonzero,zeroOrder,add_zero]
  rw [same] at lower
  omega

private theorem source_clock_pole (N D : (ℂ[X])[X]) (m : ℕ) (dFactor : X^m∣D)
    (dNonzero : D.coeff m≠0) (failure : ¬X^m∣N) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
      0<poleOrder (readFraction (clockSpecialize eps N) (clockSpecialize eps D)) 0 := by
  have coefficient : ¬∀ j < m, N.coeff j=0 := fun zero => failure (X_pow_dvd_iff.mpr zero)
  push Not at coefficient
  obtain ⟨j,less,nonzero⟩ := coefficient
  filter_upwards [source_static_punctured_chart _ dNonzero,source_static_punctured_chart _ nonzero] with eps dRegular nRegular
  exact specialized_clock_pole N D m j less dFactor eps dRegular nRegular

/-- A failed source clock divisibility check generates a genuine damping pole on its own spatial punctured chart. -/
theorem source_clock_principal_return (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (nonzero : irClockDeterminant event n≠0)
    (failure : ¬ClockFinite event n pd ps dL dR sL sR) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
      (∃mu nu,0<poleOrder (dampingEMFraction event eps n mu nu) 0) ∨
        0<poleOrder (dampingProbeFraction event eps n pd ps dL dR sL sR) 0 := by
  classical
  by_cases emFactors : ∀mu nu,X^sourceClockOrder event n∣irClockEMNumerator event n mu nu
  · have probeFailure : ¬X^sourceClockOrder event n∣irClockProbeNumerator event n pd ps dL dR sL sR :=
      fun factor => failure ⟨emFactors,factor⟩
    have paid := source_clock_pole _ _ (sourceClockOrder event n) (source_clock_factor event n)
      (source_clock_denominator_nonzero event n nonzero) probeFailure
    filter_upwards [paid] with eps pole
    rw [actual_ir_clock_probe_numerator,actual_ir_clock_determinant] at pole
    exact Or.inr pole
  · push Not at emFactors
    obtain ⟨mu,nu,factorFailure⟩ := emFactors
    have paid := source_clock_pole _ _ (sourceClockOrder event n) (source_clock_factor event n)
      (source_clock_denominator_nonzero event n nonzero) factorFailure
    filter_upwards [paid] with eps pole
    rw [actual_ir_clock_em_numerator,actual_ir_clock_determinant] at pole
    exact Or.inl ⟨mu,nu,pole⟩

private theorem kappa_to_ir : Tendsto Real.sqrt (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 ({0}ᶜ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · simpa only [Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Ioi 0)≤𝓝 0 from inf_le_left)
  · filter_upwards [self_mem_nhdsWithin] with kappa positive
    simpa only [mem_compl_iff,mem_singleton_iff] using (Real.sqrt_pos.mpr positive).ne'

/-- Canonical kappa=epsilon squared consumes the paid ordered limits; damping is still taken first at each fixed kappa. -/
theorem actual_ordered_coulomb_return (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (nonzero : irClockDeterminant event n≠0)
    (clock : ClockFinite event n pd ps dL dR sL sR)
    (emBounded : ∀mu nu,poleOrder (zeroClockEMFraction event n mu nu) 0≤4)
    (probeBounded : poleOrder (zeroClockProbeFraction event n pd ps dL dR sL sR) 0≤4) :
    (∀ᶠ kappa : ℝ in nhdsWithin 0 (Ioi 0),
      Tendsto (fun sigma : ℝ => correctedEMTensor event (Real.sqrt kappa) 0 sigma n)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockEMRead event (Real.sqrt kappa) n)) ∧
      Tendsto (fun sigma : ℝ => correctedProbeRead event (Real.sqrt kappa) 0 sigma n pd ps dL dR sL sR)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockProbeRead event (Real.sqrt kappa) n pd ps dL dR sL sR))) ∧
    Tendsto (fun kappa : ℝ => -(kappa : ℂ)^2 • zeroClockEMRead event (Real.sqrt kappa) n)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (sourceOrderedEMCoefficient event n)) ∧
    Tendsto (fun kappa : ℝ => -(kappa : ℂ)^2*zeroClockProbeRead event (Real.sqrt kappa) n pd ps dL dR sL sR)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (sourceOrderedProbeCoefficient event n pd ps dL dR sL sR)) := by
  have em := actual_ordered_em_return event n nonzero clock.1 emBounded
  have probe := actual_ordered_probe_return event n pd ps dL dR sL sR nonzero clock.2 probeBounded
  refine ⟨?_,?_,?_⟩
  · filter_upwards [kappa_to_ir.eventually em.1,kappa_to_ir.eventually probe.1] with kappa emReturn probeReturn
    exact ⟨emReturn,probeReturn⟩
  · apply Tendsto.congr' _ (em.2.comp kappa_to_ir)
    filter_upwards [self_mem_nhdsWithin] with kappa positive
    have weight := ordered_spatial_weight (Real.sqrt kappa)
    rw [Real.sq_sqrt positive.le] at weight
    exact congrArg (fun z : ℂ => z • zeroClockEMRead event (Real.sqrt kappa) n) weight
  · apply Tendsto.congr' _ (probe.2.comp kappa_to_ir)
    filter_upwards [self_mem_nhdsWithin] with kappa positive
    have weight := ordered_spatial_weight (Real.sqrt kappa)
    rw [Real.sq_sqrt positive.le] at weight
    exact congrArg (fun z : ℂ => z*zeroClockProbeRead event (Real.sqrt kappa) n pd ps dL dR sL sR) weight

/-- Orders and all coefficients of the post-zero-damping spatial principal data stay entrywise and include the complete scalar probe. -/
def sourceOrderedPrincipalData (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : Option (Matrix (Fin 4) (Fin 4) (ℕ × List ℂ) × (ℕ × List ℂ)) := by
  classical
  exact if irClockDeterminant event n=0 ∨ ¬ClockFinite event n pd ps dL dR sL sR then none else some
    ((fun mu nu => let R := zeroClockEMFraction event n mu nu
      (poleOrder R 0,List.ofFn (fun k : Fin (poleOrder R 0) => principalCoefficient R 0 k.val))),
      let R := zeroClockProbeFraction event n pd ps dL dR sL sR
      (poleOrder R 0,List.ofFn (fun k : Fin (poleOrder R 0) => principalCoefficient R 0 k.val)))

inductive OrderedStaticReturn (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : Type
  | singular (determinant_zero : irClockDeterminant event n=0)
  | clockPrincipal (determinant_nonzero : irClockDeterminant event n≠0)
      (source_clock_responsibility : ¬ClockFinite event n pd ps dL dR sL sR)
      (actual_clock_pole : ∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
        (∃mu nu,0<poleOrder (dampingEMFraction event eps n mu nu) 0) ∨
          0<poleOrder (dampingProbeFraction event eps n pd ps dL dR sL sR) 0)
  | higherSpatial (determinant_nonzero : irClockDeterminant event n≠0)
      (clock_finite : ClockFinite event n pd ps dL dR sL sR)
      (higher : (∃mu nu,4<poleOrder (zeroClockEMFraction event n mu nu) 0) ∨
        4<poleOrder (zeroClockProbeFraction event n pd ps dL dR sL sR) 0)
  | finite (determinant_nonzero : irClockDeterminant event n≠0)
      (clock_finite : ClockFinite event n pd ps dL dR sL sR)
      (tensor_orders : ∀mu nu,poleOrder (zeroClockEMFraction event n mu nu) 0≤4)
      (probe_order : poleOrder (zeroClockProbeFraction event n pd ps dL dR sL sR) 0≤4)
      (tensor_return : (∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
        Tendsto (fun sigma : ℝ => correctedEMTensor event eps 0 sigma n)
          (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockEMRead event eps n))) ∧
        Tendsto (fun eps : ℝ => -(eps : ℂ)^4 • zeroClockEMRead event eps n)
          (nhdsWithin 0 ({0}ᶜ)) (𝓝 (sourceOrderedEMCoefficient event n)))
      (probe_return : (∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
        Tendsto (fun sigma : ℝ => correctedProbeRead event eps 0 sigma n pd ps dL dR sL sR)
          (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockProbeRead event eps n pd ps dL dR sL sR))) ∧
        Tendsto (fun eps : ℝ => -(eps : ℂ)^4*zeroClockProbeRead event eps n pd ps dL dR sL sR)
          (nhdsWithin 0 ({0}ᶜ)) (𝓝 (sourceOrderedProbeCoefficient event n pd ps dL dR sL sR)))

def sourceOrderedStaticReturn (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : OrderedStaticReturn event n pd ps dL dR sL sR := by
  classical
  by_cases zero : irClockDeterminant event n=0
  · exact .singular zero
  · by_cases clock : ClockFinite event n pd ps dL dR sL sR
    · by_cases emBounded : ∀mu nu,poleOrder (zeroClockEMFraction event n mu nu) 0≤4
      · by_cases probeBounded : poleOrder (zeroClockProbeFraction event n pd ps dL dR sL sR) 0≤4
        · exact .finite zero clock emBounded probeBounded (actual_ordered_em_return event n zero clock.1 emBounded)
            (actual_ordered_probe_return event n pd ps dL dR sL sR zero clock.2 probeBounded)
        · exact .higherSpatial zero clock (Or.inr (Nat.lt_of_not_ge probeBounded))
      · push Not at emBounded
        exact .higherSpatial zero clock (Or.inl emBounded)
    · exact .clockPrincipal zero clock (source_clock_principal_return event n pd ps dL dR sL sR zero clock)

end LowEnergy.GaussComposite.ActualDressedOrderedStatic
