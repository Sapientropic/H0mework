import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3NormalizedOutputPole
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeAdaptivePhysicalSoftReturn

/-! Upper-half-plane approach of the generated whole-output pole unit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3SourceEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse
open PreparationVacuumUncutYukawa PreparationVacuumSourcePreparedResponse
open GaussComposite.SourceGraph
open ActualDressedUniformMaterialCoefficients ActualElectronPhysicalJointInverse
open ActualElectronWholeChargeSoft
open SourcePropagationAlgebraicResponse SourcePropagationCommonMomentum
open LowEnergy.ActualDressedVisiblePole
open Filter
open scoped InnerProductSpace Topology

attribute [local irreducible] actualElectronPhysicalSeed actualElectronPhysicalResponse
  materialJointNumerator jointGenerator jointResolvent jointPolynomial compressionPolynomial
  physicalN3InputEnergyRead physicalN3InputEnergyNumerator
  physicalN3OutputEnergyNumerator physicalN3OutputEnergyGerm actualElectronPhysicalUnit
  physicalN3OutputPoleOrder physicalN3OutputPoleLeading physicalN3OutputPoleUnit

/-- The generated source phase of the pole order: the `I^M` carried by the positive
half-plane scaling `(iσ)^M` on the weighted response. -/
def physicalN3PolePhase (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (pole : N3SourceEnergyPole p F leg) : ℂ :=
  Complex.I ^ physicalN3OutputPoleOrder p F leg pole

theorem physical_n3_pole_phase_norm (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (pole : N3SourceEnergyPole p F leg) :
    ‖physicalN3PolePhase p F leg pole‖ = 1 := by
  unfold physicalN3PolePhase
  rw [norm_pow, Complex.norm_I, one_pow]

/-- The boundary curve `a + iσ` stays in the nonreal domain for `σ > 0` when `a` is the
generated real pole. -/
private theorem pole_boundary_curve (a : ℂ) (ha : a.im = 0) :
    Tendsto (fun σ : ℝ => a + Complex.I * (σ:ℂ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin a {z : ℂ | z.im ≠ 0}) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have cont : Continuous (fun σ : ℝ => a + Complex.I * (σ:ℂ)) :=
      continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
    simpa [ha] using (cont.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have pos : 0 < σ := Set.mem_Ioi.mp hσ
    have him : (a + Complex.I * (σ:ℂ)).im = σ := by
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add, ha]
    rw [him]
    exact ne_of_gt pos

/-- Normalization is continuous at a nonzero limit on any abstract normed space. -/
private theorem pole_normalize_tendsto {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {v : I → E} {L : E} {l : Filter I}
    (hlim : Tendsto v l (𝓝 L)) (hL : L ≠ 0) :
    Tendsto (fun z => (↑(‖v z‖) : ℂ)⁻¹ • v z) l (𝓝 ((↑‖L‖ : ℂ)⁻¹ • L)) := by
  have hnorm : Tendsto (fun z => ‖v z‖) l (𝓝 ‖L‖) := hlim.norm
  have hreal : Tendsto (fun z => ((‖v z‖ : ℝ) : ℂ)) l (𝓝 ((‖L‖ : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hnorm
  have hne : ((‖L‖ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact norm_ne_zero_iff.mpr hL
  have hinv : Tendsto (fun z => ((‖v z‖ : ℝ) : ℂ)⁻¹) l (𝓝 ((‖L‖ : ℂ))⁻¹) :=
    hreal.inv₀ hne
  exact hinv.smul hlim

/-- Normalizing a unit-modulus scalar multiple only carries the phase. -/
private theorem pole_normalize_unit_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : E) :
    (↑(‖ζ • x‖) : ℂ)⁻¹ • (ζ • x) = ζ • (↑(‖x‖) : ℂ)⁻¹ • x := by
  have h1 : ‖ζ • x‖ = ‖x‖ := by rw [norm_smul, hζ, one_mul]
  rw [h1]
  exact smul_comm _ _ _

/-- Normalization discards a positive real scalar factor (casted to ℂ). -/
private theorem pole_normalize_pos_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ρ : ℝ) (hρ : 0 < ρ) (x : E) :
    (↑(‖(ρ : ℂ) • x‖) : ℂ)⁻¹ • ((ρ : ℂ) • x) = (↑(‖x‖) : ℂ)⁻¹ • x := by
  have h1 : ‖(ρ : ℂ) • x‖ = ρ * ‖x‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  rw [h1, smul_smul]
  congr 1
  have hr : (ρ * ‖x‖)⁻¹ * ρ = ‖x‖⁻¹ := by
    rw [mul_inv, mul_assoc, mul_comm (‖x‖⁻¹) ρ, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hρ), one_mul]
  calc (↑(ρ * ‖x‖) : ℂ)⁻¹ * ↑ρ = ↑((ρ * ‖x‖)⁻¹ * ρ) := by
        rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
    _ = ↑‖x‖⁻¹ := by rw [hr]
    _ = (↑‖x‖ : ℂ)⁻¹ := by rw [Complex.ofReal_inv]

/-- On the positive half-plane the normalized weighted vector is the source phase times
the normalized vector itself. -/
private theorem pole_phase_normalize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : E) (σ : ℝ) (hσ : 0 < σ) (M : ℕ) :
    (↑(‖(Complex.I * (σ : ℂ))^M • w‖) : ℂ)⁻¹ • ((Complex.I * (σ : ℂ))^M • w) =
      (Complex.I)^M • (↑(‖w‖) : ℂ)⁻¹ • w := by
  have hp : 0 < σ ^ M := pow_pos hσ M
  have hpow : (Complex.I * (σ : ℂ)) ^ M = Complex.I ^ M * ↑(σ ^ M) := by
    rw [mul_pow, Complex.ofReal_pow]
  rw [hpow]
  have hsplit : (Complex.I ^ M * ↑(σ ^ M)) • w = Complex.I ^ M • (↑(σ ^ M) • w) :=
    mul_smul _ _ _
  rw [hsplit, pole_normalize_unit_smul (Complex.I ^ M)
    (by rw [norm_pow, Complex.norm_I, one_pow]) _]
  congr 1
  exact pole_normalize_pos_smul (σ ^ M) hp w

/-- The upper-half-plane normalized weighted limit: phase-rotated normalized `v` tends to
the normalized canonical leading vector. Generic over the carrier space. -/
private theorem pole_upper_unit_generic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : ℂ) (ha : a.im = 0) (M : ℕ) (v : ℂ → E) (L : E)
    (hl : Tendsto (fun z : ℂ => (z - a)^M • v z) (nhdsWithin a {z : ℂ | z.im ≠ 0}) (𝓝 L))
    (hL : L ≠ 0) :
    Tendsto (fun σ : ℝ => Complex.I^M • (↑(‖v (a + Complex.I * (σ : ℂ))‖) : ℂ)⁻¹ •
        v (a + Complex.I * (σ : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 ((↑‖L‖ : ℂ)⁻¹ • L)) := by
  have hcurve := pole_boundary_curve a ha
  have hw : Tendsto (fun σ : ℝ => ((a + Complex.I * (σ : ℂ)) - a)^M •
        v (a + Complex.I * (σ : ℂ)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) := hl.comp hcurve
  have hs : (fun σ : ℝ => ((a + Complex.I * (σ : ℂ)) - a)^M •
        v (a + Complex.I * (σ : ℂ)))
      = fun σ : ℝ => (Complex.I * (σ : ℂ))^M • v (a + Complex.I * (σ : ℂ)) := by
    funext σ
    congr 1
    ring
  rw [hs] at hw
  have hn := pole_normalize_tendsto hw hL
  refine hn.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact pole_phase_normalize (v (a + Complex.I * (σ : ℂ))) σ hσ M

/-- The generated pole phase times the original physical unit converges to the source
pole unit on the upper half-plane `pole.val + iσ`, `σ → 0⁺`. This is source phase
alignment: no unphased vector limit on arbitrary complex approaches is asserted. -/
theorem physical_n3_pole_upper_unit_limit (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg)
    (pole : N3SourceEnergyPole p F leg) :
    Tendsto (fun σ : ℝ =>
        physicalN3PolePhase p F leg pole •
          actualElectronPhysicalUnit p F (pole.val + Complex.I * (σ : ℂ)) leg)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (physicalN3OutputPoleUnit p F leg pole)) := by
  have hreal : pole.val.im = 0 :=
    physical_n3_energy_pole_real p F leg pole.val pole.property
  have hlim := pole_upper_unit_generic pole.val hreal
    (physicalN3OutputPoleOrder p F leg pole)
    (fun z => actualElectronPhysicalResponse p F z leg)
    (physicalN3OutputPoleLeading p F leg pole)
    (physical_n3_output_pole_boundary_limit p F leg pole)
    (physical_n3_output_pole_leading_nonzero p F leg pole)
  have hunit : (↑(‖physicalN3OutputPoleLeading p F leg pole‖) : ℂ)⁻¹ •
      physicalN3OutputPoleLeading p F leg pole =
      physicalN3OutputPoleUnit p F leg pole :=
    (physicalN3OutputPoleUnit.eq_def p F leg pole).symm
  rw [hunit] at hlim
  refine hlim.congr' ?_
  apply Eventually.of_forall
  intro σ
  simp only [physicalN3PolePhase]
  rw [actualElectronPhysicalUnit.eq_def]

/-- A source radius on which the phased upper unit stays within `actualSoftBudget m`. -/
private theorem pole_unit_radius_exists (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg)
    (pole : N3SourceEnergyPole p F leg) (m : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ σ : ℝ, 0 < σ → σ < r →
      ‖physicalN3PolePhase p F leg pole •
          actualElectronPhysicalUnit p F (pole.val + Complex.I * (σ : ℂ)) leg -
        physicalN3OutputPoleUnit p F leg pole‖ ≤ actualSoftBudget m := by
  have hlim := physical_n3_pole_upper_unit_limit p F leg pole
  rw [Metric.tendsto_nhdsWithin_nhds] at hlim
  obtain ⟨δ, hδ, hδ'⟩ := hlim (actualSoftBudget m) (actual_soft_budget_positive m)
  refine ⟨δ, hδ, fun σ hσ hlt => ?_⟩
  have hd : dist σ 0 < δ := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hσ]
    exact hlt
  have h := hδ' (x := σ) (Set.mem_Ioi.mpr hσ) hd
  rw [dist_eq_norm] at h
  exact h.le

/-- The source-generated positive radius inside which the phased unit stays within the
soft budget `m`; extracted from the genuine upper limit, no caller-supplied uniform
witness. -/
def physicalN3PoleEnergyRadius (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (pole : N3SourceEnergyPole p F leg) (m : ℕ) : ℝ :=
  (pole_unit_radius_exists p F leg pole m).choose

private theorem pole_radius_positive (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg)
    (pole : N3SourceEnergyPole p F leg) (m : ℕ) :
    0 < physicalN3PoleEnergyRadius p F leg pole m :=
  (pole_unit_radius_exists p F leg pole m).choose_spec.1

private theorem pole_radius_spec (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg)
    (pole : N3SourceEnergyPole p F leg) (m : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (hlt : σ < physicalN3PoleEnergyRadius p F leg pole m) :
    ‖physicalN3PolePhase p F leg pole •
        actualElectronPhysicalUnit p F (pole.val + Complex.I * (σ : ℂ)) leg -
      physicalN3OutputPoleUnit p F leg pole‖ ≤ actualSoftBudget m :=
  (pole_unit_radius_exists p F leg pole m).choose_spec.2 σ hσ hlt

/-- The adaptive approach scale: below the source radius and bounded by the soft budget. -/
def physicalN3PoleEnergyScale (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (pole : N3SourceEnergyPole p F leg) (m : ℕ) : ℝ :=
  min (physicalN3PoleEnergyRadius p F leg pole m / 2) (actualSoftBudget m)

theorem physical_n3_pole_scale_positive (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg)
    (pole : N3SourceEnergyPole p F leg) (m : ℕ) :
    0 < physicalN3PoleEnergyScale p F leg pole m :=
  lt_min (half_pos (pole_radius_positive p F leg pole m)) (actual_soft_budget_positive m)

theorem physical_n3_pole_scale_bound (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg)
    (pole : N3SourceEnergyPole p F leg) (m : ℕ) :
    physicalN3PoleEnergyScale p F leg pole m ≤ actualSoftBudget m :=
  min_le_right _ _

private theorem pole_scale_lt_radius (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg)
    (pole : N3SourceEnergyPole p F leg) (m : ℕ) :
    physicalN3PoleEnergyScale p F leg pole m <
      physicalN3PoleEnergyRadius p F leg pole m :=
  (min_le_left _ _).trans_lt (half_lt_self (pole_radius_positive p F leg pole m))

/-- The adaptive approach energy: the generated real pole plus the positive imaginary
step `i·scale m`. -/
def physicalN3PoleApproachEnergy (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (pole : N3SourceEnergyPole p F leg) (m : ℕ) : ℂ :=
  pole.val + Complex.I * (physicalN3PoleEnergyScale p F leg pole m : ℂ)

theorem physical_n3_pole_energy_nonreal (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg)
    (pole : N3SourceEnergyPole p F leg) (m : ℕ) :
    (physicalN3PoleApproachEnergy p F leg pole m).im ≠ 0 := by
  have hreal : pole.val.im = 0 :=
    physical_n3_energy_pole_real p F leg pole.val pole.property
  unfold physicalN3PoleApproachEnergy
  have him : (pole.val + Complex.I * ↑(physicalN3PoleEnergyScale p F leg pole m)).im =
      pole.val.im + physicalN3PoleEnergyScale p F leg pole m := by
    simp [Complex.add_im, Complex.mul_im]
  rw [him, hreal, zero_add]
  exact ne_of_gt (physical_n3_pole_scale_positive p F leg pole m)

theorem physical_n3_pole_energy_tendsto (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg)
    (pole : N3SourceEnergyPole p F leg) :
    Tendsto (fun m => physicalN3PoleApproachEnergy p F leg pole m) atTop (𝓝 pole.val) := by
  have hs : Tendsto (fun m => physicalN3PoleEnergyScale p F leg pole m) atTop (𝓝 0) :=
    squeeze_zero (fun m => (physical_n3_pole_scale_positive p F leg pole m).le)
      (fun m => physical_n3_pole_scale_bound p F leg pole m) actual_soft_budget_tendsto
  have hc : Tendsto (fun m => pole.val +
        Complex.I * ↑(physicalN3PoleEnergyScale p F leg pole m))
      atTop (𝓝 (pole.val + Complex.I * (0 : ℂ))) :=
    tendsto_const_nhds.add
      (tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto 0).comp hs))
  unfold physicalN3PoleApproachEnergy
  simpa only [Complex.ofReal_zero, mul_zero, add_zero] using hc

/-- The phased approach unit: the source phase times the original physical unit at the
approach energy. -/
def physicalN3PoleApproachUnit (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (pole : N3SourceEnergyPole p F leg) (m : ℕ) : H :=
  physicalN3PolePhase p F leg pole •
    actualElectronPhysicalUnit p F (physicalN3PoleApproachEnergy p F leg pole m) leg

theorem physical_n3_pole_approach_unit_norm (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg)
    (pole : N3SourceEnergyPole p F leg) (m : ℕ) :
    ‖physicalN3PoleApproachUnit p F leg pole m‖ = 1 := by
  unfold physicalN3PoleApproachUnit
  rw [norm_smul, physical_n3_pole_phase_norm, one_mul,
    actual_electron_physical_unit_norm p F _
      (physical_n3_pole_energy_nonreal p F leg pole m) leg]

theorem physical_n3_pole_approach_error (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg)
    (pole : N3SourceEnergyPole p F leg) (m : ℕ) :
    ‖physicalN3PoleApproachUnit p F leg pole m -
      physicalN3OutputPoleUnit p F leg pole‖ ≤ actualSoftBudget m :=
  pole_radius_spec p F leg pole m _
    (physical_n3_pole_scale_positive p F leg pole m)
    (pole_scale_lt_radius p F leg pole m)

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
