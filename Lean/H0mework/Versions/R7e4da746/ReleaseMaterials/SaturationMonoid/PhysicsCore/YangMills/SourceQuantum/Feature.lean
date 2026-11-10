import H0mework.Versions.R7e4da746.Physics.YangMillsSourceQuantum.Time
import H0mework.Versions.R2.Physics.GaugeSpectrum.Ground
import H0mework.Quantum.Generator.Approximate
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Dynamics.States.Approximate
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Dynamics.States.Witness

/-! The existing source ground projector filters the original preparation.
Its actual time derivative supplies the old near-state and cluster producers
on the full mother fibre, with the original source-response values retained. -/

set_option autoImplicit false
open Filter Topology
open scoped InnerProductSpace Matrix

namespace SaturationMonoid.PhysicsCore.YangMills.NativeSource
open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage9DEF
open Stage10.GaugeSpectrum FullPairing
noncomputable section

def groundFeature : Hilbert :=
  naturalCoordinates (Compatibility.embed (groundProjector *ᵥ Source.vector 0))

private theorem groundFeature_apply (i : FullPairing.Index) :
    groundFeature i = if i.1.val < 2 then prepared 0 i else 0 := by
  rcases i with ⟨spin, sector⟩
  rw [groundFeature, naturalCoordinates_apply, prepared, naturalCoordinates_apply]
  by_cases h : spin.val < 2
  all_goals
    simp only [Nat.lt_succ_iff] at h
    simp [Compatibility.embed, groundProjector_normalForm, Matrix.mulVec_diagonal,
      sourceColorDiracMatter, h]

theorem groundFeature_inner : inner ℂ groundFeature groundFeature = (1 / 2 : ℂ) := by
  rw [groundFeature, inner_embed, Compatibility.coordinates_embed, groundProjector_normalForm]
  norm_num [Matrix.mulVec_diagonal, Fintype.sum_prod_type, Fin.sum_univ_four,
    Fin.sum_univ_two, Source.vector_zero, spinPairCoefficients, map_ofNat]

private theorem groundFeature_ne_zero : groundFeature ≠ 0 := by
  intro h
  have value := groundFeature_inner
  rw [h, inner_zero_left] at value
  norm_num at value

instance : Nontrivial Hilbert := ⟨⟨groundFeature, 0, groundFeature_ne_zero⟩⟩

def normalizedFeature : Hilbert := (‖groundFeature‖⁻¹ : ℂ) • groundFeature

theorem normalizedFeature_norm : ‖normalizedFeature‖ = 1 := by
  rw [normalizedFeature, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr groundFeature_ne_zero)]

def sourcePreparation : Mother := (‖groundFeature‖⁻¹ : ℂ) •
  Compatibility.embed.comp ((Matrix.toLin' groundProjector).comp Compatibility.coordinates)

theorem sourcePreparation_value : operator sourcePreparation (prepared 0) = normalizedFeature := by
  rw [prepared, operator_coordinates]
  change naturalCoordinates ((‖groundFeature‖⁻¹ : ℂ) • Compatibility.embed
    (groundProjector *ᵥ Compatibility.coordinates (Compatibility.embed (Source.vector 0)))) = _
  rw [Compatibility.coordinates_embed, map_smul]
  rfl

theorem feature_source_pair (B C : Mother) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
        (Compatibility.responseMatrix
          (pairedMother (B.comp sourcePreparation) (C.comp sourcePreparation))) =
      inner ℂ (operator B normalizedFeature) (operator C normalizedFeature) := by
  rw [source_gram]
  have value (A : Mother) : operator (A.comp sourcePreparation) (prepared 0) =
      operator A normalizedFeature := by
    calc
      _ = operator A (operator sourcePreparation (prepared 0)) := by simp [operator]
      _ = _ := congrArg (operator A) sourcePreparation_value
  rw [value, value]

private theorem groundFeature_ground :
    Quantum.Generator.hamiltonian time (point groundFeature) = -(frequency : ℂ) • groundFeature := by
  rw [show Quantum.Generator.hamiltonian time (point groundFeature) =
    Quantum.Generator.hamiltonianOperator time (point groundFeature) from rfl,
    hamiltonian_point]
  apply PiLp.ext
  rintro ⟨spin, sector⟩
  change Complex.I * velocity groundFeature (spin, sector) =
    -(frequency : ℂ) * groundFeature (spin, sector)
  by_cases h : spin.val < 2
  · have same : velocity groundFeature (spin, sector) = velocity (prepared 0) (spin, sector) := by
      rw [velocity_apply, velocity_apply, groundFeature_apply, if_pos h]
    rw [same, groundFeature_apply, if_pos h]
    calc
      _ = Complex.I * quantumFeature
          (fun i => Stage10.Runtime.tick.answer 0 i * Dynamics.generator i) (spin, sector) :=
        congrArg (fun v : Hilbert => Complex.I * v (spin, sector)) (source_velocity 0)
      _ = _ := by
        change Complex.I * naturalCoordinates (Compatibility.embed
          (fun i => Stage10.Runtime.tick.answer 0 i * Dynamics.generator i)) (spin, sector) = _
        rw [Stage10.Runtime.tick_vector, naturalCoordinates_apply, prepared, naturalCoordinates_apply]
        simp only [Nat.lt_succ_iff] at h
        simp [Compatibility.embed, sourceColorDiracMatter,
          Dynamics.generator, Dynamics.rate, h]
        ring_nf
        simp [Complex.I_sq]
        ring
  · rw [velocity_apply, groundFeature_apply, if_neg h]
    simp

theorem normalizedFeature_ground :
    Quantum.Generator.hamiltonian time (point normalizedFeature) =
      -(frequency : ℂ) • normalizedFeature := by
  have same : point normalizedFeature = (‖groundFeature‖⁻¹ : ℂ) • point groundFeature :=
    Subtype.ext rfl
  rw [same, map_smul, groundFeature_ground, normalizedFeature, smul_comm]

theorem normalizedFeature_phase_error (t : ℝ) :
    ‖time (Multiplicative.ofAdd t) normalizedFeature -
      Quantum.Generator.energyPhase (-frequency) (-t) • normalizedFeature‖ = 0 := by
  have bound := Quantum.Generator.orbit_energy_error time (point normalizedFeature) (-frequency) t
  rw [normalizedFeature_ground, Complex.ofReal_neg] at bound
  have same : Quantum.Generator.orbit time (point normalizedFeature).val t =
      time (Multiplicative.ofAdd t) normalizedFeature := rfl
  rw [same] at bound
  change ‖time (Multiplicative.ofAdd t) normalizedFeature -
    Quantum.Generator.energyPhase (-frequency) (-t) • normalizedFeature‖ ≤
      |t| * ‖-(frequency : ℂ) • normalizedFeature - -(frequency : ℂ) • normalizedFeature‖ at bound
  have zero : ‖time (Multiplicative.ofAdd t) normalizedFeature -
      Quantum.Generator.energyPhase (-frequency) (-t) • normalizedFeature‖ ≤ 0 := by
    simpa only [sub_self, norm_zero, mul_zero] using bound
  exact le_antisymm zero (norm_nonneg _)

def featureWitness : Quantum.Dynamics.ClusterWitness (fun _ => Hilbert) (fun _ => time)
    (fun _ => normalizedFeature) :=
  Classical.choice <| Quantum.Dynamics.clusterWitness_of_asymptotic
    (fun _ => Hilbert) (fun _ => time) (fun _ => normalizedFeature)
    (fun _ => normalizedFeature_norm)
    (Quantum.Dynamics.vectorState_asymptotic_invariant
      (fun _ => Hilbert) (fun _ => time) (fun _ => normalizedFeature)
      (fun _ => normalizedFeature_norm)
      (fun _ t => Quantum.Generator.energyPhase (-frequency) (-t.toAdd))
      (fun _ _ => Quantum.Generator.energyPhase_norm _ _)
      (fun t => by
        have zero := normalizedFeature_phase_error t.toAdd
        change ‖time t normalizedFeature -
          Quantum.Generator.energyPhase (-frequency) (-t.toAdd) • normalizedFeature‖ = 0 at zero
        simpa only [zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))))

def motherFamily (B : Mother) : Quantum.Dynamics.Bounded (fun _ => Hilbert) :=
  ⟨fun _ => operator B, memℓp_infty ⟨‖operator B‖, by rintro _ ⟨k, rfl⟩; exact le_rfl⟩⟩

theorem featureWitness_source_pair (B C : Mother) :
    featureWitness.full (star (motherFamily B) * motherFamily C) =
      State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
        (Compatibility.responseMatrix
          (pairedMother (B.comp sourcePreparation) (C.comp sourcePreparation))) := by
  let A := star (motherFamily B) * motherFamily C
  have values (k : ℕ) : Quantum.Dynamics.vectorState (fun _ => Hilbert)
      (fun _ => normalizedFeature) k A =
        inner ℂ (operator B normalizedFeature) (operator C normalizedFeature) := by
    change inner ℂ normalizedFeature ((operator B).adjoint (operator C normalizedFeature)) = _
    exact ContinuousLinearMap.adjoint_inner_right _ _ _
  have image := featureWitness.cluster.continuousAt_comp (WeakDual.eval_continuous A).continuousAt
  have limit : Tendsto
      ((fun φ : WeakDual ℂ (Quantum.Dynamics.Bounded (fun _ => Hilbert)) => φ A) ∘
        Quantum.Dynamics.weakVector (fun _ => Hilbert) (fun _ => normalizedFeature))
      atTop (𝓝 (inner ℂ (operator B normalizedFeature) (operator C normalizedFeature))) := by
    change Tendsto (fun k => Quantum.Dynamics.vectorState (fun _ => Hilbert)
      (fun _ => normalizedFeature) k A) atTop _
    simpa only [values] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => inner ℂ (operator B normalizedFeature) (operator C normalizedFeature)) atTop _)
  exact (eq_of_nhds_neBot (image.clusterPt.mono limit)).trans (feature_source_pair B C).symm

end
end SaturationMonoid.PhysicsCore.YangMills.NativeSource
