import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalCompletedSector

/-! The existing canonical source preparation itself supplies N1/G0. No
configuration profile, completion boundary or new quantum state is chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedCurrent
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open CanonicalCompletedSector QuantizationCheck.Fermion
attribute [local instance] SourceRealScalarFock.branchOrder

theorem canonical_seed_degreeSix :
    LowEnergy.MixedSymbol.degreeSix
      (Stage10.ChargedPreparation.CanonicalParticle.normalizedPreparation 0
        (Stage9DEF.Compatibility.embed (Stage9DEF.Source.vector 0))) = 0 := by
  rw [Stage10.ChargedPreparation.CanonicalParticle.normalized_source]
  funext spin
  simp [LowEnergy.MixedSymbol.degreeSix, Stage9DEF.Compatibility.embed,
    Stage9C.Material.SpinPair.sourceColorDiracMatter,
    Stage9C.Material.SpinPair.sourceColorDoubletMatter]

theorem canonical_seed_target_zero (i : Mode) (hi : i ∈ target) : seedCoordinates i = 0 := by
  cases i with
  | inr i => rfl
  | inl i =>
    have hs := (mem_target_left i).mp hi
    have h := congrArg (fun v => LowEnergy.Quantum.coordinates v i) canonical_seed_degreeSix
    rw [coordinates_degreeSix] at h
    simpa only [seedCoordinates, Sum.elim_inl, if_pos hs, one_mul, map_zero, Pi.zero_apply] using h

theorem canonical_seed_N1_G0 : GaussCoreLabel.fiberPiece (1, 0) seed = seed := by
  apply PiLp.ext
  intro word
  rw [GaussCoreLabel.fiberPiece_apply]
  have hs : seed word = oneParticle seedCoordinates word := rfl
  rw [hs]
  by_cases singleton : ∃ i : Mode, word = {i}
  · obtain ⟨i, rfl⟩ := singleton
    rw [oneParticle_singleton]
    by_cases hi : i ∈ target
    · rw [canonical_seed_target_zero i hi]
      simp only [ite_self]
    · have label : NativeHistoryGrade.sourceLabel ({i} : Occupation) = (1, 0) := by
        apply Prod.ext <;> apply Fin.ext
        · simp [NativeHistoryGrade.sourceLabel, NativeHistoryGrade.sourceNumber]
        · simp [NativeHistoryGrade.sourceLabel, NativeHistoryGrade.sourceGrade, SourceGradeTransport.count, hi]
      rw [if_pos label]
  · have hn : ∀ i : Mode, word ≠ {i} := by simpa only [not_exists] using singleton
    rw [oneParticle_eq_zero_of_not_singleton seedCoordinates word hn]
    simp only [ite_self]

#print axioms canonical_seed_N1_G0
end LowEnergy.CanonicalGradedCurrent
