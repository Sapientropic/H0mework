import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorYukawaMatrix
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorYukawaSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace LowEnergy.MixedSpectatorCandidate
open SaturationMonoid SaturationMonoid.PhysicsCore
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussYukawaCoefficient GaussCoreDifferential GaussCoreHilbert GaussHistoryHilbert GaussDensityCore
open scoped BigOperators InnerProductSpace

theorem actual_vacuum_primal_entry_nonzero :
    primal vacuum ⟨1,Sum.inl yukawaOutputA⟩ (rootIndex (3,2,1)) ≠ 0 := by
  rw [actual_vacuum_primal_entry]
  have hl : (Stage9C.Material.SpinPair.lapse : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt Stage9C.Material.SpinPair.lapse_pos
  have hp : yukawaSourcePhase ≠ 0 := by
    rw [←actual_vacuum_mass_entry]
    exact actual_vacuum_mass_entry_nonzero
  exact mul_ne_zero hl hp

/-- The isolated actual mother-CAR coefficient proves that the source's
literal joint-vacuum Yukawa acts nontrivially on this fixed mixed candidate. -/
theorem actual_candidate_vacuum_Y_nonzero (dual : Bool) :
    sourceMap vacuum (candidate dual) ≠ 0 := by
  have h := actual_candidate_Y_entry dual (fullMatrix vacuum)
  have hm : fullMatrix vacuum (yukawaTargetMode dual) (rootMode dual (3,2,1)) ≠ 0 := by
    cases dual
    · change primal vacuum ⟨1,Sum.inl yukawaOutputA⟩ (rootIndex (3,2,1)) ≠ 0
      exact actual_vacuum_primal_entry_nonzero
    · change -star (primal vacuum ⟨1,Sum.inl yukawaOutputA⟩ (rootIndex (3,2,1))) ≠ 0
      exact neg_ne_zero.mpr (star_ne_zero.mpr actual_vacuum_primal_entry_nonzero)
  have hi : inner ℂ (yukawaWitness dual) (sourceMap vacuum (candidate dual)) ≠ 0 := by
    change inner ℂ (yukawaWitness dual) (GaussQuantumMultiplier.quantized (fullMatrix vacuum) (candidate dual)) ≠ 0
    rw [h]
    exact mul_ne_zero (by norm_num) hm
  intro hz
  rw [hz,inner_zero_right] at hi
  exact hi rfl

/-- The generated source-point profile carries its actual nonzero first-Y
output into the original smooth physical core. -/
theorem actual_candidate_test_Y_nonzero (dual : Bool) (f : ScalarTest)
    (hf : f sourcePoint.val = 1) : GaussYukawaOperator.originalAction (candidateTest dual f) ≠ 0 := by
  intro hz
  have hv := congrArg (fun q : QuantumTest => q sourcePoint.val) hz
  change sourceMap (GaussNativePotential.scalarField sourcePoint.val)
    (f sourcePoint.val • candidate dual) = 0 at hv
  rw [hf,one_smul] at hv
  have hp : GaussNativePotential.scalarField sourcePoint.val = vacuum := by
    simp [GaussNativePotential.scalarField,GaussHistoryHilbert.sourcePoint]
  rw [hp] at hv
  exact actual_candidate_vacuum_Y_nonzero dual hv

/-- The native chart generates a genuine (3,0) source with nonzero source
and first-Y output; no nonzero premise is supplied to the producer. -/
theorem actual_generated_candidate_Y_source (dual : Bool) :
    ∃f : ScalarTest, f sourcePoint.val = 1 ∧
      GaussCoreLabel.project (3,0) (candidateTest dual f) = candidateTest dual f ∧
      embed (candidateTest dual f) ≠ 0 ∧
      embed (GaussYukawaOperator.originalAction (candidateTest dual f)) ≠ 0 := by
  obtain ⟨f,hf,hsector,hne⟩ := actual_candidate_core_source dual
  refine ⟨f,hf,hsector,hne,?_⟩
  intro hz
  exact actual_candidate_test_Y_nonzero dual f hf (embed_injective (hz.trans (map_zero embed).symm))

/-- The same source's nonzero literal Y output gives a nonzero globally
bounded normalized-Y reader, ready for ordinary resolvent high-frequency return. -/
theorem actual_generated_candidate_bounded_Y_source (dual : Bool) :
    ∃f : ScalarTest, f sourcePoint.val = 1 ∧
      GaussCoreLabel.project (3,0) (candidateTest dual f) = candidateTest dual f ∧
      GaussYukawaOperator.bounded (embed (candidateTest dual f)) ≠ 0 := by
  obtain ⟨f,hf,hsector,_,hY⟩ := actual_generated_candidate_Y_source dual
  refine ⟨f,hf,hsector,?_⟩
  intro hz
  rw [GaussYukawaOperator.bounded_core] at hz
  have ha : GaussYukawaCoefficient.action (candidateTest dual f) = 0 :=
    embed_injective (hz.trans (map_zero embed).symm)
  have ho : GaussYukawaOperator.originalAction (candidateTest dual f) = 0 := by
    rw [←GaussYukawaOperator.radius_action_return,ha,map_zero]
  exact hY ((congrArg embed ho).trans (map_zero embed))

end LowEnergy.MixedSpectatorCandidate
