import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.CoulombReplacement.Runtime.Facade
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Regression

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.CoulombReplacement.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.UnifiedOrbitals
open SourceFiniteData
open LAlanine40K2025.BasinRefinement.SourceSignedEvaluator
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open scoped BigOperators
noncomputable section

theorem target_parent_preserved :
    Weight.material.parent =
      Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.material ∧
      type_of% PreciseAtomicIQA.Runtime.sourceGeneratedPhysicalPreciseAtomicIQANext :=
  ⟨rfl,PreciseAtomicIQA.Runtime.sourceGeneratedPhysicalPreciseAtomicIQANext⟩

theorem weight_per_quartet (runtime : LivingRuntimeState process) (i j : Basis) :
    quartetErrorWeight i j ≤
      (1/10^12 : ℝ) * ((readMaterial runtime).pairMajorantTable i j : ℝ) *
        ((readMaterial runtime).sumBound : ℝ) := by
  rw [(material_read runtime).2]
  exact Weight.quartet_error_weight_le i j

theorem weight_uniform (runtime : LivingRuntimeState process) (i j : Basis) :
    quartetErrorWeight i j ≤
      (1/10^12 : ℝ) * ((readMaterial runtime).amaxBound : ℝ) *
        ((readMaterial runtime).sumBound : ℝ) := by
  rw [(material_read runtime).2]
  exact Weight.quartet_error_weight_uniform i j

theorem j_replacement (runtime : LivingRuntimeState process) (i j : Basis) :
    |(readMaterial runtime).parent.targetJ i j -
        (readMaterial runtime).parent.reportWeightedJ i j| ≤
      (1/10^12 : ℝ) * ((readMaterial runtime).amaxBound : ℝ) *
        ((readMaterial runtime).sumBound : ℝ) := by
  rw [(material_read runtime).2]
  exact Weight.report_J_replacement i j

theorem j_replacement_picohartree (runtime : LivingRuntimeState process) (i j : Basis) :
    10^12 * |(readMaterial runtime).parent.targetJ i j -
        (readMaterial runtime).parent.reportWeightedJ i j| ≤
      ((readMaterial runtime).amaxBound : ℝ) * ((readMaterial runtime).sumBound : ℝ) := by
  rw [(material_read runtime).2]
  exact Weight.report_J_replacement_picohartree i j

theorem d3_hartree_address_read (runtime : LivingRuntimeState process) :
    Hartree.Charge.Residual.Interaction.d3HartreeEnergy = (1/2 : ℝ) * ∑ a : Fin 4851,
      ((readMaterial runtime).parent.sourceCoefficient a : ℝ) *
        (readMaterial runtime).parent.targetJ (targetLeft a.val) (targetRight a.val) := by
  rw [(material_read runtime).2]
  exact Weight.d3_hartree_address

theorem blyp_replacement_read (runtime : LivingRuntimeState process) :
    |Hartree.Charge.Residual.Interaction.d3HartreeEnergy -
        (readMaterial runtime).reportHartree| ≤
      ((readMaterial runtime).hartreeBound : ℝ) := by
  rw [(material_read runtime).2]
  exact Weight.blyp_coulomb_replacement

theorem blyp_nanohartree_read (runtime : LivingRuntimeState process) :
    10^9 * |Hartree.Charge.Residual.Interaction.d3HartreeEnergy -
        (readMaterial runtime).reportHartree| ≤
      ((readMaterial runtime).hartreeNanoBound : ℝ) := by
  rw [(material_read runtime).2]
  exact Weight.blyp_coulomb_nanohartree

theorem blyp_nanohartree_lt (runtime : LivingRuntimeState process) :
    ((readMaterial runtime).hartreeNanoBound : ℝ) < 2426 := by
  rw [(material_read runtime).2]
  exact Weight.hartreeNanoBound_lt

theorem response (runtime : LivingRuntimeState process) :
    Reentry.Runtime.reentryResponse runtime.state.current = Frame.Runtime.parentResult := by
  have keeps : ∀ {state : process.State}, SourceNativeRuntimeReachableAt process state →
      Reentry.Runtime.reentryResponse state.current = Frame.Runtime.parentResult := by
    intro state reachable
    induction reachable with
    | initial => rfl
    | step prior kept => exact kept
  exact keeps runtime.reachable

theorem read_commutes_with_physicalOccurrence (runtime : LivingRuntimeState process) :
    Frame.Runtime.parentResult.nuclear.target =
        Reentry.Runtime.reentryFrame runtime.tick.next.state.current ∧
    Frame.Runtime.parentResult.realized =
        (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    Frame.Runtime.parentResult.clock =
        Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current ∧
    Frame.Runtime.parentResult.nuclear.targetLedger =
        Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current := by
  change Frame.Runtime.parentResult.nuclear.target =
      (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.target ∧
    Frame.Runtime.parentResult.realized =
      (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    Frame.Runtime.parentResult.clock =
      (Reentry.Runtime.reentryResponse runtime.state.current).clock ∧
    Frame.Runtime.parentResult.nuclear.targetLedger =
      (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.targetLedger
  rw [response]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem wholeLedger_same_occurrence (runtime : LivingRuntimeState process) :
    runtime.tick.generated.wholeLedgerWriteBack =
      Reentry.Runtime.reentryLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        runtime.state.current := rfl

theorem row_identity (runtime : LivingRuntimeState process) :
    (Reentry.Runtime.reentryOccurrenceEntry
      (Reentry.Runtime.reentryEmitted runtime.state.current)).1 =
        .bondDensityIncidenceAdjudication ∧
    (Reentry.Runtime.reentryOccurrenceEntry
      (Reentry.Runtime.reentryEmitted runtime.state.current)).claim =
        .registeredExperimentalGeometryModelBondTopology ∧
    (Reentry.Runtime.reentryOccurrenceEntry
      (Reentry.Runtime.reentryEmitted runtime.state.current)).progressBudget = 0 ∧
    LAlanine40K2025.Root.N.lineageAt Reentry.Runtime.reentrySupport =
      LAlanine40K2025.Source.key :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem clock_preserved (runtime : LivingRuntimeState process) :
    Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current =
      3 * Propagation.Producer.nativeClockStep := by
  change (Reentry.Runtime.reentryResponse runtime.state.current).clock = _
  rw [response]
  exact Frame.Runtime.parent_clock

theorem coulomb_column_rows (runtime : LivingRuntimeState process) :
    (Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).rowToIntegralExact ∧
    ((Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).aoPairBlocks.toList.map
      Array.size).sum = 4851 ∧
    ∀ b : Fin 4851,
      (((Reentry.Runtime.reentryCurrentLedger
        runtime.tick.next.state.current).aoPairBlocks)[b.val / 64]!)[b.val % 64]! =
        targetAORow b.val := by
  have ledger := (read_commutes_with_physicalOccurrence runtime).2.2.2
  rw [← ledger]
  exact ⟨Reentry.Producer.nuclearTargetEnergyRows_exact,
    Reentry.Producer.nuclearTargetEnergyCensus.1, fun b => rfl⟩

theorem blyp_coulomb_column_read (runtime : LivingRuntimeState process) :
    |10^9 * Hartree.Charge.Residual.Interaction.d3HartreeEnergy -
        ((Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).rowSum
          .coulomb : ℝ) -
        (readMaterial runtime).reportPotentialResidual| ≤ 863 ∧
    |10^9 * Hartree.Charge.Residual.Interaction.d3HartreeEnergy -
        (((Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current).integral
          .coulomb).independentIntegral : ℝ) -
        (readMaterial runtime).reportPotentialResidual| ≤ 860 := by
  have ledger := (read_commutes_with_physicalOccurrence runtime).2.2.2
  rw [← ledger]
  rw [(material_read runtime).2]
  exact ⟨Weight.blyp_coulomb_column, Weight.blyp_coulomb_integral⟩

structure PhysicalCoulombReplacementClosure : Prop where
  source : Weight.Closure
  parent : type_of% target_parent_preserved
  perQuartet : type_of% weight_per_quartet
  uniformWeight : type_of% weight_uniform
  jReplacement : type_of% j_replacement
  jReplacementPico : type_of% j_replacement_picohartree
  d3Address : type_of% d3_hartree_address_read
  blypReplacement : type_of% blyp_replacement_read
  nanoBound : type_of% blyp_nanohartree_read
  nanoLt : type_of% blyp_nanohartree_lt
  coulombColumn : type_of% coulomb_column_rows
  blypColumn : type_of% blyp_coulomb_column_read
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit =
    Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 186)

theorem sourceGeneratedPhysicalCoulombReplacementNext : PhysicalCoulombReplacementClosure :=
  ⟨(certificate_read afterFirst).2,target_parent_preserved,
    weight_per_quartet,weight_uniform,j_replacement,j_replacement_picohartree,
    d3_hartree_address_read,blyp_replacement_read,blyp_nanohartree_read,
    blyp_nanohartree_lt,coulomb_column_rows,blyp_coulomb_column_read,
    read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,
    row_identity,clock_preserved,all_original_faces,face_factorizes,
    generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.CoulombReplacement.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
