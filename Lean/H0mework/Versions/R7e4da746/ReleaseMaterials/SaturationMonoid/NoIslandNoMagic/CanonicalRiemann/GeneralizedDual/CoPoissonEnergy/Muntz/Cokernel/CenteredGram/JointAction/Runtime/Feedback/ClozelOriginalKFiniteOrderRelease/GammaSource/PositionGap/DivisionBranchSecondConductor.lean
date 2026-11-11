import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextOutsideGamma.Second
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorSymmetry

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.DivisionConductor

open BurnolPhysicalState
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.JointLogConductor
open OriginalGamma.Source.KGamma OriginalGamma.Source.KGamma.Iterated
open ConductorJet
open scoped InnerProductSpace

open private conductor_unique literal_split from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
open private literal_raw from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionConductor

namespace D
export OriginalKCombFirstFullSourceDynamics (input raw first_pair)
end D

namespace H
export OriginalKCrossParameterRAdjointSource.GammaOutsideHistory (write write_graph physical_start_graph)
export OriginalKCrossParameterRAdjointSource.GammaOutsideHistory.Second
  (writeSecond write_second_graph historySecond)
end H

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "R" => burnolDirectRightResolventCLM
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "raw" => D.raw observation nontrivial half depth
local notation "input" => D.input observation nontrivial half depth
local notation "first" => branchGammaAt observation nontrivial half depth
local notation "fullSecond" => secondGammaAt observation half
local notation "start" => OriginalKCombPhysicalAction.value observation nontrivial depth half
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate

private def openingSecond : BurnolL2 :=
  H.writeSecond c (R c start, H.writeSecond c (start, 0))

private theorem opening_second_graph :
    GammaPair (first 0).2 (openingSecond observation nontrivial half depth) := by
  have physical : start ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
    rw [MaterialConsumer.value_actual_actor]
    exact actor_physical observation nontrivial half.down 0 m le_rfl
  have zero : GammaPair (0 : BurnolL2) 0 := by
    intro test
    simp only [inner_zero_right]
  have startGraph : GammaPair (O start) 0 :=
    H.physical_start_graph (⟨start, physical⟩ : BurnolPaAmbientCarrier)
  have once := H.write_graph c observation.mathlibZero start 0 startGraph
  have twice := H.write_graph c observation.mathlibZero (R c start) _ once
  have actual : OriginalKCombPhysicalAction.R observation nontrivial half = R c :=
    ContinuousLinearMap.ext (OriginalKCombCofinalRAction.original_R_direct observation nontrivial half)
  have read := congrArg Prod.snd (D.first_pair observation nontrivial half depth)
  change (input 0).2 = O ((OriginalKCombPhysicalAction.R observation nontrivial half)
    ((OriginalKCombPhysicalAction.R observation nontrivial half) start)) at read
  rw [actual] at read
  have existing := (actual_division_branch_conductor observation nontrivial half depth 0).2
  rw [read] at existing
  rw [conductor_unique _ _ _ existing twice]
  exact H.write_second_graph c (R c start) _ _
    (H.write_second_graph c start _ _ zero)

/-- The two actual opening writes and the original cofinal stock generate the second outside field. -/
def outsideSecondAt (ordinal : Nat) : BurnolL2 :=
  H.historySecond c raw (openingSecond observation nontrivial half depth) ordinal

local notation "outside" => outsideSecondAt observation nontrivial half depth

private theorem outside_second_graph (ordinal : Nat) : GammaPair (first ordinal).2 (outside ordinal) := by
  induction ordinal with
  | zero => exact opening_second_graph observation nontrivial half depth
  | succ n prior =>
    change GammaPair (first (n+1)).2 (H.writeSecond c (raw n, outside n))
    rw [actual_division_branch_conductor_step observation nontrivial half depth n]
    exact H.write_second_graph c (raw n) _ _ prior

/-- The original physical second field is the complete second write minus its generated outside slot. -/
def branchSecondAt (ordinal : Nat) : BurnolL2 × BurnolL2 :=
  (fullSecond ordinal - outside ordinal, outside ordinal)

local notation "second" => branchSecondAt observation nontrivial half depth

theorem actual_division_branch_second_conductor (ordinal : Nat) :
    GammaPair (first ordinal).1 (second ordinal).1 ∧
      GammaPair (first ordinal).2 (second ordinal).2 := by
  have external := outside_second_graph observation nontrivial half depth ordinal
  refine ⟨?_, external⟩
  have full := actual_division_second_conductor observation half ordinal
  have split : (first ordinal).1 = gammaAt observation half ordinal - (first ordinal).2 := by
    exact (sub_sub_cancel _ _).symm
  intro test
  change inner ℂ (wholeConductorTest test) (first ordinal).1 =
    inner ℂ (test.toLp 2 MeasureTheory.volume) (fullSecond ordinal - outside ordinal)
  rw [split, inner_sub_right, inner_sub_right, full test, external test]

theorem actual_division_branch_second_step (ordinal : Nat) :
    let output := H.writeSecond c (raw ordinal, (second ordinal).2);
    second (ordinal+1) = (R c (fullSecond ordinal) - output, output) := by
  change (fullSecond (ordinal+1) - _, _) = (R c (fullSecond ordinal) - _, _)
  rw [actual_division_second_step observation half nontrivial depth ordinal]
  rfl

private theorem input_even (ordinal : Nat) :
    reflectL2 (input ordinal).1 = (input ordinal).1 ∧
      reflectL2 (input ordinal).2 = (input ordinal).2 := by
  have physical : reflectL2 (burnolEvenAmbientProjectionEndomorphism (raw ordinal)) =
      burnolEvenAmbientProjectionEndomorphism (raw ordinal) :=
    mem_evenL2ClosedFace_iff.mp (burnolEvenAmbientProjection (raw ordinal)).property.2
  have split := congrArg Prod.fst (literal_split observation nontrivial half depth ordinal)
  change burnolEvenAmbientProjectionEndomorphism (raw ordinal) = (input ordinal).1 at split
  rw [split] at physical
  have whole : reflectL2 (raw ordinal) = raw ordinal := by
    rw [literal_raw observation nontrivial half depth, ← CofinalCanonicalSourceMaterial.actual_iterate_power]
    exact CofinalCanonicalSourceMaterial.actual_iterate_even _ _
      (mem_evenL2ClosedFace_iff.mp (burnolPaCombApproximation 0).property.2) _
  have residual : (input ordinal).2 = raw ordinal - (input ordinal).1 := by
    change _ = (input ordinal).1 + (input ordinal).2 - (input ordinal).1
    simp
  refine ⟨physical, ?_⟩
  rw [residual, map_sub, whole, physical]

/-- Independent original K reads both actual second slots using the even conductor graph. -/
theorem actual_division_branch_second_K_price (ordinal : Nat) (test : BurnolCompletedMellinCoordinate) :
    let K : BurnolL2 := burnolCompletedMellinRieszVector test;
    inner ℂ (actualSecondGammaKernel test) (input ordinal).1 = inner ℂ K (second ordinal).1 ∧
      inner ℂ (actualSecondGammaKernel test) (input ordinal).2 = inner ℂ K (second ordinal).2 := by
  let K : BurnolL2 := burnolCompletedMellinRieszVector test
  have kEven : reflectL2 K = K :=
    mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector test).property.2
  have kFirst := actual_gamma_original_kernel test
  have kSecond := actual_second_gamma_kernel test
  have kgEven := even_conductor_value _ _ kEven kFirst
  have price (x g s : BurnolL2) (even : reflectL2 x = x)
      (one : GammaPair x g) (two : GammaPair g s) :
      inner ℂ (actualSecondGammaKernel test) x = inner ℂ K s :=
    (even_conductor_symmetry c _ _ _ _ kgEven even kSecond one).trans
      (even_conductor_symmetry c _ _ _ _ kEven (even_conductor_value _ _ even one) kFirst two)
  have even := input_even observation nontrivial half depth ordinal
  have one := actual_division_branch_conductor observation nontrivial half depth ordinal
  have two := actual_division_branch_second_conductor observation nontrivial half depth ordinal
  exact ⟨price _ _ _ even.1 one.1 two.1, price _ _ _ even.2 one.2 two.2⟩

/-- The second action prices the full Gram of the two first fields, including their cross terms. -/
theorem actual_division_branch_second_gram (ordinal : Nat) :
    let x := input ordinal;
    let g := first ordinal;
    let s := second ordinal;
    Matrix.of (fun i j : Fin 2 => inner ℂ (![x.1, x.2] i) (![s.1, s.2] j)) =
      SourceGeneratedFiniteGram.Projection.gram ![g.1, g.2] := by
  let x := input ordinal
  let g := first ordinal
  let s := second ordinal
  have even := input_even observation nontrivial half depth ordinal
  have one := actual_division_branch_conductor observation nontrivial half depth ordinal
  have two := actual_division_branch_second_conductor observation nontrivial half depth ordinal
  have inputEven (i : Fin 2) : reflectL2 (![x.1, x.2] i) = ![x.1, x.2] i := by
    fin_cases i
    · exact even.1
    · exact even.2
  have firstGraph (i : Fin 2) : GammaPair (![x.1, x.2] i) (![g.1, g.2] i) := by
    fin_cases i
    · exact one.1
    · exact one.2
  have secondGraph (i : Fin 2) : GammaPair (![g.1, g.2] i) (![s.1, s.2] i) := by
    fin_cases i
    · exact two.1
    · exact two.2
  ext i j
  exact (even_conductor_symmetry c _ _ _ _ (inputEven i)
    (even_conductor_value _ _ (inputEven j) (firstGraph j)) (firstGraph i) (secondGraph j)).symm

end OriginalKFiniteOrderRelease.PositionGapCayley.DivisionConductor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
