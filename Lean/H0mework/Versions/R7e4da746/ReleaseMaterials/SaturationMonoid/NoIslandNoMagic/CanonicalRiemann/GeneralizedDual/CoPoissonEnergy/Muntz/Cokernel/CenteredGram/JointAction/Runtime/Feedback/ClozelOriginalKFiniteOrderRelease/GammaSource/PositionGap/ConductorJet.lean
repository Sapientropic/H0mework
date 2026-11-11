import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionSecondConductor

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.ConductorJet

open BurnolPhysicalState CofinalCanonicalSourceMaterial DivisionConductor
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.WeightedRadialKernel
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower

open private conductor_unique from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
open private gamma_pair_fourier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
open private actual_R_reflect seed_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial

local notation "R" => burnolDirectRightResolventCLM
local notation "G" => gammaR
local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)

private theorem gammaR_even (c : BurnolCompletedMellinCoordinate) (x : BurnolL2)
    (even : reflectL2 x = x) : reflectL2 (G c x) = G c x := by
  have graph := actual_gamma_R c x even
  have once := gamma_pair_fourier _ _ graph
  have twice := gamma_pair_fourier _ _ once
  have preserved : reflectL2 (R c x) = R c x := by
    change reflectL2 (burnolDirectRightResolvent (c.value/2) x) = _
    rw [actual_R_reflect, even]
    rfl
  simp only [fourierL2_fourierL2, preserved] at twice
  exact conductor_unique _ _ _ twice graph

private theorem gamma_power_even (c : BurnolCompletedMellinCoordinate) (x : BurnolL2)
    (even : reflectL2 x = x) (k : Nat) : reflectL2 (((G c)^k) x) = ((G c)^k) x := by
  induction k with
  | zero => exact even
  | succ k prior =>
    rw [pow_succ', mul_apply_eq_comp]
    exact gammaR_even c _ prior

private theorem gamma_pair_after_power (c : BurnolCompletedMellinCoordinate) (x g : BurnolL2)
    (paid : GammaPair x g) (k : Nat) : GammaPair (((R c)^k) x) (((R c)^k) g) := by
  induction k with
  | zero => exact paid
  | succ k prior =>
    rw [pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
    exact actual_Gamma_R c _ _ prior

/-- Each conductor level spends one actual R application from the source budget. -/
def jetField (c : BurnolCompletedMellinCoordinate) (x : BurnolL2) (budget degree : Nat) : BurnolL2 :=
  ((R c)^(budget-degree)) (((G c)^degree) x)

theorem jetField_zero (c : BurnolCompletedMellinCoordinate) (x : BurnolL2) (budget : Nat) :
    jetField c x budget 0 = ((R c)^budget) x := by
  rw [jetField, Nat.sub_zero, pow_zero, one_apply_eq_self]

theorem jetField_graph (c : BurnolCompletedMellinCoordinate) (x : BurnolL2)
    (even : reflectL2 x = x) (budget degree : Nat) (inside : degree < budget) :
    GammaPair (jetField c x budget degree) (jetField c x budget (degree+1)) := by
  have remainder : budget-degree = (budget-(degree+1))+1 := by omega
  unfold jetField
  rw [remainder, pow_succ, mul_apply_eq_comp, pow_succ' (G c), mul_apply_eq_comp]
  exact gamma_pair_after_power c _ _
    (actual_gamma_R c _ (gamma_power_even c x even degree)) _

/-- Below the top degree the original field is itself a literal R output. -/
theorem jetField_source (c : BurnolCompletedMellinCoordinate) (x : BurnolL2)
    (even : reflectL2 x = x) (budget degree : Nat) (inside : degree < budget) :
    let before := jetField c x (budget-1) degree;
    reflectL2 before = before ∧ R c before = jetField c x budget degree ∧
      G c before = jetField c x budget (degree+1) := by
  let before := jetField c x (budget-1) degree
  have present : R c before = jetField c x budget degree := by
    change R c (((R c)^(budget-1-degree)) (((G c)^degree) x)) = jetField c x budget degree
    unfold jetField
    rw [show budget-degree = (budget-1-degree)+1 by omega, pow_succ', mul_apply_eq_comp]
  have parity : reflectL2 before = before := by
    unfold before jetField
    rw [← actual_iterate_power]
    exact actual_iterate_even c _ (gamma_power_even c x even degree) _
  have actual := actual_gamma_R c before parity
  rw [present] at actual
  exact ⟨parity, present, conductor_unique _ _ _ actual (jetField_graph c x even budget degree inside)⟩

theorem jetField_step (c : BurnolCompletedMellinCoordinate) (x : BurnolL2)
    (budget degree : Nat) (paid : degree ≤ budget) :
    jetField c x (budget+1) degree = R c (jetField c x budget degree) := by
  unfold jetField
  rw [show budget+1-degree = (budget-degree)+1 by omega, pow_succ', mul_apply_eq_comp]

theorem jetField_new_top (c : BurnolCompletedMellinCoordinate) (x : BurnolL2) (budget : Nat) :
    jetField c x (budget+1) (budget+1) = G c (jetField c x budget budget) := by
  simp only [jetField, Nat.sub_self, pow_zero, one_apply_eq_self, pow_succ', mul_apply_eq_comp]

variable (observation : GeneratedRiemannZeroObservation)
variable (half : OriginalKCombCalculation.Half observation)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "budget" => CofinalCanonicalSourceMaterial.sourceIndex observation

/-- The inventory grows at exactly the literal source index of the original Division. -/
def divisionJet (ordinal : Nat) (degree : Fin (budget ordinal+1)) : BurnolL2 :=
  jetField c seed (budget ordinal) degree

theorem actual_division_jet_graph (ordinal : Nat) (degree : Fin (budget ordinal)) :
    GammaPair (divisionJet observation half ordinal degree.castSucc)
      (divisionJet observation half ordinal degree.succ) :=
  jetField_graph c seed seed_even _ _ degree.isLt

private theorem budget_step (ordinal : Nat) : budget (ordinal+1) = budget ordinal+1 := by
  unfold CofinalCanonicalSourceMaterial.sourceIndex
  omega

theorem actual_division_jet_write (ordinal : Nat) (degree : Fin (budget ordinal+1)) :
    divisionJet observation half (ordinal+1)
      (Fin.castLE (by rw [budget_step]; omega) degree) =
    R c (divisionJet observation half ordinal degree) := by
  change jetField c seed (budget (ordinal+1)) degree = R c (jetField c seed (budget ordinal) degree)
  rw [budget_step]
  exact jetField_step c seed _ _ (Nat.le_of_lt_succ degree.isLt)

theorem actual_division_jet_new_top (ordinal : Nat) :
    divisionJet observation half (ordinal+1) (Fin.last (budget (ordinal+1))) =
      G c (divisionJet observation half ordinal (Fin.last (budget ordinal))) := by
  change jetField c seed (budget (ordinal+1)) (budget (ordinal+1)) =
    G c (jetField c seed (budget ordinal) (budget ordinal))
  rw [budget_step]
  exact jetField_new_top c seed (budget ordinal)

variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (depth : Nat)

theorem actual_division_jet_zero (ordinal : Nat) :
    divisionJet observation half ordinal 0 =
      OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal := by
  change jetField c seed (budget ordinal) 0 = _
  rw [jetField_zero, actual_raw_field observation nontrivial half depth ordinal, actual_iterate_power]

include nontrivial depth in
theorem actual_division_jet_first_two (ordinal : Nat) :
    let b := budget ordinal;
    let first : Fin (b+1) := ⟨1, by dsimp [b, CofinalCanonicalSourceMaterial.sourceIndex]; omega⟩;
    let second : Fin (b+1) := ⟨2, by dsimp [b, CofinalCanonicalSourceMaterial.sourceIndex]; omega⟩;
    divisionJet observation half ordinal first = gammaAt observation half ordinal ∧
      divisionJet observation half ordinal second = secondGammaAt observation half ordinal := by
  let b := budget ordinal
  have large : 2 ≤ b := by unfold b CofinalCanonicalSourceMaterial.sourceIndex; omega
  have zero := actual_division_jet_zero observation half nontrivial depth ordinal
  have original := (actual_division_conductor observation nontrivial half depth ordinal).1
  have first := jetField_graph c seed seed_even b 0 (by omega)
  change GammaPair (divisionJet observation half ordinal 0) (jetField c seed b 1) at first
  rw [zero] at first
  have same := conductor_unique _ _ _ first original
  have second := jetField_graph c seed seed_even b 1 (by omega)
  rw [same] at second
  exact ⟨same, conductor_unique _ _ _ second (actual_division_second_conductor observation half ordinal)⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.ConductorJet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
