import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DenseDivisionPrice

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.FirstPaReturn

open BurnolPhysicalState Filter Set SourceGeneratedObservationAction
open OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial (sourceIndex)
open OriginalKFiniteOrderRelease.PositionGapCayley.AdjointGerm
open OriginalKFiniteOrderRelease.PositionGapCayley.DivisionXiEscape (divisionLeading actual_division_germ)
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped InnerProductSpace Topology

attribute [local instance] OriginalKCombCofinalPaAction.physicalComplete

open private original_power_read leading_continuous leading_nonzero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionXiEscape
open private right_quarter below_half adjoint_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private coordinate_eq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CrossUnitKSource
open private seed_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2*(j+1))
variable (half : OriginalKCombCalculation.Half observation)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate c
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "seed" => burnolPaCombApproximation 0
local notation "G" => locallyConstantFace burnolUnscaledCommonGapRadius
local notation "Pa" => burnolOriginalPaInL2
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "T" => sourceCayley c
local notation "J" => ContinuousLinearMap.adjoint (sourceCayley c)
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half

private def adjointOrbit (i : Nat) : BurnolL2 := (J^i) (seed : BurnolL2)
local notation "orbit" => adjointOrbit observation half

private def forwardFactor (t : ℝ) : ℂ := (-(1/denominator c t))^(sourceIndex observation 0)
local notation "weight" => forwardFactor observation half

private theorem weight_ne (t : ℝ) : weight t ≠ 0 :=
  pow_ne_zero _ (neg_ne_zero.mpr (div_ne_zero one_ne_zero (denominator_nonzero c t)))

private def seedLeading (t : ℝ) : ℂ := divisionLeading observation half 0 t / weight t

private theorem seed_leading_continuous : ContinuousAt (seedLeading observation half) 0 := by
  have inverse : ContinuousAt (fun t : ℝ => -(1/denominator c t)) 0 :=
    (continuousAt_const.div (denominator_continuous c).continuousAt (denominator_nonzero c 0)).neg
  exact (leading_continuous observation half 0).div (inverse.pow _) (weight_ne observation half 0)

private theorem seed_leading_ne : seedLeading observation half 0 ≠ 0 :=
  div_ne_zero (leading_nonzero observation half 0) (weight_ne observation half 0)

include nontrivial in
private theorem seed_germ :
    (fun t => M (probe c t) (seed : BurnolL2)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => (factor c t)^m * seedLeading observation half t := by
  filter_upwards [actual_division_germ observation nontrivial half 0 0] with t paid
  let reader := probe c t
  let w := reader.value/2
  have chart : burnolDivisionCompletedMellinCoordinate w (right_quarter reader) (below_half reader) = reader := by
    apply coordinate_eq
    change 2*(reader.value/2)=reader.value
    ring
  have written : M reader (raw 0 0) = weight t * M reader (seed : BurnolL2) := by
    rw [OriginalKCombFirstFullSourceDynamics.raw_xi_source observation nontrivial half 0 0]
    have effect := original_power_read observation nontrivial half (sourceIndex observation 0)
      w (right_quarter reader) (below_half reader)
    rw [chart] at effect
    exact effect
  have equation : weight t * M reader (seed : BurnolL2) =
      (factor c t)^m * divisionLeading observation half 0 t := written.symm.trans paid
  have separated : M reader (seed : BurnolL2) =
      ((factor c t)^m * divisionLeading observation half 0 t)/weight t :=
    (eq_div_iff (weight_ne observation half t)).mpr ((mul_comm _ _).trans equation)
  exact separated.trans (mul_div_assoc _ _ _)

private theorem seed_in_pa : (seed : BurnolL2) ∈ Pa :=
  Submodule.mem_map.mpr ⟨seed,burnolPaCombApproximation_mem 0,rfl⟩

private theorem pa_price_zero {value : BurnolL2} (inside : value ∈ Pa) : M barC value = 0 := by
  obtain ⟨p,belongs,rfl⟩ := Submodule.mem_map.mp inside
  have restrict := congrArg (fun f : BurnolPaAmbientCarrier →L[ℂ] ℂ => f p)
    (burnolAmbientCompletedMellinEvaluator_restrict barC)
  change M barC (p : BurnolL2) = burnolCompletedMellinEvaluator barC p at restrict
  have zero : riemannZeta (barC).value = 0 := observation.conjugate_mathlibZero
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal barC zero
  have silent := inner_eq_zero_symm.mp (orthogonal p belongs)
  exact restrict.trans ((burnolCompletedMellinRieszVector_readback barC p).symm.trans silent)

include nontrivial in
private theorem seed_reads :
    (∀ i < m, M barC (orbit i) = 0) ∧ M barC (orbit m) = seedLeading observation half 0 := by
  have gap : (seed : BurnolL2) ∈ G := (seed : BurnolPaAmbientCarrier).property.1.1
  have reads := actual_adjoint_germ_exit c (seed : BurnolL2) gap seed_even m
    (seedLeading observation half) (seed_leading_continuous observation half) (seed_leading_ne observation half)
    (seed_germ observation nontrivial half)
  exact ⟨reads.1, reads.2.1⟩

include nontrivial in
private theorem exits_at_bound : ¬ orbit m ∈ Pa := by
  have last := (seed_reads observation nontrivial half).2
  exact fun still => seed_leading_ne observation half (last.symm.trans (pa_price_zero observation half still))

include nontrivial in
private theorem exit_exists : ∃ i : Nat, ¬ orbit i ∈ Pa :=
  ⟨m,exits_at_bound observation nontrivial half⟩

/-- Select the first departure of the original seed's adjoint action from the original infinite Pa. -/
def exitIndex : Nat := open Classical in Nat.find (exit_exists observation nontrivial half)

local notation "k" => exitIndex observation nontrivial half

theorem first_exit :
    0 < k ∧ k ≤ m ∧ (¬ orbit k ∈ Pa) ∧ ∀ i < k, orbit i ∈ Pa := by
  classical
  let existsExit := exit_exists observation nontrivial half
  have outside : ¬ orbit k ∈ Pa := Nat.find_spec existsExit
  have positive : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro zero
    change ¬ (J^k) (seed : BurnolL2) ∈ Pa at outside
    rw [zero,pow_zero,one_apply_eq_self] at outside
    exact outside seed_in_pa
  exact ⟨positive,Nat.find_min' existsExit (exits_at_bound observation nontrivial half),
    outside,fun i earlier => not_not.mp (Nat.find_min existsExit earlier)⟩

private theorem projected_mem (value : BurnolL2) : E value ∈ burnolCompactCoPoissonClosedRange :=
  Submodule.starProjection_apply_mem _ _

private theorem projected_source (value : BurnolL2) : (E value : BurnolL2) ∈ Pa :=
  Submodule.mem_map.mpr ⟨E value,projected_mem value,rfl⟩

private theorem projection_fixed {value : BurnolL2} (inside : value ∈ Pa) :
    (E value : BurnolL2) = value := by
  obtain ⟨p,belongs,rfl⟩ := Submodule.mem_map.mp inside
  have physical : burnolEvenAmbientProjection (p : BurnolL2) = p :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self p
  have fixed : E (p : BurnolL2) = p := by
    change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (burnolEvenAmbientProjection (p : BurnolL2)) = p
    rw [physical]
    exact Submodule.starProjection_eq_self_iff.mpr belongs
  exact congrArg (fun v : BurnolPaAmbientCarrier => (v : BurnolL2)) fixed

def predecessor : BurnolL2 := orbit (k-1)
local notation "previous" => predecessor observation nontrivial half

private theorem predecessor_index : k-1 < k := by
  have positive := (first_exit observation nontrivial half).1
  omega

private theorem predecessor_mem : previous ∈ Pa :=
  (first_exit observation nontrivial half).2.2.2 _ (predecessor_index observation nontrivial half)

private theorem departure_outside : ¬ J previous ∈ Pa := by
  have positive := (first_exit observation nontrivial half).1
  have next : k-1+1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt positive)
  have actual : J previous = orbit k := by
    change J ((J^(k-1)) (seed : BurnolL2)) = (J^k) (seed : BurnolL2)
    rw [← mul_apply_eq_comp,← pow_succ',next]
  rw [actual]
  exact (first_exit observation nontrivial half).2.2.1

private theorem pa_position {value : BurnolL2} (inside : value ∈ Pa) :
    value ∈ HilbertInventory.PositionField := by
  obtain ⟨p, _, rfl⟩ := Submodule.mem_map.mp inside
  exact ⟨p.property.1.1, p.property.2⟩

private theorem departure_position : J previous ∈ HilbertInventory.PositionField := by
  have current := pa_position (predecessor_mem observation nontrivial half)
  have symmetric := mem_evenL2ClosedFace_iff.mp current.2
  have within := lt_of_lt_of_le (predecessor_index observation nontrivial half)
    (first_exit observation nontrivial half).2.1
  have head : M barC previous = 0 := (seed_reads observation nontrivial half).1 _ within
  exact ⟨(actual_gap_cayley_adjoint_iff c previous current.1 symmetric).2 head,
    mem_evenL2ClosedFace_iff.mpr (adjoint_even c previous symmetric)⟩

/-- The invisible source is the orthogonal remainder produced at the first departure. -/
def invisibleInput : BurnolL2 := OriginalKCombCofinalPaAction.invisible (J previous)
local notation "remainder" => invisibleInput observation nontrivial half

theorem invisible_input : E remainder = 0 :=
  OriginalKCombCofinalPaAction.invisible_mem _

/-- At the first Pa departure the invisible input still lies in the original even position gap. -/
theorem input_position : remainder ∈ HilbertInventory.PositionField :=
  HilbertInventory.PositionField.sub_mem (departure_position observation nontrivial half)
    (pa_position (projected_source (J previous)))

theorem input_nonzero : remainder ≠ 0 := by
  intro erased
  have same : J previous = (E (J previous) : BurnolL2) := sub_eq_zero.mp erased
  exact departure_outside observation nontrivial half (same.symm ▸ projected_source (J previous))

def cotest : BurnolPaAmbientCarrier := E previous
local notation "test" => cotest observation nontrivial half

/-- Apply the original R to the generated invisible input before projecting back to Pa. -/
def returned : BurnolPaAmbientCarrier :=
  E (OriginalKCombPhysicalAction.R observation nontrivial half remainder)

local notation "returnAt" => returned observation nontrivial half
local notation "R" => burnolDirectRightResolvent (observation.coordinate/2)

theorem return_energy :
    (sourceDamping c : ℂ) * inner ℂ test returnAt = inner ℂ remainder remainder := by
  let z := remainder
  let v := J previous
  have testIn : test ∈ burnolCompactCoPoissonClosedRange := projected_mem previous
  have same : (test : BurnolL2) = previous := projection_fixed (predecessor_mem observation nontrivial half)
  have silent : E z = 0 := invisible_input observation nontrivial half
  have invisibleNormal (g : BurnolPaAmbientCarrier) (inside : g ∈ burnolCompactCoPoissonClosedRange) :
      inner ℂ (g : BurnolL2) z = 0 := by
    have reads := (OriginalKCombCofinalPaAction.wholePa_normal_read z g inside).symm
    rw [silent,inner_zero_right] at reads
    exact reads
  have split : v = (E v : BurnolL2)+z := by
    change v = (E v : BurnolL2)+(v-(E v : BurnolL2))
    abel
  have energy : inner ℂ v z = inner ℂ z z :=
    (congrArg (fun u : BurnolL2 => inner ℂ u z) split).trans
      (by rw [inner_add_left,invisibleNormal (E v) (projected_mem v),zero_add])
  have step : inner ℂ (test : BurnolL2) (T z) = inner ℂ v z := by
    rw [same]
    exact (ContinuousLinearMap.adjoint_inner_left T z previous).symm
  have written : returnAt = E (R z) := by
    unfold returned
    rw [OriginalKCombCofinalRAction.original_R_direct]
  calc
    _ = (sourceDamping c : ℂ) * inner ℂ (test : BurnolL2) (R z) := by
      rw [written,OriginalKCombCofinalPaAction.wholePa_normal_read _ _ testIn]
    _ = inner ℂ (test : BurnolL2) (T z) := by
      have coordinate : (c).value = observation.coordinate := rfl
      rw [sourceCayley_apply,inner_add_right,invisibleNormal test testIn,inner_smul_right,zero_add,coordinate]
    _ = _ := step.trans energy

theorem return_nonzero : returnAt ≠ 0 := by
  intro erased
  have paid := return_energy observation nontrivial half
  rw [erased,inner_zero_right,mul_zero] at paid
  exact input_nonzero observation nontrivial half (inner_self_eq_zero.mp paid.symm)

/-- The generic action defect consumes the actual nonzero remainder on its original invisible fibre. -/
theorem source_defect_nonzero :
    actionDefect (OriginalKCombPhysicalAction.R observation nontrivial half).toLinearMap (E).toLinearMap
      ⟨remainder, invisible_input observation nontrivial half⟩ ≠ 0 :=
  fun zero => return_nonzero observation nontrivial half
    ((actionDefect_value_zero_iff _ _ _).mp zero)

/-- An independent retained original K price detects this actual return. -/
theorem visible_original_price (depth : Nat) :
    ∃ i : Nat, PhysicalPriceCountable.price
      (DenseDivisionPrice.height observation nontrivial half depth i) returnAt ≠ 0 := by
  by_contra! silent
  exact return_nonzero observation nontrivial half
    (DenseDivisionPrice.separates observation nontrivial half depth returnAt silent)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.FirstPaReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
