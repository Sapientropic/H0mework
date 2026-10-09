import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedCurrentPair.Partition

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000

namespace CPS1AddressedCurrentPair
noncomputable section
open CPS1ElectronicSource CPS1Deformation CPS1AddressedTransfer
open CPS1MolecularFrame (NuclearIndex)
open scoped BigOperators InnerProductSpace
variable {frame : CPS1Recycling.Frame}

private theorem matrix_action_symmetric {ι : Type*} [Fintype ι]
    (fields : ι → SpinSpace) (matrix : Matrix ι ι ℂ) (hermitian : matrix.IsHermitian)
    (left right : SpinSpace) :
    inner ℂ (∑ first, ∑ second, matrix first second •
      (inner ℂ (fields second) left • fields first)) right =
    inner ℂ left (∑ first, ∑ second, matrix first second •
      (inner ℂ (fields second) right • fields first)) := by
  classical
  simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [hermitian.apply first second,
    show star (inner ℂ (fields first) left) = inner ℂ left (fields first) from
      inner_conj_symm (𝕜 := ℂ) left (fields first)]
  ring

theorem physical_action_symmetric (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) (left right : SpinSpace) :
    inner ℂ (physicalAction source positions occupied left) right =
      inner ℂ left (physicalAction source positions occupied right) := by
  simp only [physicalAction,sum_apply,smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply]
  exact matrix_action_symmetric _ _ (normed_physical_fock_hermitian source positions occupied) left right

def midpointFields (state : Material frame) (time : ℝ) (slot : ElectronIndex state.reference.geometry) : SpinSpace :=
  Generic.midpoint (seedFields state time slot) (responseFields state time slot)

theorem midpoint_generated (state : Material frame) (time : ℝ) (slot : ElectronIndex state.reference.geometry) :
    midpointFields state time slot ∈ fullSpace state.reference (state.movedPositions time) :=
  Submodule.smul_mem _ _ (Submodule.add_mem _ (occupied_in_full _ _ _ _) (occupied_in_full _ _ _ _))

def pairCurrent (state : Material frame) (first : NuclearIndex state.reference) (time : ℝ)
    (left right : NuclearIndex state.reference) : ℝ :=
  ∑ slot, (inner ℂ
    (projection state.reference (state.movedPositions time) first left (midpointFields state time slot))
    (responseAction state time
      (projection state.reference (state.movedPositions time) first right (midpointFields state time slot)))).im

theorem pair_antisymmetric (state : Material frame) (first : NuclearIndex state.reference) (time : ℝ)
    (left right : NuclearIndex state.reference) :
    pairCurrent state first time right left = -pairCurrent state first time left right := by
  unfold pairCurrent
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro slot _
  unfold responseAction
  rw [← physical_action_symmetric state.reference (state.movedPositions time) (seedOccupation state time)]
  exact inner_im_symm (𝕜 := ℂ) (E := SpinSpace)
    (physicalAction state.reference (state.movedPositions time) (seedOccupation state time)
      (projection state.reference (state.movedPositions time) first right (midpointFields state time slot)))
    (projection state.reference (state.movedPositions time) first left (midpointFields state time slot))

theorem pair_diagonal (state : Material frame) (first : NuclearIndex state.reference) (time : ℝ)
    (index : NuclearIndex state.reference) : pairCurrent state first time index index = 0 := by
  have symmetric := pair_antisymmetric state first time index index
  linarith

def rowFlux (state : Material frame) (first : NuclearIndex state.reference) (time : ℝ)
    (index : NuclearIndex state.reference) : ℝ :=
  Generic.midpointFlux (projection state.reference (state.movedPositions time) first index)
    (responseAction state time) (seedFields state time) (responseFields state time)

theorem row_sum (state : Material frame) (first : NuclearIndex state.reference) (time : ℝ)
    (index : NuclearIndex state.reference) :
    ∑ partner : NuclearIndex state.reference, pairCurrent state first time index partner =
      rowFlux state first time index := by
  unfold pairCurrent rowFlux Generic.midpointFlux
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro slot _
  rw [← Complex.im_sum,← inner_sum,← map_sum]
  rw [projections_reconstruct _ _ _ _ (midpoint_generated state time slot)]
  exact congrArg Complex.im (Generic.projected_inner
    (sectorSpace state.reference (state.movedPositions time) first index)
    (midpointFields state time slot) (responseAction state time (midpointFields state time slot))).symm

theorem first_row_sum (state : Material frame) (first : NuclearIndex state.reference) (time : ℝ) :
    ∑ partner : NuclearIndex state.reference, pairCurrent state first time first partner =
      responseFlux state first time := by
  rw [row_sum,rowFlux,first_projection]
  rfl

theorem total_pair_conserved (state : Material frame) (first : NuclearIndex state.reference) (time : ℝ) :
    (∑ left : NuclearIndex state.reference, ∑ right : NuclearIndex state.reference,
      pairCurrent state first time left right) = 0 := by
  have reverse : (∑ left : NuclearIndex state.reference, ∑ right : NuclearIndex state.reference,
      pairCurrent state first time left right) =
      -(∑ left : NuclearIndex state.reference, ∑ right : NuclearIndex state.reference,
        pairCurrent state first time left right) := by
    calc
      _ = ∑ right : NuclearIndex state.reference, ∑ left : NuclearIndex state.reference,
        pairCurrent state first time left right := Finset.sum_comm
      _ = ∑ right : NuclearIndex state.reference, ∑ left : NuclearIndex state.reference,
        -pairCurrent state first time right left := by
          apply Finset.sum_congr rfl
          intro right _
          apply Finset.sum_congr rfl
          intro left _
          exact pair_antisymmetric state first time right left
      _ = _ := by simp only [Finset.sum_neg_distrib]
  linarith

def sectorPopulation (state : Material frame) (first : NuclearIndex state.reference) (time : ℝ)
    (index : NuclearIndex state.reference) (after : Bool) : ℝ :=
  Generic.population (projection state.reference (state.movedPositions time) first index)
    (if after then responseFields state time else seedFields state time)

theorem sector_population_change (state : Material frame) (first : NuclearIndex state.reference) (time : ℝ)
    (index : NuclearIndex state.reference) :
    sectorPopulation state first time index true-sectorPopulation state first time index false =
      2*time*(∑ partner : NuclearIndex state.reference, pairCurrent state first time index partner) := by
  rw [row_sum]
  exact Generic.total_cayley_population_change _ _ _ _ time (response_midpoint state time)

theorem norm_partition (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first : NuclearIndex source) (field : SpinSpace) (generated : field ∈ fullSpace source positions) :
    (∑ index : NuclearIndex source, ‖projection source positions first index field‖^2) = ‖field‖^2 := by
  have exactInner (index : NuclearIndex source) :
      ‖projection source positions first index field‖^2 =
        (inner ℂ (projection source positions first index field) field).re := by
    unfold projection
    rw [← Generic.projected_inner (sectorSpace source positions first index) field field]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
  simp_rw [exactInner]
  rw [← Complex.re_sum,← sum_inner,projections_reconstruct source positions first field generated]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) field

theorem population_number (state : Material frame) (first : NuclearIndex state.reference) (time : ℝ)
    (after : Bool)
    (normalized : normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) =
      .ok (seedOccupation state time)) :
    (∑ index : NuclearIndex state.reference, sectorPopulation state first time index after) =
      electronCount frame state.reference.geometry.originJoint := by
  have good : Orthonormal ℂ (if after then responseFields state time else seedFields state time) := by
    cases after
    · exact response_seed_good state time normalized
    · exact response_after_good state time normalized
  have generated (slot : ElectronIndex state.reference.geometry) :
      (if after then responseFields state time else seedFields state time) slot ∈
        fullSpace state.reference (state.movedPositions time) := by
    cases after <;> exact occupied_in_full _ _ _ _
  unfold sectorPopulation Generic.population
  rw [Finset.sum_comm]
  simp_rw [norm_partition _ _ _ _ (generated _),good.1,one_pow]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,ElectronIndex,nsmul_eq_mul,mul_one]

theorem signed_partner_exists (state : Material frame) (first : NuclearIndex state.reference) (time : ℝ)
    (positive : 0 < time)
    (signed : 0 < responseFlux state first 0 * transferredPopulation state first time) :
    ∃ partner : NuclearIndex state.reference, partner ≠ first ∧
      0 < responseFlux state first 0 * pairCurrent state first time first partner := by
  classical
  have fullPositive : 0 < responseFlux state first 0 * responseFlux state first time := by
    rw [response_population] at signed
    have rearranged : responseFlux state first 0*(2*time*responseFlux state first time) =
        (2*time)*(responseFlux state first 0*responseFlux state first time) := by ring
    rw [rearranged] at signed
    exact pos_of_mul_pos_right signed (le_of_lt (mul_pos (by norm_num) positive))
  by_contra absent
  have all (partner : NuclearIndex state.reference) :
      responseFlux state first 0*pairCurrent state first time first partner ≤ 0 := by
    by_cases same : partner = first
    · rw [same,pair_diagonal,mul_zero]
    · apply le_of_not_gt
      intro contribution
      exact absent ⟨partner,same,contribution⟩
  have nonpositive : (∑ partner : NuclearIndex state.reference,
      responseFlux state first 0*pairCurrent state first time first partner) ≤ 0 :=
    Finset.sum_nonpos (fun partner _ => all partner)
  rw [← Finset.mul_sum,first_row_sum] at nonpositive
  exact not_lt_of_ge nonpositive fullPositive

end
end CPS1AddressedCurrentPair
