import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.GaugeTriplet
import H0mework.Physics.LowEnergy.Electromagnetic.Identification.Composite
import H0mework.Physics.GaugeStanding.ScalarPairingSkew

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
noncomputable section

namespace LowEnergy.DressedColourYScalarColumns

open SaturationMonoid SaturationMonoid.PhysicsCore SU7MotherLieAlgebra
open SU7ExteriorMatterRestriction SU7ExteriorMatterRepresentation
open StageNineExteriorMotherLieRepresentation StageNineHolonomicField
open StageNineP286GaugeConnectionVariation
open LowEnergy.Electromagnetic.Identification
open GaugeProjection.ConcreteBlockDiagonal

local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

private def complement (color : Fin 3) : Fin 2 → Fin 3 :=
  if color = 0 then ![1, 2] else if color = 1 then ![0, 2] else ![0, 1]

private def spectator (channel : Fin 2) : Fin 2 → SU7MotherIndex :=
  if channel = 0 then
    ![Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1)]
  else
    ![Sum.inr (Sum.inr (Sum.inl 0)), Sum.inr (Sum.inr (Sum.inr 0))]

private def scalarIndices (channel : Fin 2) (color : Fin 3) : Fin 4 → SU7MotherIndex :=
  ![Sum.inl (complement color 0), Sum.inl (complement color 1),
    spectator channel 0, spectator channel 1]

private theorem scalar_enumeration (channel : Fin 2) (color : Fin 3) (position : Fin 4) :
    Set.powersetCard.ofFinEmbEquiv.symm (Composite.scalarBasis channel color) position =
      scalarIndices channel color position := by
  let family := scalarIndices channel color
  have membership (p : Fin 4) : family p ∈ (Composite.scalarBasis channel color).1 := by
    fin_cases channel <;> fin_cases color <;> fin_cases p <;> decide
  have unique : family =
      (Composite.scalarBasis channel color).1.orderEmbOfFin
        (Composite.scalarBasis channel color).prop := by
    apply Finset.orderEmbOfFin_unique _ membership
    intro first second ordered
    fin_cases channel <;> fin_cases color <;> fin_cases first <;> fin_cases second
    all_goals try norm_num at ordered
    all_goals decide
  exact (congrFun unique position).symm

theorem scalar_basis_wedge (channel : Fin 2) (color : Fin 3) :
    su7ExteriorBasis 4 (Composite.scalarBasis channel color) =
      (exteriorPower.ιMulti ℂ 4)
        (fun p => su7FundamentalBasis (scalarIndices channel color p)) := by
  erw [← exteriorBasisInput_wedge_eq_basis_slot]
  apply congrArg (exteriorPower.ιMulti ℂ 4)
  funext position
  change su7FundamentalBasis
    (Set.powersetCard.ofFinEmbEquiv.symm (Composite.scalarBasis channel color) position) = _
  erw [scalar_enumeration]

def signedScalarBasis (channel : Fin 2) (color : Fin 3) :=
  (if color = 1 then (-1 : ℂ) else 1) • su7ExteriorBasis 4 (Composite.scalarBasis channel color)

theorem signed_scalar_basis_wedge (channel : Fin 2) (color : Fin 3) :
    signedScalarBasis channel color =
      (if color = 1 then (-1 : ℂ) else 1) •
        (exteriorPower.ιMulti ℂ 4)
          (fun p => su7FundamentalBasis (scalarIndices channel color p)) := by
  erw [signedScalarBasis, scalar_basis_wedge]

/-- Weak spectator column: only the weak block survives. -/
private theorem p286_fundamental_weak (data : P286LieBlockData) (w : Fin 2) :
    fundamentalMotherLieAction (p286LieBlockEmbed data)
        (su7FundamentalBasis (Sum.inr (Sum.inl w))) =
      ∑ w' : Fin 2, (data.2.1 : Matrix (Fin 2) (Fin 2) ℂ) w' w •
        su7FundamentalBasis (Sum.inr (Sum.inl w')) := by
  ext row
  rcases row with c | w' | p | m
  all_goals try fin_cases p
  all_goals try fin_cases m
  all_goals simp [fundamentalMotherLieAction,su7FundamentalBasis,p286LieBlockEmbed,rawP286LieBlock,
    weakHyperchargeLieBlock,hyperchargeLieBlock,scalarLieBlock,Matrix.mulVecLin,Matrix.mulVec,dotProduct,
    Pi.single_apply,mul_ite]

/-- Hypercharge-minus column is the `-H` eigenline. -/
private theorem p286_fundamental_hyper_minus (data : P286LieBlockData) :
    fundamentalMotherLieAction (p286LieBlockEmbed data)
        (su7FundamentalBasis (Sum.inr (Sum.inr (Sum.inr 0)))) =
      -(data.2.2.1) • su7FundamentalBasis (Sum.inr (Sum.inr (Sum.inr 0))) := by
  ext row
  rcases row with c | w | p | m
  all_goals try fin_cases p
  all_goals try fin_cases m
  all_goals simp [fundamentalMotherLieAction,su7FundamentalBasis,p286LieBlockEmbed,rawP286LieBlock,
    weakHyperchargeLieBlock,hyperchargeLieBlock,scalarLieBlock,Matrix.mulVecLin,Matrix.mulVec,dotProduct,
    Pi.single_apply,mul_ite]

/-- Updating a canonical tuple at a position already holding that entry leaves
it unchanged, hence the wedge is the basis vector. -/
private theorem wedge_same (channel : Fin 2) (c : Fin 3) (pos : Fin 4) :
    (exteriorPower.ιMulti ℂ 4)
        (Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
          (su7FundamentalBasis (scalarIndices channel c pos))) =
      su7ExteriorBasis 4 (Composite.scalarBasis channel c) := by
  erw [Function.update_eq_self, ← scalar_basis_wedge]

/-- Replacing a position by another occupied index gives a repeated entry. -/
private theorem wedge_repeat (channel : Fin 2) (c : Fin 3) (pos other : Fin 4)
    (hne : pos ≠ other) :
    (exteriorPower.ιMulti ℂ 4)
        (Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
          (su7FundamentalBasis (scalarIndices channel c other))) = 0 := by
  have hval : Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
        (su7FundamentalBasis (scalarIndices channel c other)) pos =
      Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
        (su7FundamentalBasis (scalarIndices channel c other)) other := by
    erw [Function.update_self, Function.update_of_ne hne.symm]
  exact (exteriorPower.ιMulti ℂ 4).map_eq_zero_of_eq _ hval hne

/-- A single-position update landing on another scalar-family tuple with a
concrete permutation sign. -/
private theorem wedge_move (channel : Fin 2) (c : Fin 3) (pos : Fin 4)
    (k : SU7MotherIndex) (channel' : Fin 2) (d : Fin 3) (σ : Equiv.Perm (Fin 4))
    (h : ∀ i, Function.update (scalarIndices channel c) pos k i =
        scalarIndices channel' d (σ i)) :
    (exteriorPower.ιMulti ℂ 4)
        (Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
          (su7FundamentalBasis k)) =
      σ.sign • su7ExteriorBasis 4 (Composite.scalarBasis channel' d) := by
  have key (i : Fin 4) :
      Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
          (su7FundamentalBasis k) i =
        su7FundamentalBasis (scalarIndices channel' d (σ i)) := by
    have hval := congrArg su7FundamentalBasis (h i)
    have eval : Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
          (su7FundamentalBasis k) i =
        su7FundamentalBasis
          (Function.update (scalarIndices channel c) pos k i) := by
      by_cases hpi : i = pos
      · subst hpi
        erw [Function.update_self, Function.update_self]
      · erw [Function.update_of_ne hpi, Function.update_of_ne hpi]
    erw [eval]
    exact hval
  have ht : Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
        (su7FundamentalBasis k) =
      (fun p => su7FundamentalBasis (scalarIndices channel' d p)) ∘ σ :=
    funext key
  erw [ht, AlternatingMap.map_perm, ← scalar_basis_wedge]

/-- Cross-slot eval with trivial permutation. -/
private theorem wedge_move_id (channel : Fin 2) (c : Fin 3) (pos : Fin 4)
    (k : SU7MotherIndex) (channel' : Fin 2) (d : Fin 3)
    (h : ∀ i, Function.update (scalarIndices channel c) pos k i =
        scalarIndices channel' d i) :
    (exteriorPower.ιMulti ℂ 4)
        (Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
          (su7FundamentalBasis k)) =
      su7ExteriorBasis 4 (Composite.scalarBasis channel' d) := by
  erw [wedge_move channel c pos k channel' d (Equiv.refl (Fin 4)) (by
    intro i; simpa only [Equiv.refl_apply] using h i), Equiv.Perm.sign_refl, one_smul]

/-- Cross-slot eval swapping positions 0 and 1. -/
private theorem wedge_move_swap (channel : Fin 2) (c : Fin 3) (pos : Fin 4)
    (k : SU7MotherIndex) (channel' : Fin 2) (d : Fin 3)
    (h : ∀ i, Function.update (scalarIndices channel c) pos k i =
        scalarIndices channel' d (Equiv.swap (0 : Fin 4) 1 i)) :
    (exteriorPower.ιMulti ℂ 4)
        (Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
          (su7FundamentalBasis k)) =
      -su7ExteriorBasis 4 (Composite.scalarBasis channel' d) := by
  erw [wedge_move channel c pos k channel' d (Equiv.swap (0 : Fin 4) 1) h,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)]
  simp

/-- The fundamental colour column inserted into a scalar slot. -/
private theorem colour_slot (data : P286LieBlockData) (channel : Fin 2) (c : Fin 3)
    (pos : Fin 4) (x : Fin 3) (hx : scalarIndices channel c pos = Sum.inl x) :
    (exteriorPower.ιMulti ℂ 4)
        (Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
          (fundamentalMotherLieAction (p286LieBlockEmbed data)
            (su7FundamentalBasis (scalarIndices channel c pos)))) =
      ∑ r : Fin 3, (data.1 : Matrix (Fin 3) (Fin 3) ℂ) r x •
        (exteriorPower.ιMulti ℂ 4)
          (Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
            (su7FundamentalBasis (Sum.inl r))) := by
  erw [hx, LowEnergy.MatterSpace.p286_fundamental_color,
    (exteriorPower.ιMulti ℂ 4).map_update_sum]
  simp_rw [(exteriorPower.ιMulti ℂ 4).map_update_smul]

/-- The fundamental weak column inserted into a scalar slot. -/
private theorem weak_slot (data : P286LieBlockData) (channel : Fin 2) (c : Fin 3)
    (pos : Fin 4) (w : Fin 2) (hx : scalarIndices channel c pos = Sum.inr (Sum.inl w)) :
    (exteriorPower.ιMulti ℂ 4)
        (Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
          (fundamentalMotherLieAction (p286LieBlockEmbed data)
            (su7FundamentalBasis (scalarIndices channel c pos)))) =
      ∑ w' : Fin 2, (data.2.1 : Matrix (Fin 2) (Fin 2) ℂ) w' w •
        (exteriorPower.ιMulti ℂ 4)
          (Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
            (su7FundamentalBasis (Sum.inr (Sum.inl w')))) := by
  erw [hx, p286_fundamental_weak,
    (exteriorPower.ιMulti ℂ 4).map_update_sum]
  simp_rw [(exteriorPower.ιMulti ℂ 4).map_update_smul]

/-- A hypercharge eigen-slot contributes its eigenvalue times the basis. -/
private theorem hyper_slot (data : P286LieBlockData) (channel : Fin 2) (c : Fin 3)
    (pos : Fin 4) (k : SU7MotherIndex) (Hcoef : ℂ)
    (hx : scalarIndices channel c pos = k)
    (hf : fundamentalMotherLieAction (p286LieBlockEmbed data)
        (su7FundamentalBasis k) = Hcoef • su7FundamentalBasis k) :
    (exteriorPower.ιMulti ℂ 4)
        (Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
          (fundamentalMotherLieAction (p286LieBlockEmbed data)
            (su7FundamentalBasis (scalarIndices channel c pos)))) =
      Hcoef • su7ExteriorBasis 4 (Composite.scalarBasis channel c) := by
  erw [hx, hf, (exteriorPower.ιMulti ℂ 4).map_update_smul]
  congr 1
  erw [← hx]
  exact wedge_same channel c pos

/-- Update-evaluation at the occupied entry: tuple-form convenience. -/
private theorem wedge_self' (channel : Fin 2) (c : Fin 3) (pos : Fin 4)
    (k : SU7MotherIndex) (hk : k = scalarIndices channel c pos) :
    (exteriorPower.ιMulti ℂ 4)
        (Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
          (su7FundamentalBasis k)) =
      su7ExteriorBasis 4 (Composite.scalarBasis channel c) := by
  erw [hk]; exact wedge_same channel c pos

/-- Update-evaluation at another occupied index vanishes. -/
private theorem wedge_repeat' (channel : Fin 2) (c : Fin 3) (pos other : Fin 4)
    (k : SU7MotherIndex) (hk : k = scalarIndices channel c other) (hne : pos ≠ other) :
    (exteriorPower.ιMulti ℂ 4)
        (Function.update (fun p => su7FundamentalBasis (scalarIndices channel c p)) pos
          (su7FundamentalBasis k)) = 0 := by
  erw [hk]; exact wedge_repeat channel c pos other hne

/-- The elementary six-column law: the P286 block Lie action on the signed
degree-four scalar basis vector `e_c` is `-∑_d A(c,d) • e_d`.  The two colour
positions contribute `A_{x,x}` diagonals and the missing-colour cross term;
the weak pair contributes `tr W = 0` and the hypercharge pair `H + (-H) = 0`. -/
theorem scalar_signed_column (data : P286LieBlockData) (channel : Fin 2) (c : Fin 3) :
    exteriorMotherLieAction 4 (p286LieBlockEmbed data) (signedScalarBasis channel c) =
      -(∑ d : Fin 3, ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) c d) •
        signedScalarBasis channel d) := by
  have traceA : (data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 +
      (data.1 : Matrix (Fin 3) (Fin 3) ℂ) 1 1 +
      (data.1 : Matrix (Fin 3) (Fin 3) ℂ) 2 2 = 0 := by
    have h := specialUnitaryLieMatrix_trace data.1
    simpa [Matrix.trace, Fin.sum_univ_three] using h
  have traceW : (data.2.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 +
      (data.2.1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := by
    have h := specialUnitaryLieMatrix_trace data.2.1
    simpa [Matrix.trace, Fin.sum_univ_two] using h
  erw [signedScalarBasis, map_smul, scalar_basis_wedge,
    exteriorMotherLieAction_eq_slotDerivedAction,
    exteriorSlotDerivedAction_apply_ιMulti, Fin.sum_univ_four]
  fin_cases channel <;> fin_cases c
  all_goals dsimp only
  · -- channel 0, colour 0: tuple [col1, col2, w0, w1]
    erw [colour_slot data 0 0 0 1 (by decide), Fin.sum_univ_three]
    erw [wedge_move_id 0 0 0 (Sum.inl 0) 0 1 (fun i => by fin_cases i <;> decide),
      wedge_self' 0 0 0 (Sum.inl 1) (by decide),
      wedge_repeat' 0 0 0 1 (Sum.inl 2) (by decide) (by decide)]
    simp only [smul_zero, add_zero]
    erw [colour_slot data 0 0 1 2 (by decide), Fin.sum_univ_three]
    erw [wedge_move_swap 0 0 1 (Sum.inl 0) 0 2 (fun i => by fin_cases i <;> decide),
      wedge_repeat' 0 0 1 0 (Sum.inl 1) (by decide) (by decide),
      wedge_self' 0 0 1 (Sum.inl 2) (by decide)]
    simp only [smul_zero, add_zero]
    erw [weak_slot data 0 0 2 0 (by decide), Fin.sum_univ_two,
      wedge_self' 0 0 2 (Sum.inr (Sum.inl 0)) (by decide),
      wedge_repeat' 0 0 2 3 (Sum.inr (Sum.inl 1)) (by decide) (by decide)]
    simp only [smul_zero, add_zero]
    erw [weak_slot data 0 0 3 1 (by decide), Fin.sum_univ_two,
      wedge_repeat' 0 0 3 2 (Sum.inr (Sum.inl 0)) (by decide) (by decide),
      wedge_self' 0 0 3 (Sum.inr (Sum.inl 1)) (by decide)]
    simp only [smul_zero, zero_add]
    erw [Fin.sum_univ_three]
    apply (su7ExteriorBasis 4).repr.injective
    ext J
    simp [signedScalarBasis, Finsupp.single_apply]
    split_ifs <;> first
      | (linear_combination traceA + traceW)
      | (linear_combination -traceA - traceW)
      | (linear_combination traceA)
      | (linear_combination -traceA)
      | ring
  · -- channel 0, colour 1: tuple [col0, col2, w0, w1], outer sign -1
    erw [colour_slot data 0 1 0 0 (by decide), Fin.sum_univ_three]
    erw [wedge_self' 0 1 0 (Sum.inl 0) (by decide),
      wedge_move_id 0 1 0 (Sum.inl 1) 0 0 (fun i => by fin_cases i <;> decide),
      wedge_repeat' 0 1 0 1 (Sum.inl 2) (by decide) (by decide)]
    simp only [smul_zero, add_zero]
    erw [colour_slot data 0 1 1 2 (by decide), Fin.sum_univ_three]
    erw [wedge_repeat' 0 1 1 0 (Sum.inl 0) (by decide) (by decide),
      wedge_move_id 0 1 1 (Sum.inl 1) 0 2 (fun i => by fin_cases i <;> decide),
      wedge_self' 0 1 1 (Sum.inl 2) (by decide)]
    simp only [smul_zero, zero_add]
    erw [weak_slot data 0 1 2 0 (by decide), Fin.sum_univ_two,
      wedge_self' 0 1 2 (Sum.inr (Sum.inl 0)) (by decide),
      wedge_repeat' 0 1 2 3 (Sum.inr (Sum.inl 1)) (by decide) (by decide)]
    simp only [smul_zero, add_zero]
    erw [weak_slot data 0 1 3 1 (by decide), Fin.sum_univ_two,
      wedge_repeat' 0 1 3 2 (Sum.inr (Sum.inl 0)) (by decide) (by decide),
      wedge_self' 0 1 3 (Sum.inr (Sum.inl 1)) (by decide)]
    simp only [smul_zero, zero_add]
    erw [Fin.sum_univ_three]
    apply (su7ExteriorBasis 4).repr.injective
    ext J
    simp [signedScalarBasis, Finsupp.single_apply]
    split_ifs <;> first
      | (linear_combination traceA + traceW)
      | (linear_combination -traceA - traceW)
      | (linear_combination traceA)
      | (linear_combination -traceA)
      | ring
  · -- channel 0, colour 2: tuple [col0, col1, w0, w1]
    erw [colour_slot data 0 2 0 0 (by decide), Fin.sum_univ_three]
    erw [wedge_self' 0 2 0 (Sum.inl 0) (by decide),
      wedge_repeat' 0 2 0 1 (Sum.inl 1) (by decide) (by decide),
      wedge_move_swap 0 2 0 (Sum.inl 2) 0 0 (fun i => by fin_cases i <;> decide)]
    simp only [smul_zero, add_zero]
    erw [colour_slot data 0 2 1 1 (by decide), Fin.sum_univ_three]
    erw [wedge_repeat' 0 2 1 0 (Sum.inl 0) (by decide) (by decide),
      wedge_self' 0 2 1 (Sum.inl 1) (by decide),
      wedge_move_id 0 2 1 (Sum.inl 2) 0 1 (fun i => by fin_cases i <;> decide)]
    simp only [smul_zero, zero_add]
    erw [weak_slot data 0 2 2 0 (by decide), Fin.sum_univ_two,
      wedge_self' 0 2 2 (Sum.inr (Sum.inl 0)) (by decide),
      wedge_repeat' 0 2 2 3 (Sum.inr (Sum.inl 1)) (by decide) (by decide)]
    simp only [smul_zero, add_zero]
    erw [weak_slot data 0 2 3 1 (by decide), Fin.sum_univ_two,
      wedge_repeat' 0 2 3 2 (Sum.inr (Sum.inl 0)) (by decide) (by decide),
      wedge_self' 0 2 3 (Sum.inr (Sum.inl 1)) (by decide)]
    simp only [smul_zero, zero_add]
    erw [Fin.sum_univ_three]
    apply (su7ExteriorBasis 4).repr.injective
    ext J
    simp [signedScalarBasis, Finsupp.single_apply]
    split_ifs <;> first
      | (linear_combination traceA + traceW)
      | (linear_combination -traceA - traceW)
      | (linear_combination traceA)
      | (linear_combination -traceA)
      | ring
  · -- channel 1, colour 0: tuple [col1, col2, h+, h-]
    erw [colour_slot data 1 0 0 1 (by decide), Fin.sum_univ_three]
    erw [wedge_move_id 1 0 0 (Sum.inl 0) 1 1 (fun i => by fin_cases i <;> decide),
      wedge_self' 1 0 0 (Sum.inl 1) (by decide),
      wedge_repeat' 1 0 0 1 (Sum.inl 2) (by decide) (by decide)]
    simp only [smul_zero, add_zero]
    erw [colour_slot data 1 0 1 2 (by decide), Fin.sum_univ_three]
    erw [wedge_move_swap 1 0 1 (Sum.inl 0) 1 2 (fun i => by fin_cases i <;> decide),
      wedge_repeat' 1 0 1 0 (Sum.inl 1) (by decide) (by decide),
      wedge_self' 1 0 1 (Sum.inl 2) (by decide)]
    simp only [smul_zero, add_zero]
    erw [hyper_slot data 1 0 2 hyperPlusIndex (data.2.2.1) (by decide)
        (LowEnergy.MatterSpace.p286_fundamental_hyper data),
      hyper_slot data 1 0 3 hyperMinusIndex (-(data.2.2.1)) (by decide)
        (p286_fundamental_hyper_minus data)]
    erw [Fin.sum_univ_three]
    apply (su7ExteriorBasis 4).repr.injective
    ext J
    simp [signedScalarBasis, Finsupp.single_apply]
    split_ifs <;> first
      | (linear_combination traceA + traceW)
      | (linear_combination -traceA - traceW)
      | (linear_combination traceA)
      | (linear_combination -traceA)
      | ring
  · -- channel 1, colour 1
    erw [colour_slot data 1 1 0 0 (by decide), Fin.sum_univ_three]
    erw [wedge_self' 1 1 0 (Sum.inl 0) (by decide),
      wedge_move_id 1 1 0 (Sum.inl 1) 1 0 (fun i => by fin_cases i <;> decide),
      wedge_repeat' 1 1 0 1 (Sum.inl 2) (by decide) (by decide)]
    simp only [smul_zero, add_zero]
    erw [colour_slot data 1 1 1 2 (by decide), Fin.sum_univ_three]
    erw [wedge_repeat' 1 1 1 0 (Sum.inl 0) (by decide) (by decide),
      wedge_move_id 1 1 1 (Sum.inl 1) 1 2 (fun i => by fin_cases i <;> decide),
      wedge_self' 1 1 1 (Sum.inl 2) (by decide)]
    simp only [smul_zero, zero_add]
    erw [hyper_slot data 1 1 2 hyperPlusIndex (data.2.2.1) (by decide)
        (LowEnergy.MatterSpace.p286_fundamental_hyper data),
      hyper_slot data 1 1 3 hyperMinusIndex (-(data.2.2.1)) (by decide)
        (p286_fundamental_hyper_minus data)]
    erw [Fin.sum_univ_three]
    apply (su7ExteriorBasis 4).repr.injective
    ext J
    simp [signedScalarBasis, Finsupp.single_apply]
    split_ifs <;> first
      | (linear_combination traceA + traceW)
      | (linear_combination -traceA - traceW)
      | (linear_combination traceA)
      | (linear_combination -traceA)
      | ring
  · -- channel 1, colour 2
    erw [colour_slot data 1 2 0 0 (by decide), Fin.sum_univ_three]
    erw [wedge_self' 1 2 0 (Sum.inl 0) (by decide),
      wedge_repeat' 1 2 0 1 (Sum.inl 1) (by decide) (by decide),
      wedge_move_swap 1 2 0 (Sum.inl 2) 1 0 (fun i => by fin_cases i <;> decide)]
    simp only [smul_zero, add_zero]
    erw [colour_slot data 1 2 1 1 (by decide), Fin.sum_univ_three]
    erw [wedge_repeat' 1 2 1 0 (Sum.inl 0) (by decide) (by decide),
      wedge_self' 1 2 1 (Sum.inl 1) (by decide),
      wedge_move_id 1 2 1 (Sum.inl 2) 1 1 (fun i => by fin_cases i <;> decide)]
    simp only [smul_zero, zero_add]
    erw [hyper_slot data 1 2 2 hyperPlusIndex (data.2.2.1) (by decide)
        (LowEnergy.MatterSpace.p286_fundamental_hyper data),
      hyper_slot data 1 2 3 hyperMinusIndex (-(data.2.2.1)) (by decide)
        (p286_fundamental_hyper_minus data)]
    erw [Fin.sum_univ_three]
    apply (su7ExteriorBasis 4).repr.injective
    ext J
    simp [signedScalarBasis, Finsupp.single_apply]
    split_ifs <;> first
      | (linear_combination traceA + traceW)
      | (linear_combination -traceA - traceW)
      | (linear_combination traceA)
      | (linear_combination -traceA)
      | ring

