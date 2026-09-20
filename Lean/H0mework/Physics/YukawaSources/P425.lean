import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Physics.CouplingSources.P274
import H0mework.Physics.YukawaSources.P424

/-!
# Proposition 425: the 3x3 Yukawa matrix inside the 19-slot surface

P424 proves that the nine Yukawa rows are exactly a
`generation x interaction-sector` matrix.  P273/P274 still state the
Standard-Model-facing residual-power law on named Yukawa slots inside the
19-slot surface.

This file connects those layers:

* the 19-slot surface decomposes as the disjoint sum of the 3x3 Yukawa matrix
  and ten non-Yukawa slots;
* the matrix image is injective and disjoint from the non-Yukawa complement;
* P274's running-sigma residual-power theorem can be read directly at each
  matrix cell.

Boundary: this remains finite parameter bookkeeping.  It does not solve RG
equations, derive threshold corrections, or construct the physical geometry
producer.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Yukawa matrix slots in the 19-slot surface -/

/-- A matrix Yukawa cell, embedded into the 19 Standard Model slots. -/
def yukawaMatrixSlot
    (g : StandardModelFermionGeneration) (s : YukawaInteractionSector) :
    StandardModelParameter :=
  yukawaSlot (yukawaMatrixParameter g s)

/-- THEOREM 1: the matrix slot recovers the named Yukawa slot. -/
theorem yukawaMatrixSlot_eq_yukawaSlot
    (g : StandardModelFermionGeneration) (s : YukawaInteractionSector) :
    yukawaMatrixSlot g s = yukawaSlot (yukawaMatrixParameter g s) := by
  rfl

/-! ## The ten-slot non-Yukawa complement -/

/-- The ten Standard Model slots outside the Yukawa matrix:
three gauge couplings, two Higgs-potential parameters, theta_QCD, and four
CKM parameters. -/
inductive NonYukawaStandardModelParameter where
  | gauge_g1
  | gauge_g2
  | gauge_g3
  | higgs_muSq
  | higgs_lambda
  | qcd_theta
  | ckm_theta12
  | ckm_theta23
  | ckm_theta13
  | ckm_delta
  deriving DecidableEq, Repr, FintypeViaProxy

namespace NonYukawaStandardModelParameter

/-- THEOREM 2: there are ten non-Yukawa slots. -/
theorem card : Fintype.card NonYukawaStandardModelParameter = 10 := by
  decide

end NonYukawaStandardModelParameter

/-- Embed the ten-slot non-Yukawa complement into the 19-slot surface. -/
def nonYukawaSlot : NonYukawaStandardModelParameter -> StandardModelParameter
  | .gauge_g1 => .gauge_g1
  | .gauge_g2 => .gauge_g2
  | .gauge_g3 => .gauge_g3
  | .higgs_muSq => .higgs_muSq
  | .higgs_lambda => .higgs_lambda
  | .qcd_theta => .qcd_theta
  | .ckm_theta12 => .ckm_theta12
  | .ckm_theta23 => .ckm_theta23
  | .ckm_theta13 => .ckm_theta13
  | .ckm_delta => .ckm_delta

/-- THEOREM 3: the non-Yukawa complement has no duplicate slots. -/
theorem nonYukawaSlot_injective :
    Function.Injective nonYukawaSlot := by
  intro a b h
  cases a <;> cases b <;> simp [nonYukawaSlot] at h ⊢

/-! ## 19 = 9 + 10 as a disjoint finite surface -/

/-- The 19-slot surface as a disjoint sum of a 3x3 Yukawa matrix and the
ten-slot non-Yukawa complement. -/
def standardModelParameterDecomposition :
    Sum (StandardModelFermionGeneration × YukawaInteractionSector)
      NonYukawaStandardModelParameter ->
    StandardModelParameter
  | .inl p => yukawaMatrixSlot p.1 p.2
  | .inr n => nonYukawaSlot n

/-- Coordinates of a 19-slot parameter in the disjoint decomposition. -/
def standardModelParameterCoordinates :
    StandardModelParameter ->
    Sum (StandardModelFermionGeneration × YukawaInteractionSector)
      NonYukawaStandardModelParameter
  | .gauge_g1 => .inr .gauge_g1
  | .gauge_g2 => .inr .gauge_g2
  | .gauge_g3 => .inr .gauge_g3
  | .higgs_muSq => .inr .higgs_muSq
  | .higgs_lambda => .inr .higgs_lambda
  | .qcd_theta => .inr .qcd_theta
  | .yukawa_u => .inl (.first, .upLike)
  | .yukawa_c => .inl (.second, .upLike)
  | .yukawa_t => .inl (.third, .upLike)
  | .yukawa_d => .inl (.first, .downLike)
  | .yukawa_s => .inl (.second, .downLike)
  | .yukawa_b => .inl (.third, .downLike)
  | .yukawa_e => .inl (.first, .chargedLepton)
  | .yukawa_mu => .inl (.second, .chargedLepton)
  | .yukawa_tau => .inl (.third, .chargedLepton)
  | .ckm_theta12 => .inr .ckm_theta12
  | .ckm_theta23 => .inr .ckm_theta23
  | .ckm_theta13 => .inr .ckm_theta13
  | .ckm_delta => .inr .ckm_delta

/-- THEOREM 4: the 19 slots are exactly the disjoint sum of
`3 x 3` Yukawa matrix cells and ten non-Yukawa slots. -/
def standardModelParameterDecompositionEquiv :
    Sum (StandardModelFermionGeneration × YukawaInteractionSector)
      NonYukawaStandardModelParameter ≃
    StandardModelParameter where
  toFun := standardModelParameterDecomposition
  invFun := standardModelParameterCoordinates
  left_inv := by
    intro x
    cases x with
    | inl p =>
        rcases p with ⟨g, s⟩
        cases g <;> cases s <;> rfl
    | inr n =>
        cases n <;> rfl
  right_inv := by
    intro p
    cases p <;> rfl

instance : Fintype StandardModelParameter :=
  Fintype.ofEquiv
    (Sum (StandardModelFermionGeneration × YukawaInteractionSector)
      NonYukawaStandardModelParameter)
    standardModelParameterDecompositionEquiv

/-- THEOREM 5: the conventional Standard Model surface has exactly
nineteen slots. -/
theorem standardModelParameter_card :
    Fintype.card StandardModelParameter = 19 := by
  decide

/-- THEOREM 6: matrix Yukawa cells embed injectively into the 19-slot surface. -/
theorem yukawaMatrixSlot_injective :
    Function.Injective
      (fun p : StandardModelFermionGeneration × YukawaInteractionSector =>
        yukawaMatrixSlot p.1 p.2) := by
  intro p q h
  rcases p with ⟨g, s⟩
  rcases q with ⟨g', s'⟩
  cases g <;> cases s <;> cases g' <;> cases s' <;>
    simp [yukawaMatrixSlot, yukawaMatrixParameter, yukawaSlot] at h ⊢

/-- THEOREM 7: every named Yukawa slot is covered by a matrix cell inside
the 19-slot surface. -/
theorem yukawaMatrixSlot_surjective_on_yukawa :
    ∀ y : YukawaParameter,
      ∃ g s, yukawaMatrixSlot g s = yukawaSlot y := by
  intro y
  rcases yukawaMatrix_surjective y with ⟨p, hp⟩
  refine ⟨p.1, p.2, ?_⟩
  exact congrArg yukawaSlot hp

/-- THEOREM 8: the Yukawa matrix image and the non-Yukawa complement are
disjoint inside the 19-slot surface. -/
theorem yukawaMatrixSlot_ne_nonYukawaSlot
    (p : StandardModelFermionGeneration × YukawaInteractionSector)
    (n : NonYukawaStandardModelParameter) :
    yukawaMatrixSlot p.1 p.2 ≠ nonYukawaSlot n := by
  intro h
  rcases p with ⟨g, s⟩
  cases g <;> cases s <;> cases n <;>
    simp [yukawaMatrixSlot, yukawaMatrixParameter, yukawaSlot,
      nonYukawaSlot] at h

/-- THEOREM 9: no gauge-coupling slot lies in the Yukawa matrix image. -/
theorem yukawaMatrixSlot_ne_gaugeSlot
    (p : StandardModelFermionGeneration × YukawaInteractionSector)
    (gauge : GaugeCouplingParameter) :
    yukawaMatrixSlot p.1 p.2 ≠ gaugeSlot gauge := by
  rcases p with ⟨g, s⟩
  cases g <;> cases s <;> cases gauge <;>
    simp [yukawaMatrixSlot, yukawaMatrixParameter, yukawaSlot, gaugeSlot]

/-- THEOREM 10: no CKM slot lies in the Yukawa matrix image. -/
theorem yukawaMatrixSlot_ne_ckmSlot
    (p : StandardModelFermionGeneration × YukawaInteractionSector)
    (ckm : CKMParameter) :
    yukawaMatrixSlot p.1 p.2 ≠ ckmSlot ckm := by
  rcases p with ⟨g, s⟩
  cases g <;> cases s <;> cases ckm <;>
    simp [yukawaMatrixSlot, yukawaMatrixParameter, yukawaSlot, ckmSlot]

/-! ## Running-sigma law in matrix coordinates -/

namespace RunningSigmaStandardModelCertificate

variable {Seed Scale Index A K CKMCarrier : Type*}
variable [AddCommGroup A] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- THEOREM 11: P274's running-sigma residual-power law, expressed directly
at a `generation x interaction-sector` Yukawa matrix cell. -/
theorem generated_yukawaMatrix_residual_power_running_sigma
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (seed : Seed)
    (g : StandardModelFermionGeneration) (s : YukawaInteractionSector) :
    C.pinned.base.generated seed (yukawaMatrixSlot g s) =
      C.pinned.yukawaAmplitude (yukawaMatrixParameter g s) *
        (((1 : K) -
            C.sigma (C.yukawaScale seed (yukawaMatrixParameter g s))) ^
          C.pinned.yukawaExponent seed (yukawaMatrixParameter g s)) := by
  exact C.generated_yukawa_residual_power_running_sigma seed
    (yukawaMatrixParameter g s)

/-- THEOREM 12: every matrix cell uses the running sigma at that cell's
declared scale. -/
theorem yukawaMatrixSigma_is_runningSigma
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (seed : Seed)
    (g : StandardModelFermionGeneration) (s : YukawaInteractionSector) :
    C.pinned.yukawaSigma seed (yukawaMatrixParameter g s) =
      C.sigma (C.yukawaScale seed (yukawaMatrixParameter g s)) := by
  exact C.yukawaSigma_is_runningSigma seed (yukawaMatrixParameter g s)

end RunningSigmaStandardModelCertificate

end StandardModelConstraint
end SaturationMonoid
