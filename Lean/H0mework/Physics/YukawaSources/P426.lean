import H0mework.Physics.CouplingSources.P276
import H0mework.Physics.YukawaSources.P425

/-!
# Proposition 426: parameter vectors split into matrix Yukawa data plus complement

P425 proves the finite slot-level decomposition

`StandardModelParameter ≃ (generation × Yukawa-sector) ⊕ non-Yukawa-10`.

This file lifts that result from slots to actual 19-slot parameter vectors.
Every `ParameterVector K` is equivalent to:

* a `3 × 3` Yukawa matrix subvector; and
* a ten-slot non-Yukawa complement subvector.

It also transports the P274/P276 running-sigma residual-power law from named
Yukawa slots to matrix subvector coordinates.

Boundary: this is still coordinate algebra.  It does not construct the
physical RG/threshold producer that fills those coordinates.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Parameter-vector component carriers -/

/-- A `3 × 3` Yukawa matrix of values over `K`. -/
abbrev YukawaMatrixSubvector (K : Type*) :=
  StandardModelFermionGeneration -> YukawaInteractionSector -> K

/-- The ten-slot complement of the Yukawa matrix over `K`. -/
abbrev NonYukawaSubvector (K : Type*) :=
  NonYukawaStandardModelParameter -> K

/-- Project a 19-slot parameter vector to its `3 × 3` Yukawa matrix. -/
def parameterVectorToYukawaMatrix {K : Type*}
    (p : ParameterVector K) : YukawaMatrixSubvector K :=
  fun g s => p (yukawaMatrixSlot g s)

/-- Project a 19-slot parameter vector to its ten-slot non-Yukawa complement. -/
def parameterVectorToNonYukawaComplement {K : Type*}
    (p : ParameterVector K) : NonYukawaSubvector K :=
  fun n => p (nonYukawaSlot n)

/-- Rebuild a 19-slot parameter vector from a Yukawa matrix and a non-Yukawa
complement. -/
def parameterVectorFromComponents {K : Type*}
    (Y : YukawaMatrixSubvector K) (N : NonYukawaSubvector K) :
    ParameterVector K :=
  fun slot =>
    match standardModelParameterCoordinates slot with
    | .inl p => Y p.1 p.2
    | .inr n => N n

/-- THEOREM 1: reconstructing from a vector's own components recovers the
original 19-slot vector. -/
theorem parameterVectorFromComponents_of_projections {K : Type*}
    (p : ParameterVector K) :
    parameterVectorFromComponents
      (parameterVectorToYukawaMatrix p)
      (parameterVectorToNonYukawaComplement p) = p := by
  funext slot
  cases slot <;> rfl

/-- THEOREM 2: projecting a reconstructed vector recovers the supplied
Yukawa matrix. -/
theorem parameterVectorToYukawaMatrix_fromComponents {K : Type*}
    (Y : YukawaMatrixSubvector K) (N : NonYukawaSubvector K) :
    parameterVectorToYukawaMatrix
      (parameterVectorFromComponents Y N) = Y := by
  funext g s
  cases g <;> cases s <;> rfl

/-- THEOREM 3: projecting a reconstructed vector recovers the supplied
non-Yukawa complement. -/
theorem parameterVectorToNonYukawaComplement_fromComponents {K : Type*}
    (Y : YukawaMatrixSubvector K) (N : NonYukawaSubvector K) :
    parameterVectorToNonYukawaComplement
      (parameterVectorFromComponents Y N) = N := by
  funext n
  cases n <;> rfl

/-- THEOREM 4: a 19-slot parameter vector is exactly a pair consisting of a
`3 × 3` Yukawa matrix and a ten-slot non-Yukawa complement. -/
def parameterVectorComponentsEquiv (K : Type*) :
    ParameterVector K ≃ YukawaMatrixSubvector K × NonYukawaSubvector K where
  toFun p :=
    (parameterVectorToYukawaMatrix p,
      parameterVectorToNonYukawaComplement p)
  invFun c := parameterVectorFromComponents c.1 c.2
  left_inv := parameterVectorFromComponents_of_projections
  right_inv := by
    intro c
    rcases c with ⟨Y, N⟩
    apply Prod.ext
    · exact parameterVectorToYukawaMatrix_fromComponents Y N
    · exact parameterVectorToNonYukawaComplement_fromComponents Y N

/-- THEOREM 5: the generated 19-slot vector is reconstructed exactly from
its generated matrix-Yukawa and non-Yukawa components. -/
theorem generated_parameterVector_reconstructs_from_components
    {Seed Scale Index A K CKMCarrier : Type*} [AddCommGroup A]
    (C : StandardModelConstraintSynthesisCertificate
      Seed Scale Index A K CKMCarrier)
    (seed : Seed) :
    parameterVectorFromComponents
      (parameterVectorToYukawaMatrix (C.generated seed))
      (parameterVectorToNonYukawaComplement (C.generated seed)) =
        C.generated seed :=
  parameterVectorFromComponents_of_projections (C.generated seed)

/-! ## Running-sigma law as a matrix subvector law -/

namespace RunningSigmaStandardModelCertificate

variable {Seed Scale Index A K CKMCarrier : Type*}
variable [AddCommGroup A] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- THEOREM 6: P274's generated Yukawa law is a pointwise law for the
generated `3 × 3` matrix subvector. -/
theorem generated_yukawaMatrixSubvector_residual_power_running_sigma
    (C : RunningSigmaStandardModelCertificate
      Seed Scale Index A K CKMCarrier)
    (seed : Seed)
    (g : StandardModelFermionGeneration) (s : YukawaInteractionSector) :
    parameterVectorToYukawaMatrix (C.pinned.base.generated seed) g s =
      C.pinned.yukawaAmplitude (yukawaMatrixParameter g s) *
        (((1 : K) -
            C.sigma (C.yukawaScale seed (yukawaMatrixParameter g s))) ^
          C.pinned.yukawaExponent seed (yukawaMatrixParameter g s)) := by
  exact C.generated_yukawaMatrix_residual_power_running_sigma seed g s

end RunningSigmaStandardModelCertificate

/-! ## Zero-free certificate in matrix coordinates -/

namespace ZeroContinuousFreeStandardModelCertificate

variable {Index A K CKMCarrier : Type*}
variable [AddCommGroup A] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- THEOREM 7: any accepted solution has the same matrix-Yukawa subvector as
the selected generated solution. -/
theorem accepted_yukawaMatrixSubvector_eq_selected
    (C : ZeroContinuousFreeStandardModelCertificate Index A K CKMCarrier)
    (p : ParameterVector K)
    (hp : C.running.pinned.base.constraints p) :
    parameterVectorToYukawaMatrix p =
      parameterVectorToYukawaMatrix
        (C.running.pinned.base.generated C.selectedSeed) := by
  rw [C.accepted_solution_eq_selected_generated p hp]

/-- THEOREM 8: any accepted solution has the same non-Yukawa complement as
the selected generated solution. -/
theorem accepted_nonYukawaSubvector_eq_selected
    (C : ZeroContinuousFreeStandardModelCertificate Index A K CKMCarrier)
    (p : ParameterVector K)
    (hp : C.running.pinned.base.constraints p) :
    parameterVectorToNonYukawaComplement p =
      parameterVectorToNonYukawaComplement
        (C.running.pinned.base.generated C.selectedSeed) := by
  rw [C.accepted_solution_eq_selected_generated p hp]

/-- THEOREM 9: the zero-continuous-free certificate in component coordinates:
accepted vectors have exactly the selected matrix subvector and exactly the
selected non-Yukawa complement. -/
theorem accepted_components_eq_selected
    (C : ZeroContinuousFreeStandardModelCertificate Index A K CKMCarrier)
    (p : ParameterVector K)
    (hp : C.running.pinned.base.constraints p) :
    (parameterVectorComponentsEquiv K p) =
      (parameterVectorComponentsEquiv K
        (C.running.pinned.base.generated C.selectedSeed)) := by
  rw [C.accepted_solution_eq_selected_generated p hp]

/-- THEOREM 10: P276's accepted Yukawa finite-iterate law, read directly at a
matrix cell and its discrete scale label. -/
theorem accepted_yukawaMatrix_eq_zeroTarget_relaxation_iterate_discrete_scale
    (C : ZeroContinuousFreeStandardModelCertificate Index A K CKMCarrier)
    (p : ParameterVector K)
    (hp : C.running.pinned.base.constraints p)
    (g : StandardModelFermionGeneration) (s : YukawaInteractionSector) :
    p (yukawaMatrixSlot g s) =
      (fun x : K =>
        AffineRelaxation.relaxModule
          (0 : K)
          (C.running.sigma
            (StandardModelScaleCode.yukawa (yukawaMatrixParameter g s)))
          x)^[C.running.pinned.yukawaExponent
              C.selectedSeed (yukawaMatrixParameter g s)]
        (C.running.pinned.yukawaAmplitude (yukawaMatrixParameter g s)) := by
  simpa [yukawaMatrixSlot] using
    C.accepted_yukawa_eq_zeroTarget_relaxation_iterate_discrete_scale p hp
      (yukawaMatrixParameter g s)

/-- THEOREM 11: P276's accepted Yukawa effective-rate law, read directly at a
matrix cell and its discrete scale label. -/
theorem accepted_yukawaMatrix_eq_zeroTarget_effective_relaxation_discrete_scale
    (C : ZeroContinuousFreeStandardModelCertificate Index A K CKMCarrier)
    (p : ParameterVector K)
    (hp : C.running.pinned.base.constraints p)
    (g : StandardModelFermionGeneration) (s : YukawaInteractionSector) :
    p (yukawaMatrixSlot g s) =
      AffineRelaxation.relaxModule
        (0 : K)
        (1 -
          (1 -
            C.running.sigma
              (StandardModelScaleCode.yukawa (yukawaMatrixParameter g s))) ^
            C.running.pinned.yukawaExponent
              C.selectedSeed (yukawaMatrixParameter g s))
        (C.running.pinned.yukawaAmplitude (yukawaMatrixParameter g s)) := by
  simpa [yukawaMatrixSlot] using
    C.accepted_yukawa_eq_zeroTarget_effective_relaxation_discrete_scale p hp
      (yukawaMatrixParameter g s)

end ZeroContinuousFreeStandardModelCertificate

end StandardModelConstraint
end SaturationMonoid
