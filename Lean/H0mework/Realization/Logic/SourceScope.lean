import H0mework.Foundation.Relations.ScalarDifferentialResidual
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Logic.Equiv.Basic

/-!
The model scope is the existing source coimage, never the ambient codomain.
Quantifiers are the existing image/preimage/kernel-image adjoints. Their
Type-valued fibres retain every source representative; evidence transport is
an eliminator and supplies no truth or chosen representative.
-/

set_option autoImplicit false

universe r c d w c' d'

namespace SaturationMonoid.SourceOperationLogic

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedScalarDifferentialResidual

variable {R : Type r} [CommRing R]
variable {C : Type c} [AddCommGroup C] [Module R C]
variable {D : Type d} [AddCommGroup D] [Module R D]
variable (e : C →ₗ[R] D)

abbrev Scope := ResidualCarrier e

abbrev q : C →ₗ[R] Scope e := canonicalResidual e

theorem q_surjective : Function.Surjective (q e) :=
  (LinearMap.ker e).mkQ_surjective

noncomputable abbrev scopeEquivRange : Scope e ≃ₗ[R] LinearMap.range e :=
  residualEquivRange e

abbrev Fibre (point : Scope e) := { source : C // q e source = point }

def sourceWitness (source : C) : Fibre e (q e source) :=
  ⟨source, rfl⟩

/-- The whole fibre inventory reconstructs the original source in `Type`. -/
def fibreDecomposition : C ≃ Σ point : Scope e, Fibre e point :=
  (Equiv.sigmaFiberEquiv (q e)).symm

theorem q_eq_iff (left right : C) :
    q e left = q e right ↔ left - right ∈ LinearMap.ker e := by
  rw [LinearMap.mem_ker, ← canonicalResidual_eq_zero_iff e, map_sub, sub_eq_zero]

abbrev existsAlong : Set C → Set (Scope e) := Set.image (q e)

abbrev pullback : Set (Scope e) → Set C := Set.preimage (q e)

abbrev forallAlong : Set C → Set (Scope e) := Set.kernImage (q e)

theorem exists_pullback : GaloisConnection (existsAlong e) (pullback e) :=
  Set.image_preimage

theorem pullback_forall : GaloisConnection (pullback e) (forallAlong e) :=
  Set.preimage_kernImage

abbrev ExistsEvidence (evidenceAt : C → Type w) (point : Scope e) :=
  Σ source : Fibre e point, evidenceAt source.val

abbrev ForallEvidence (evidenceAt : C → Type w) (point : Scope e) :=
  (source : Fibre e point) → evidenceAt source.val

/-- Introduction retains the supplied source evidence and its exact source. -/
def retainEvidence {evidenceAt : C → Type w} {source : C}
    (evidence : evidenceAt source) : ExistsEvidence e evidenceAt (q e source) :=
  ⟨sourceWitness e source, evidence⟩

/-- Existential evidence over all model fibres eliminates to source evidence. -/
def existsEvidenceElim (evidenceAt : C → Type w) :
    (Σ point : Scope e, ExistsEvidence e evidenceAt point) ≃
      Σ source : C, evidenceAt source :=
  (Equiv.sigmaAssoc (fun (_point : Scope e) (source : Fibre e _point) =>
    evidenceAt source.val)).symm.trans
    (Equiv.sigmaCongrLeft (Equiv.sigmaFiberEquiv (q e)))

/-- A dependent consumer covers each whole fibre; no section of `q` is chosen. -/
def forallEvidenceElim (evidenceAt : C → Type w) :
    ((point : Scope e) → ForallEvidence e evidenceAt point) ≃
      ((source : C) → evidenceAt source) :=
  (Equiv.piCurry (fun (_point : Scope e) (source : Fibre e _point) =>
    evidenceAt source.val)).symm.trans
    (Equiv.piCongrSigmaFiber (f := q e) (fun _ => Equiv.refl _))

@[simp] theorem forallEvidenceElim_apply (evidenceAt : C → Type w)
    (evidence : (point : Scope e) → ForallEvidence e evidenceAt point)
    (source : C) :
    forallEvidenceElim e evidenceAt evidence source =
      evidence (q e source) (sourceWitness e source) := rfl

section Substitution

variable {C' : Type c'} [AddCommGroup C'] [Module R C']
variable {D' : Type d'} [AddCommGroup D'] [Module R D']
variable {e' : C' →ₗ[R] D'}

/-- Existing differential squares transport substitution on the exact coimages.
Identity and composition use `Morphism.id/comp`, `inducedResidualMap_id/comp`,
and `GaloisConnection.id/compose`; no parallel substitution law is introduced. -/
theorem pullback_substitution (substitution : Morphism e e')
    (predicate : Set (Scope e')) :
    Set.preimage substitution.sourceMap (pullback e' predicate) =
      pullback e (Set.preimage (inducedResidualMap substitution) predicate) := rfl

end Substitution

end SaturationMonoid.SourceOperationLogic
