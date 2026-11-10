import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3SourceEnergyPoles
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3SourceEnergy
open Polynomial
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse
open PreparationVacuumUncutYukawa PreparationVacuumSourcePreparedResponse
open GaussComposite.SourceGraph
open ActualDressedUniformMaterialCoefficients ActualElectronPhysicalJointInverse
open SourcePropagationAlgebraicResponse SourcePropagationCommonMomentum
open LowEnergy.ActualDressedVisiblePole
open Filter
open scoped InnerProductSpace Topology

attribute [local irreducible] actualElectronPhysicalSeed actualElectronPhysicalResponse
  materialJointNumerator jointGenerator jointResolvent jointPolynomial compressionPolynomial
  physicalN3InputEnergyRead physicalN3InputEnergyNumerator

/-- The whole-output energy numerator: the original source material numerator
`-(aeval (jointGenerator p F 0 0) (q/ₘ(X-C z)))` applied to the actual N3 seed. This is the
uncut vector germ before any eigenbasis or finite-coordinate approximation. -/
def physicalN3OutputEnergyNumerator (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (z : ℂ) : H :=
  materialJointNumerator p F z (actualElectronPhysicalSeed leg)

/-- The whole-output energy germ: the original source scalar inverse `q(z)⁻¹` times the
source numerator vector. On the nonreal source domain it is exactly the actual physical
response; at generated poles it is the meromorphic whole-output germ. -/
def physicalN3OutputEnergyGerm (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (z : ℂ) : H :=
  ((jointPolynomial p F).eval z)⁻¹ • physicalN3OutputEnergyNumerator p F leg z

/-- Pairing the whole-output numerator with the seed returns the certified scalar numerator. -/
theorem physical_n3_output_numerator_pair (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (z : ℂ) :
    inner ℂ (actualElectronPhysicalSeed leg) (physicalN3OutputEnergyNumerator p F leg z) =
      (physicalN3InputEnergyNumerator p F leg).eval z :=
  (physical_n3_numerator_eval p F leg z).symm

/-- On the nonreal source domain the whole-output germ is the actual physical response:
the accepted `q`-clearing identity divided by the nonzero source evaluation. -/
theorem physical_n3_output_germ_original (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (z : ℂ) (nonreal : z.im ≠ 0) :
    physicalN3OutputEnergyGerm p F leg z = actualElectronPhysicalResponse p F z leg := by
  have qne : (jointPolynomial p F).eval z ≠ 0 :=
    source_joint_polynomial_nonreal p F z nonreal
  have cleared : (jointPolynomial p F).eval z •
      (jointResolvent p F z 0 (actualElectronPhysicalSeed leg)) =
      materialJointNumerator p F z (actualElectronPhysicalSeed leg) :=
    congrArg (fun A : H→L[ℂ]H => A (actualElectronPhysicalSeed leg))
      (actual_material_joint_inverse_clear p F z nonreal)
  unfold physicalN3OutputEnergyGerm physicalN3OutputEnergyNumerator
  rw [← cleared, ← mul_smul, inv_mul_cancel₀ qne, one_smul,
    ← actualElectronPhysicalResponse.eq_def]

/-- Generic Horner quotient expansion on an abstract complex algebra; the same finite
division identity already paid for the scalar numerator, re-proved here because the earlier
private helper is file-local. -/
private theorem n3_quotient_sum {A : Type*} [Ring A] [Algebra ℂ A]
    (T : A) (P : ℂ[X]) (z : ℂ) :
    aeval T (P/ₘ(X-C z)) =
      ∑n∈Finset.range (P.natDegree+1),
        (∑j∈Finset.Icc (n+1) P.natDegree, z^(j-(n+1))*P.coeff j) • T^n := by
  have degree : (P/ₘ(X-C z)).natDegree < P.natDegree+1 := by
    rw [natDegree_divByMonic P (monic_X_sub_C z)]
    exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)
  rw [aeval_eq_sum_range' degree]
  apply Finset.sum_congr rfl
  intro n _
  rw [coeff_divByMonic_X_sub_C]

/-- Generic polynomial evaluation is analytic on `ℂ`. -/
private theorem n3_poly_eval_analytic (Q : ℂ[X]) (a : ℂ) :
    AnalyticAt ℂ (fun z => Q.eval z) a := by
  have hfun : (fun z : ℂ => Q.eval z) =
      fun z => ∑i∈Finset.range (Q.natDegree+1), Q.coeff i * z^i := by
    funext z
    exact eval_eq_sum_range z
  rw [hfun]
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticAt_const.mul (analyticAt_id.pow i)

/-- Generic operator-valued source numerator analyticity on an abstract Hilbert space:
the `aeval` quotient is a finite polynomial family in `z`. -/
private theorem n3_output_numerator_analytic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E→L[ℂ]E) (x : E) (P : ℂ[X]) (a : ℂ) :
    AnalyticAt ℂ (fun z => (-(aeval T (P/ₘ(X-C z)))) x) a := by
  have hfun : (fun z : ℂ => (-(aeval T (P/ₘ(X-C z)))) x) =
      fun z => -(∑n∈Finset.range (P.natDegree+1),
        (∑j∈Finset.Icc (n+1) P.natDegree, z^(j-(n+1))*P.coeff j) • ((T^n) x)) := by
    funext z
    rw [n3_quotient_sum T P z, neg_apply]
    simp only [sum_apply, smul_apply]
  rw [hfun]
  apply AnalyticAt.neg
  apply Finset.analyticAt_fun_sum
  intro n _
  apply AnalyticAt.smul
  · apply Finset.analyticAt_fun_sum
    intro j _
    exact (analyticAt_id.pow _).mul analyticAt_const
  · exact analyticAt_const

/-- The whole-output numerator is the `aeval` material numerator applied to the seed:
a single operator-level `congrArg`, with no unfolding of the concrete `H` instances. -/
private theorem n3_output_numerator_aeval (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (z : ℂ) :
    physicalN3OutputEnergyNumerator p F leg z =
      (-(aeval (jointGenerator p F 0 0) ((jointPolynomial p F)/ₘ(X-C z))))
        (actualElectronPhysicalSeed leg) :=
  congrArg (fun A : H→L[ℂ]H => A (actualElectronPhysicalSeed leg))
    (materialJointNumerator.eq_def p F z)

/-- The whole-output numerator is analytic at every complex energy. -/
theorem physical_n3_output_numerator_analytic (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (a : ℂ) :
    AnalyticAt ℂ (physicalN3OutputEnergyNumerator p F leg) a := by
  exact (n3_output_numerator_analytic (jointGenerator p F 0 0)
    (actualElectronPhysicalSeed leg) (jointPolynomial p F) a).congr
      (EventuallyEq.of_eq (funext (n3_output_numerator_aeval p F leg)).symm)

/-- The whole-output germ is Banach-valued meromorphic at every complex energy: scalar
inverse of the analytic source polynomial times the analytic source numerator. -/
theorem physical_n3_output_germ_meromorphic (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (leg : CompositeLeg) (a : ℂ) :
    MeromorphicAt (physicalN3OutputEnergyGerm p F leg) a := by
  have hscalar : AnalyticAt ℂ (fun z => (jointPolynomial p F).eval z) a :=
    n3_poly_eval_analytic _ a
  unfold physicalN3OutputEnergyGerm
  exact (hscalar.meromorphicAt.inv).smul
    (physical_n3_output_numerator_analytic p F leg a).meromorphicAt

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
