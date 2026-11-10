import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualElectronPhysicalDomainAndContact
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUniformMaterialInverse
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationJointSourceAnnihilator

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
open scoped InnerProductSpace

/-- The actual N3 physical inverse read at a fixed source preparation frame: the original
seed paired with the actual joint resolvent output at energy `z`. -/
def physicalN3InputEnergyRead (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (z : ℂ) : ℂ :=
  inner ℂ (actualElectronPhysicalSeed leg) (actualElectronPhysicalResponse p F z leg)

/-- The source-generated scalar numerator of the same read: the original material numerator
`-(q/(X-z))` evaluated against the actual seed and packaged back as a finite polynomial. -/
def physicalN3InputEnergyNumerator (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) : ℂ[X] :=
  -(∑n∈Finset.range ((jointPolynomial p F).natDegree+1),
    ∑j∈Finset.Icc (n+1) (jointPolynomial p F).natDegree,
      C ((jointPolynomial p F).coeff j*
        inner ℂ (actualElectronPhysicalSeed leg)
          (((jointGenerator p F 0 0)^n) (actualElectronPhysicalSeed leg)))*X^(j-(n+1)))

attribute [local irreducible] actualElectronPhysicalSeed actualElectronPhysicalResponse
  materialJointNumerator jointGenerator jointResolvent jointPolynomial compressionPolynomial

/-- Generic Horner quotient expansion on an abstract complex algebra; identical shape to the
already paid meromorphic numerator sum. -/
private theorem n3_numerator_sum {A : Type*} [Ring A] [Algebra ℂ A]
    (T : A) (P : ℂ[X]) (lambda : ℂ) :
    aeval T (P/ₘ(X-C lambda))=
      ∑n∈Finset.range (P.natDegree+1),
        (∑j∈Finset.Icc (n+1) P.natDegree,lambda^(j-(n+1))*P.coeff j) • T^n:=by
  have degree : (P/ₘ(X-C lambda)).natDegree<P.natDegree+1:=by
    rw [natDegree_divByMonic P (monic_X_sub_C lambda)]
    exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)
  rw [aeval_eq_sum_range' degree]
  apply Finset.sum_congr rfl
  intro n _
  rw [coeff_divByMonic_X_sub_C]

/-- Pairing the operator Horner quotient with a fixed vector on an abstract Hilbert space. -/
private theorem n3_pair_numerator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E→L[ℂ]E) (x : E) (P : ℂ[X]) (lambda : ℂ) :
    inner ℂ x ((aeval T (P/ₘ(X-C lambda))) x)=
      ∑n∈Finset.range (P.natDegree+1),
        (∑j∈Finset.Icc (n+1) P.natDegree,lambda^(j-(n+1))*P.coeff j)*
          inner ℂ x ((T^n) x):=by
  rw [n3_numerator_sum]
  simp only [sum_apply,smul_apply,inner_sum,inner_smul_right]

/-- Negating an operator before pairing pulls out to a scalar sign, on an abstract Hilbert
space so no concrete `H` instance search is needed. -/
private theorem n3_pair_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : E→L[ℂ]E) (x : E) :
    inner ℂ x ((-S) x)= -(inner ℂ x (S x)):=by
  rw [neg_apply,inner_neg_right]

/-- Generic evaluation of the finite Horner numerator: a polynomial identity on an abstract
coefficient family. -/
private theorem n3_eval_generic (Q : ℂ[X]) (c : ℕ→ℂ) (z : ℂ) :
    eval z (-(∑n∈Finset.range (Q.natDegree+1),∑j∈Finset.Icc (n+1) Q.natDegree,
        C (Q.coeff j*c n)*X^(j-(n+1))))=
      -(∑n∈Finset.range (Q.natDegree+1),
        (∑j∈Finset.Icc (n+1) Q.natDegree,z^(j-(n+1))*Q.coeff j)*c n):=by
  simp only [eval_neg,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The finite scalar numerator is exactly the seed pairing of the source material numerator. -/
theorem physical_n3_numerator_eval (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (z : ℂ) :
    (physicalN3InputEnergyNumerator p F leg).eval z=
      inner ℂ (actualElectronPhysicalSeed leg)
        ((materialJointNumerator p F z) (actualElectronPhysicalSeed leg)):=by
  have eq := materialJointNumerator.eq_def p F z
  have pair := n3_pair_numerator (jointGenerator p F 0 0) (actualElectronPhysicalSeed leg)
      (jointPolynomial p F) z
  rw [eq,n3_pair_neg,pair]
  exact n3_eval_generic _ _ _

/-- Clearing the actual physical inverse at a nonreal source energy returns the finite numerator. -/
theorem physical_n3_read_scaled (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (z : ℂ) (nonreal : z.im≠0) :
    (jointPolynomial p F).eval z*physicalN3InputEnergyRead p F leg z=
      (physicalN3InputEnergyNumerator p F leg).eval z:=by
  rw [physical_n3_numerator_eval]
  show (jointPolynomial p F).eval z*
      inner ℂ (actualElectronPhysicalSeed leg) (actualElectronPhysicalResponse p F z leg)=
    inner ℂ (actualElectronPhysicalSeed leg)
      ((materialJointNumerator p F z) (actualElectronPhysicalSeed leg))
  rw [actualElectronPhysicalResponse.eq_def]
  rw [←inner_smul_right,←smul_apply,actual_material_joint_inverse_clear p F z nonreal]

/-- The actual read is the original rational source read `P/q` on the nonreal domain. -/
theorem physical_n3_read_eq_eval (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) (z : ℂ) (nonreal : z.im≠0) :
    physicalN3InputEnergyRead p F leg z=
      (physicalN3InputEnergyNumerator p F leg).eval z/(jointPolynomial p F).eval z:=by
  rw [eq_div_iff (source_joint_polynomial_nonreal p F z nonreal),mul_comm]
  exact physical_n3_read_scaled p F leg z nonreal

/-- The original joint polynomial has positive degree because the source keeps its `X` factor. -/
theorem physical_n3_joint_degree_positive (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    0<(jointPolynomial p F).natDegree:=by
  have monic:=jointPolynomial_monic p F
  have zero : (jointPolynomial p F).eval 0=0:=by
    rw [jointPolynomial.eq_def,eval_pow,compressionPolynomial.eq_def,eval_mul,eval_X,
      mul_zero]
    exact zero_pow (by decide : (57:ℕ)≠0)
  have dvd : X∣jointPolynomial p F:=X_dvd_iff.mpr
    (by rw [coeff_zero_eq_eval_zero];exact zero)
  have le : X.natDegree≤(jointPolynomial p F).natDegree:=
    natDegree_le_of_dvd dvd monic.ne_zero
  rw [natDegree_X] at le
  exact le

/-- Generic top Horner coefficient on an abstract coefficient family; the only surviving
slot is `(n,j)=(0,d)`. -/
private theorem n3_horner_leading (Q : ℂ[X]) (c : ℕ→ℂ) (d : ℕ)
    (hd : Q.natDegree=d) (h0 : 0<d) :
    (∑n∈Finset.range (Q.natDegree+1),
      ∑j∈Finset.Icc (n+1) Q.natDegree,
        C (Q.coeff j*c n)*X^(j-(n+1))).coeff (Q.natDegree-1)=
      Q.leadingCoeff*c 0:=by
  have dpos : 0<Q.natDegree:=hd ▸ h0
  rw [finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · rw [finsetSum_coeff]
    rw [Finset.sum_eq_single Q.natDegree]
    · rw [C_mul_X_pow_eq_monomial,coeff_monomial,if_pos rfl]
      rfl
    · intro j hj jne
      rw [Finset.mem_Icc] at hj
      have noteq : j-(0+1)≠Q.natDegree-1:=by omega
      rw [C_mul_X_pow_eq_monomial,coeff_monomial,if_neg]
      intro h
      exact noteq (by rwa [Nat.zero_add] at h⊢)
    · intro outside
      exact absurd (Finset.mem_Icc.mpr ⟨dpos,le_refl Q.natDegree⟩) outside
  · intro n hn nne
    rw [Finset.mem_range] at hn
    rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Icc] at hj
    have noteq : j-(n+1)≠Q.natDegree-1:=by omega
    rw [C_mul_X_pow_eq_monomial,coeff_monomial,if_neg noteq]
  · intro outside
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos Q.natDegree)) outside

/-- Only the `(n,j)=(0,d)` Horner slot reaches the top coefficient; it carries the original
seed unit and monic leading coefficient. -/
theorem physical_n3_numerator_leading (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) :
    (physicalN3InputEnergyNumerator p F leg).coeff ((jointPolynomial p F).natDegree-1)= -1:=by
  have dpos :=physical_n3_joint_degree_positive p F
  have key : (physicalN3InputEnergyNumerator p F leg).coeff ((jointPolynomial p F).natDegree-1)=
      -((jointPolynomial p F).leadingCoeff*
        inner ℂ (actualElectronPhysicalSeed leg)
          (((jointGenerator p F 0 0)^0) (actualElectronPhysicalSeed leg))):=by
    exact congrArg Neg.neg
      (n3_horner_leading (jointPolynomial p F)
        (fun n=>inner ℂ (actualElectronPhysicalSeed leg)
          (((jointGenerator p F 0 0)^n) (actualElectronPhysicalSeed leg)))
        (jointPolynomial p F).natDegree rfl dpos)
  rw [key,(jointPolynomial_monic p F).leadingCoeff,one_mul,pow_zero,one_apply_eq_self,
    inner_self_eq_norm_sq_to_K,actual_electron_physical_seed_norm]
  norm_num

/-- The source numerator is nonzero: its `d-1` coefficient is `-1`. -/
theorem physical_n3_numerator_nonzero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) : physicalN3InputEnergyNumerator p F leg≠0:=by
  intro zero
  have leading:=physical_n3_numerator_leading p F leg
  rw [zero,coeff_zero] at leading
  norm_num at leading

/-- The source numerator degree is exactly `d-1`. -/
theorem physical_n3_numerator_degree (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) :
    (physicalN3InputEnergyNumerator p F leg).natDegree=(jointPolynomial p F).natDegree-1:=by
  apply le_antisymm
  · conv_lhs => unfold physicalN3InputEnergyNumerator
    rw [natDegree_neg]
    apply le_trans (natDegree_sum_le _ _)
    apply Finset.sup_le
    intro n _
    apply le_trans (natDegree_sum_le _ _)
    apply Finset.sup_le
    intro j hj
    rw [Finset.mem_Icc] at hj
    apply le_trans (natDegree_C_mul_X_pow_le _ _)
    omega
  · exact le_natDegree_of_ne_zero
      (by rw [physical_n3_numerator_leading];norm_num)

/-- Strict properness: the scalar numerator degree is strictly below the original `q` degree. -/
theorem physical_n3_numerator_strict (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (leg : CompositeLeg) :
    (physicalN3InputEnergyNumerator p F leg).natDegree<(jointPolynomial p F).natDegree:=by
  rw [physical_n3_numerator_degree]
  exact Nat.sub_one_lt_of_le (physical_n3_joint_degree_positive p F) (Nat.le_refl _)

end LowEnergy.GaussComposite.PhysicalN3SourceEnergy
