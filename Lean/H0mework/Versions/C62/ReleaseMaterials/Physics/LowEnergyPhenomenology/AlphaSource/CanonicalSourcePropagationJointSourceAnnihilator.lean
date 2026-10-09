import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationCompressionPolynomial

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationAlgebraicResponse
open GaussCoreHilbert CanonicalGradedSpatialSource CanonicalPhysicalSpatial
open PreparationVacuumPhysicalHalfAxis PreparationVacuumJointFieldResponse
open NativeHistoryGrade (Label projection)
open scoped BigOperators
open Polynomial
abbrev Op:=H→L[ℂ] H
local instance : Fintype Label:=Fintype.ofFinite _
attribute [local irreducible] jointGenerator compression actualA compressionPolynomial

private def sourceTail (n : ℕ) (x : H) : Prop:=
  ∀g : Label,g.2.val<n→projection g x=0

private theorem tail_zero (n : ℕ) : sourceTail n 0:=by
  intro g _
  exact map_zero _

private theorem tail_add {n : ℕ} {x y : H} (hx : sourceTail n x) (hy : sourceTail n y) :
    sourceTail n (x+y):=by
  intro g hg
  rw [map_add,hx g hg,hy g hg,add_zero]

private theorem tail_sub {n : ℕ} {x y : H} (hx : sourceTail n x) (hy : sourceTail n y) :
    sourceTail n (x-y):=by
  intro g hg
  rw [map_sub,hx g hg,hy g hg,sub_self]

private theorem tail_smul (c : ℂ) {n : ℕ} {x : H} (hx : sourceTail n x) :
    sourceTail n (c • x):=by
  intro g hg
  rw [map_smul,hx g hg,smul_zero]

private theorem tail_sum {I : Type*} (s : Finset I) (f : I→H) (n : ℕ)
    (hf : ∀i∈s,sourceTail n (f i)) : sourceTail n (∑i∈s,f i):=by
  intro g hg
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i hi=>hf i hi g hg)

private theorem tail_mono {n m : ℕ} (hmn : m≤n) {x : H} (hx : sourceTail n x) :
    sourceTail m x:=by
  intro g hg
  exact hx g (lt_of_lt_of_le hg hmn)

private theorem tail_initial (x : H) : sourceTail 0 x:=by
  intro g hg
  omega

private theorem tail_terminal {x : H} (hx : sourceTail 57 x) : x=0:=by
  have all (g : Label) : projection g x=0:=hx g g.2.isLt
  have actual:=congrArg (fun T : Op=>T x) NativeHistoryGrade.projection_resolution
  simpa only [sum_apply,all,Finset.sum_const_zero,one_apply_eq_self] using actual.symm

private theorem compression_tail (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (x : H) (hx : sourceTail n x) : sourceTail n (compression p F x):=by
  intro g hg
  have actual:=congrArg (fun T : Op=>T x) (compression_blocks p F g).eq
  change projection g (compression p F x)=compression p F (projection g x) at actual
  rw [actual,hx g hg,map_zero]

private theorem raising_block_zero (A : Op)
    (raises : GaussYukawaGrade.grade*A=A*GaussYukawaGrade.grade+A)
    (g h : Label) (below : h.2.val<g.2.val+1) (x : H) :
    projection h (A (projection g x))=0:=by
  have left:=congrArg (fun T : Op=>T (A (projection g x)))
    (GaussYukawaInteraction.source_grade_left h)
  have right:=congrArg (fun T : Op=>T x) (GaussYukawaInteraction.source_grade_right g)
  change projection h (GaussYukawaGrade.grade (A (projection g x)))=
    (h.2.val:ℂ) • projection h (A (projection g x)) at left
  change GaussYukawaGrade.grade (projection g x)=(g.2.val:ℂ) • projection g x at right
  have actual:=congrArg (fun T : Op=>projection h (T (projection g x))) raises
  simp only [mul_apply_eq_comp,add_apply,map_add] at actual
  rw [left,right,map_smul,map_smul] at actual
  have eigen : (h.2.val:ℂ) • projection h (A (projection g x))=
      ((g.2.val+1:ℕ):ℂ) • projection h (A (projection g x)):=by
    simpa only [Nat.cast_add,Nat.cast_one,add_smul,one_smul] using actual
  have zero : ((h.2.val:ℂ)-((g.2.val+1:ℕ):ℂ)) • projection h (A (projection g x))=0:=by
    rw [sub_smul,eigen,sub_self]
  have nonzero : (h.2.val:ℂ)-((g.2.val+1:ℕ):ℂ)≠0:=by
    apply sub_ne_zero.mpr
    exact_mod_cast (Nat.ne_of_lt below)
  exact (smul_eq_zero.mp zero).resolve_left nonzero

private theorem raising_tail (A : Op)
    (raises : GaussYukawaGrade.grade*A=A*GaussYukawaGrade.grade+A)
    (n : ℕ) (x : H) (hx : sourceTail n x) : sourceTail (n+1) (A x):=by
  intro h hh
  have resolution : ∑g : Label,projection g x=x:=by
    simpa only [sum_apply,one_apply_eq_self] using
      congrArg (fun T : Op=>T x) NativeHistoryGrade.projection_resolution
  rw [←resolution,map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro g _
  by_cases low : g.2.val<n
  · rw [hx g low,map_zero,map_zero]
  · exact raising_block_zero A raises g h (by omega) x

private theorem generator_tail (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (x : H) (hx : sourceTail n x) : sourceTail n (jointGenerator p F 0 0 x):=by
  rw [actualGenerator_source]
  change sourceTail n (compression p F x+actualA p F x)
  exact tail_add (compression_tail p F n x hx)
    (tail_mono (Nat.le_succ n) (raising_tail (actualA p F) (actualA_raises p F) n x hx))

private theorem compression_pow_tail (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (r n : ℕ) (x : H) (hx : sourceTail n x) : sourceTail n (((compression p F)^r) x):=by
  induction r with
  | zero=>simpa only [pow_zero,one_apply_eq_self] using hx
  | succ r ih=>
    rw [pow_succ',mul_apply_eq_comp]
    exact compression_tail p F n _ ih

private theorem generator_pow_tail (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (r n : ℕ) (x : H) (hx : sourceTail n x) : sourceTail n (((jointGenerator p F 0 0)^r) x):=by
  induction r with
  | zero=>simpa only [pow_zero,one_apply_eq_self] using hx
  | succ r ih=>
    rw [pow_succ',mul_apply_eq_comp]
    exact generator_tail p F n _ ih

private theorem linear_power_difference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (C A : E→L[ℂ] E) (r : ℕ) (x : E) :
    (((C+A)^(r+1)) x-((C^(r+1)) x))=
      (C+A) (((C+A)^r) x-(C^r) x)+A ((C^r) x):=by
  simp only [pow_succ',mul_apply_eq_comp,map_sub,add_apply]
  abel

private theorem difference_pow_tail (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (r n : ℕ) (x : H) (hx : sourceTail n x) :
    sourceTail (n+1) ((((jointGenerator p F 0 0)^r) x)-(((compression p F)^r) x)):=by
  induction r with
  | zero=>simpa only [pow_zero,one_apply_eq_self,sub_self] using tail_zero (n+1)
  | succ r ih=>
    have equation:=linear_power_difference (compression p F) (actualA p F) r x
    have source : jointGenerator p F 0 0=compression p F+actualA p F:=actualGenerator_source p F
    rw [←source] at equation
    rw [equation]
    exact tail_add (generator_tail p F (n+1) _ ih)
      (raising_tail (actualA p F) (actualA_raises p F) n _ (compression_pow_tail p F r n x hx))

private theorem polynomial_difference_tail (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (P : ℂ[X]) (n : ℕ) (x : H) (hx : sourceTail n x) :
    sourceTail (n+1) (aeval (jointGenerator p F 0 0) P x-aeval (compression p F) P x):=by
  rw [aeval_eq_sum_range,aeval_eq_sum_range]
  simp only [sum_apply,smul_apply,←Finset.sum_sub_distrib,←smul_sub]
  apply tail_sum
  intro r _
  exact tail_smul _ (difference_pow_tail p F r n x hx)

private theorem actual_polynomial_tail (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (x : H) (hx : sourceTail n x) :
    sourceTail (n+1) (aeval (jointGenerator p F 0 0) (compressionPolynomial p F) x):=by
  have source:=polynomial_difference_tail p F (compressionPolynomial p F) n x hx
  rw [actualCompression_annihilated,zero_apply,sub_zero] at source
  exact source

private theorem actual_polynomial_pow_tail (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (r : ℕ) (x : H) :
    sourceTail r (((aeval (jointGenerator p F 0 0) (compressionPolynomial p F))^r) x):=by
  induction r with
  | zero=>simpa only [pow_zero,one_apply_eq_self] using tail_initial x
  | succ r ih=>
    rw [pow_succ',mul_apply_eq_comp]
    exact actual_polynomial_tail p F r _ ih

def jointPolynomial (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℂ[X]:=
  compressionPolynomial p F^57

theorem jointPolynomial_monic (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    (jointPolynomial p F).Monic:=(compressionPolynomial_monic p F).pow 57

theorem actualJoint_annihilated (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    aeval (jointGenerator p F 0 0) (jointPolynomial p F)=0:=by
  unfold jointPolynomial
  rw [map_pow]
  apply ContinuousLinearMap.ext
  intro x
  exact tail_terminal (actual_polynomial_pow_tail p F 57 x)

end LowEnergy.SourcePropagationAlgebraicResponse
