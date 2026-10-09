import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockYukawaCubicCurrent
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCutoffVolterra
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.FiniteGradeAlgebra
import Mathlib.Algebra.Ring.GeomSum
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussNativeEnergy GaussNativePotential
open GaussYukawaGrade GaussYukawaOperator GaussCoreLabel GaussYukawaInteraction
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent FullYSourceResolventGraphSplice
open GaussUnitaryHistory Filter
open scoped Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
local instance labelFintype:Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] sourcePair embed diagonalAction originalAction GaussFullHamiltonian.adjointAction

private theorem compression_embed(F:Index)(f:QuantumTest):
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f):=by
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem resolvent_embed(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f):=by
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_grade(F:Index):Commute gradeCore (compressionCore F):=by
  apply LinearMap.ext
  intro f
  apply embed_injective
  change embed (gradeCore (compressionCore F f))=embed (compressionCore F (gradeCore f))
  rw [←grade_core,compression_embed,compression_embed,←grade_core]
  exact congrArg (fun A:H→L[ℂ]H=>A (embed f)) (FullYSourceCutoffVolterra.source_compression_grade F).eq

private def baseShift(F:Index)(z:ℂ):End:=compressionCore F-z • (1:End)
private theorem base_left(F:Index)(z:ℂ)(hz:z.im≠0):
    resolventCore F z hz*baseShift F z=1:=by
  apply LinearMap.ext
  intro f
  apply embed_injective
  simp only [baseShift,Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    resolvent_embed,map_sub,map_smul,compression_embed]
  simpa only [finiteResolvent, mul_apply_eq_comp, sub_apply,
    smul_apply, one_apply_eq_self, map_sub, map_smul] using
    congrArg (fun A:H→L[ℂ]H=>A (embed f))
    (resolvent_left (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
private theorem base_right(F:Index)(z:ℂ)(hz:z.im≠0):
    baseShift F z*resolventCore F z hz=1:=by
  apply LinearMap.ext
  intro f
  apply embed_injective
  simp only [baseShift,Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    map_sub,map_smul,compression_embed,resolvent_embed]
  exact congrArg (fun A:H→L[ℂ]H=>A (embed f))
    (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
private theorem inverse_commutes {R:Type*}[Monoid R](G D U:R)
    (hl:U*D=1)(hr:D*U=1)(hc:G*D=D*G):G*U=U*G:=by
  calc
    G*U=(U*D)*(G*U):=by rw [hl,one_mul]
    _=U*(D*G)*U:=by simp only [mul_assoc]
    _=U*(G*D)*U:=by rw [hc]
    _=(U*G)*(D*U):=by simp only [mul_assoc]
    _=U*G:=by rw [hr,mul_one]
private theorem shift_commutes {R:Type*}[Ring R][Algebra ℂ R](G D:R)(z:ℂ)
    (h:Commute G D):Commute G (D-z • 1):=
  h.sub_right ((Commute.one_right G).smul_right z)
private theorem raises_comp {R:Type*}[Ring R](G U Y:R)
    (hU:G*U=U*G)(hY:G*Y=Y*G+Y):
    G*(-(U*Y))=(-(U*Y))*G+(-(U*Y)):=by
  calc
    _= -(U*(G*Y)):=by rw [mul_neg,←mul_assoc,hU,mul_assoc]
    _= -(U*(Y*G+Y)):=by rw [hY]
    _=_:=by simp only [mul_add,neg_add,neg_mul,mul_assoc]
private theorem factor_inverse {R:Type*}[Ring R](D U Y:R)(h:D*U=1):
    D+Y=D*(1-(-(U*Y))):=by
  rw [sub_neg_eq_add,mul_add,mul_one,←mul_assoc,h,one_mul]
private theorem resolvent_grade(F:Index)(z:ℂ)(hz:z.im≠0):
    Commute gradeCore (resolventCore F z hz):=by
  have hc:Commute gradeCore (baseShift F z):=
    shift_commutes gradeCore (compressionCore F) z (compression_grade F)
  exact inverse_commutes _ _ _ (base_left F z hz) (base_right F z hz) hc.eq
private theorem original_raises:gradeCore*originalAction=originalAction*gradeCore+originalAction:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [Module.End.mul_apply,LinearMap.add_apply,add_apply]
  unfold gradeCore originalAction
  exact fiber_source_grade (scalarField z) (f z)
private theorem core_resolution:(∑g:NativeHistoryGrade.Label,project g)=(1:End):=by
  apply LinearMap.ext
  intro f
  apply embed_injective
  simp only [LinearMap.sum_apply,Module.End.one_apply,map_sum,embed_project]
  rw [←sum_apply,NativeHistoryGrade.projection_resolution]
  rfl
private theorem core_grade_left(g:NativeHistoryGrade.Label):
    project g*gradeCore=(g.2.val:ℂ) • project g:=by
  apply LinearMap.ext
  intro f
  apply embed_injective
  simp only [Module.End.mul_apply,LinearMap.smul_apply,map_smul,embed_project,←grade_core]
  exact congrArg (fun A:H→L[ℂ]H=>A (embed f)) (source_grade_left g)
private theorem core_grade_right(g:NativeHistoryGrade.Label):
    gradeCore*project g=(g.2.val:ℂ) • project g:=by
  apply LinearMap.ext
  intro f
  apply embed_injective
  simp only [Module.End.mul_apply,LinearMap.smul_apply,map_smul,←grade_core,embed_project]
  exact congrArg (fun A:H→L[ℂ]H=>A (embed f)) (source_grade_right g)

/-- Literal unbounded Y acts on the same compact core before every original resolvent. -/
def literalStep(F:Index)(z:ℂ)(hz:z.im≠0):End:=-(resolventCore F z hz*originalAction)
private theorem step_raises(F:Index)(z:ℂ)(hz:z.im≠0):
    gradeCore*literalStep F z hz=literalStep F z hz*gradeCore+literalStep F z hz:=by
  exact raises_comp gradeCore (resolventCore F z hz) originalAction
    (resolvent_grade F z hz).eq original_raises

theorem literal_step_nilpotent(F:Index)(z:ℂ)(hz:z.im≠0):
    (literalStep F z hz)^57=0:=by
  have h:=FiniteGradeAlgebra.words_zero gradeCore project
    (fun g:NativeHistoryGrade.Label=>(g.2.val:ℤ)) core_resolution
    (fun g=>by simpa only [Int.cast_natCast] using core_grade_left g)
    (fun g=>by simpa only [Int.cast_natCast] using core_grade_right g)
    0 56 (fun g=>by have hg:=g.2.isLt;constructor <;> omega)
    (List.replicate 57 (literalStep F z hz))
    (fun T hT=>by obtain ⟨_,rfl⟩:=List.mem_replicate.mp hT;exact step_raises F z hz)
    (by simp)
  simpa only [List.prod_replicate] using h

def literalCoreResolvent(F:Index)(z:ℂ)(hz:z.im≠0):End:=
  (∑n∈Finset.range 57,(literalStep F z hz)^n)*resolventCore F z hz

def literalCoreShift(F:Index)(z:ℂ):End:=compressionCore F+originalAction-z • (1:End)
private theorem source_factor(F:Index)(z:ℂ)(hz:z.im≠0):
    literalCoreShift F z=baseShift F z*(1-literalStep F z hz):=by
  have he:literalCoreShift F z=baseShift F z+originalAction:=by
    unfold literalCoreShift baseShift
    abel
  rw [he]
  exact factor_inverse (baseShift F z) (resolventCore F z hz) originalAction (base_right F z hz)

theorem literal_core_left_inverse(F:Index)(z:ℂ)(hz:z.im≠0):
    literalCoreResolvent F z hz*literalCoreShift F z=1:=by
  rw [source_factor F z hz,literalCoreResolvent]
  calc
    _=(∑n∈Finset.range 57,(literalStep F z hz)^n)*
        (resolventCore F z hz*baseShift F z)*(1-literalStep F z hz):=by simp only [mul_assoc]
    _=1:=by rw [base_left,mul_one,geom_sum_mul_neg,literal_step_nilpotent,sub_zero]
theorem literal_core_right_inverse(F:Index)(z:ℂ)(hz:z.im≠0):
    literalCoreShift F z*literalCoreResolvent F z hz=1:=by
  rw [source_factor F z hz,literalCoreResolvent]
  calc
    _=baseShift F z*((1-literalStep F z hz)*(∑n∈Finset.range 57,(literalStep F z hz)^n))*
        resolventCore F z hz:=by simp only [mul_assoc]
    _=1:=by rw [mul_neg_geom_sum,literal_step_nilpotent,sub_zero,mul_one,base_right]

/-- The complete original forcing keeps the same compression defect, with literal Y already inside the inverse. -/
theorem literal_full_source_residual(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    (GaussFullHamiltonian.fullAction-z • (1:End)) (literalCoreResolvent F z hz f)=
      f+defectAction F (literalCoreResolvent F z hz f):=by
  have h:=LinearMap.congr_fun (literal_core_right_inverse F z hz) f
  simp only [Module.End.mul_apply,Module.End.one_apply] at h
  have he:GaussFullHamiltonian.fullAction-z • (1:End)=literalCoreShift F z+defectAction F:=by
    unfold GaussFullHamiltonian.fullAction literalCoreShift defectAction
    abel
  rw [he,LinearMap.add_apply,h]

open GaussCoframeForm (Paired)
private theorem conjugate_nonreal(z:ℂ)(hz:z.im≠0):(star z).im≠0:=by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
private theorem paired_mul {A B C D:End}(hA:Paired A B)(hC:Paired C D):
    Paired (A*C) (D*B):=fun f g=>(hA f (C g)).trans (hC (B f) g)
private theorem paired_neg {A B:End}(h:Paired A B):Paired (-A) (-B):=by
  intro f g
  simpa only [LinearMap.neg_apply,sourcePair,map_neg,inner_neg_left,inner_neg_right] using
    congrArg Neg.neg (h f g)
private theorem paired_pow {A B:End}(h:Paired A B)(n:ℕ):Paired (A^n) (B^n):=by
  induction n with
  | zero => intro f g; rfl
  | succ n ih =>
    rw [pow_succ,pow_succ']
    exact paired_mul ih h
private theorem paired_sum {A B:ℕ→End}(h:∀n,Paired (A n) (B n)):
    Paired (∑n∈Finset.range 57,A n) (∑n∈Finset.range 57,B n):=by
  intro f g
  simp only [LinearMap.sum_apply,sourcePair,map_sum,inner_sum,sum_inner]
  exact Finset.sum_congr rfl (fun n _=>by simpa only [sourcePair] using h n f g)
private theorem paired_inverse {A B U V:End}(hp:Paired A B)(hA:A*U=1)(hB:B*V=1):
    Paired U V:=by
  intro f g
  have hf:=LinearMap.congr_fun hB f
  have hg:=LinearMap.congr_fun hA g
  simp only [Module.End.mul_apply,Module.End.one_apply] at hf hg
  calc
    sourcePair f (U g)=sourcePair (B (V f)) (U g):=by rw [hf]
    _=sourcePair (V f) (A (U g)):=(hp (V f) (U g)).symm
    _=sourcePair (V f) g:=by rw [hg]
private theorem base_pair(F:Index)(z:ℂ):Paired (baseShift F z) (baseShift F (star z)):=by
  intro f g
  simp only [baseShift,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    sourcePair,map_sub,map_smul,compression_embed,inner_sub_left,inner_sub_right,
    inner_smul_left,inner_smul_right]
  have hc:inner ℂ (embed f) (GaussGradedCompression.compression F (embed g))=
      inner ℂ (GaussGradedCompression.compression F (embed f)) (embed g):=
    (GaussGradedCompression.compression_pair F (embed f) (embed g)).symm
  have hs:(starRingEnd ℂ) (star z)=z:=star_star z
  exact congrArg₂ (fun a b:ℂ=>a-b) hc
    (congrArg (fun w:ℂ=>w*inner ℂ (embed f) (embed g)) hs.symm)
private theorem base_resolvent_pair(F:Index)(z:ℂ)(hz:z.im≠0):
    Paired (resolventCore F z hz) (resolventCore F (star z) (conjugate_nonreal z hz)):=
  paired_inverse (base_pair F z) (base_right F z hz)
    (base_right F (star z) (conjugate_nonreal z hz))

/-- The independently generated literal adjoint acts after each original core resolvent. -/
def literalSharpStep(F:Index)(z:ℂ)(hz:z.im≠0):End:=
  -(GaussFullHamiltonian.adjointAction*resolventCore F z hz)
def literalSharpResolvent(F:Index)(z:ℂ)(hz:z.im≠0):End:=
  resolventCore F z hz*(∑n∈Finset.range 57,(literalSharpStep F z hz)^n)
def literalSharpShift(F:Index)(z:ℂ):End:=
  compressionCore F+GaussFullHamiltonian.adjointAction-z • (1:End)
private theorem sharp_step_pair(F:Index)(z:ℂ)(hz:z.im≠0):
    Paired (literalSharpStep F z hz) (literalStep F (star z) (conjugate_nonreal z hz)):=
  paired_neg (paired_mul GaussFullHamiltonian.yukawa_pair (base_resolvent_pair F z hz))

/-- Both kernel legs use the same original scalar field and the original source pairing. -/
theorem literal_two_leg_pair(F:Index)(z:ℂ)(hz:z.im≠0)(f g:QuantumTest):
    sourcePair f (literalSharpResolvent F z hz g)=
      sourcePair (literalCoreResolvent F (star z) (conjugate_nonreal z hz) f) g:=
  paired_mul (base_resolvent_pair F z hz)
    (paired_sum (fun n=>paired_pow (sharp_step_pair F z hz) n)) f g
private theorem sharp_shift_pair(F:Index)(z:ℂ):
    Paired (literalSharpShift F z) (literalCoreShift F (star z)):=by
  intro f g
  have hY:=GaussFullHamiltonian.yukawa_pair f g
  have hC:=base_pair F z f g
  have he:literalSharpShift F z=baseShift F z+GaussFullHamiltonian.adjointAction:=by
    unfold literalSharpShift baseShift
    abel
  have he':literalCoreShift F (star z)=baseShift F (star z)+originalAction:=by
    unfold literalCoreShift baseShift
    abel
  rw [he,he']
  simpa only [LinearMap.add_apply,sourcePair,map_add,inner_add_right,inner_add_left] using
    congrArg₂ (·+·) hC hY
private theorem paired_identity {A:End}(h:Paired A 1):A=1:=by
  apply LinearMap.ext
  intro f
  apply pair_separates
  intro g
  exact h g f

theorem literal_sharp_left_inverse(F:Index)(z:ℂ)(hz:z.im≠0):
    literalSharpResolvent F z hz*literalSharpShift F z=1:=by
  apply paired_identity
  have h:=paired_mul (literal_two_leg_pair F z hz) (sharp_shift_pair F z)
  rwa [literal_core_right_inverse] at h

theorem literal_sharp_right_inverse(F:Index)(z:ℂ)(hz:z.im≠0):
    literalSharpShift F z*literalSharpResolvent F z hz=1:=by
  apply paired_identity
  have h:=paired_mul (sharp_shift_pair F z) (literal_two_leg_pair F z hz)
  rwa [literal_core_left_inverse] at h

/-- The independent sharp full source has exactly the same compression defect. -/
theorem literal_sharp_full_source_residual(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    (GaussFullHamiltonian.sharpAction-z • (1:End)) (literalSharpResolvent F z hz f)=
      f+defectAction F (literalSharpResolvent F z hz f):=by
  have h:=LinearMap.congr_fun (literal_sharp_right_inverse F z hz) f
  simp only [Module.End.mul_apply,Module.End.one_apply] at h
  have he:GaussFullHamiltonian.sharpAction-z • (1:End)=literalSharpShift F z+defectAction F:=by
    unfold GaussFullHamiltonian.sharpAction literalSharpShift defectAction
    abel
  rw [he,LinearMap.add_apply,h]

end LowEnergy.FullYDynamicSource
