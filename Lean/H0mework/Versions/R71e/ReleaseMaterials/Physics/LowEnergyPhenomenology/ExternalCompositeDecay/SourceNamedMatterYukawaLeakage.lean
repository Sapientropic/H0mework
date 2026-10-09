import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterWholeGaussReturn
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussYukawaGrade
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open SaturationMonoid SaturationMonoid.PhysicsCore NamedMatterWedgeQt
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open SourceQuantumGaugeSliceCoordinates GaussCoreDifferential GaussDensityCore
open QuantizationCheck.Fermion
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=SourceRealScalarFock.branchOrder.toDecidableEq

/-- The named original degree-two mother modes lie below the actual Yukawa raising target. -/
theorem actual_named_outside_Y_target(dual:Bool)(i:NamedMode):rootMode dual i∉target:=by
  cases dual <;> simp [rootMode,mem_target_left,mem_target_right,isSix,rootIndex]

/-- Every original Yukawa row into the named external modes vanishes, for every scalar field value and every full504 input. -/
theorem actual_Y_named_row_zero(dual:Bool)(phi:Scalar)(i:NamedMode)(j:Mode):
    GaussYukawaCoefficient.fullMatrix phi (rootMode dual i) j=0:=by
  have h:=GaussYukawaGrade.matrix_raises phi (rootMode dual i) j
  have hn:=actual_named_outside_Y_target dual i
  by_cases hj:j∈target
  · norm_num [hn,hj] at h
    exact h
  · simpa only [hn,hj,ite_false,sub_self,zero_sub,one_mul,neg_mul,neg_eq_zero] using h

private theorem adjoint_source_return(phi:Scalar):
    GaussFullHamiltonian.adjointMap phi=
      GaussQuantumMultiplier.quantized (GaussYukawaCoefficient.fullMatrix phi).conjTranspose:=by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  have h:=quantizedFiber_adjoint (GaussYukawaCoefficient.fullMatrix phi).conjTranspose x y
  rw [Matrix.conjTranspose_conjTranspose] at h
  exact h

private theorem sharp_create(dual:Bool)(phi:Scalar)(i:NamedMode)(x:FockFiber):
    GaussFullHamiltonian.adjointMap phi (GaussCARHistory.createFiber (rootMode dual i) x)=
      GaussCARHistory.createFiber (rootMode dual i) (GaussFullHamiltonian.adjointMap phi x):=by
  rw [adjoint_source_return]
  apply fiberCoordinates.injective
  have h:=LinearMap.congr_fun
    (LowEnergy.FullQuantum.NativeHistory.CurrentCAR.creation_quantize
      (GaussYukawaCoefficient.fullMatrix phi).conjTranspose (rootMode dual i)) (fiberCoordinates x)
  simp only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.sum_apply,LinearMap.smul_apply] at h
  simp_rw [Matrix.conjTranspose_apply,actual_Y_named_row_zero,star_zero] at h
  simp only [zero_smul,Finset.sum_const_zero] at h
  exact sub_eq_zero.mp h

private theorem sharp_vacuum(dual:Bool)(phi:Scalar):
    GaussFullHamiltonian.adjointMap phi (occupationFiber dual ∅)=0:=by
  rw [adjoint_source_return]
  apply fiberCoordinates.injective
  have hv:fiberCoordinates (occupationFiber dual ∅)=(QuantizationCheck.Fermion.vacuum:Fock Mode):=by
    funext s
    simp [occupationFiber,occupation,fiberCoordinates,EuclideanSpace.single,QuantizationCheck.Fermion.vacuum,occupationBasis]
  change LowEnergy.Fermion.quantize (GaussYukawaCoefficient.fullMatrix phi).conjTranspose
    (fiberCoordinates (occupationFiber dual ∅))=fiberCoordinates 0
  rw [hv,map_zero]
  simp only [LowEnergy.Fermion.quantize,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    LowEnergy.Fermion.annihilation_apply,annihilate_vacuum,map_zero,smul_zero,Finset.sum_const_zero]

theorem actual_sharp_named_triple_zero(dual:Bool)(phi:Scalar)(i j k:NamedMode):
    GaussFullHamiltonian.adjointMap phi (orderedTriple dual i j k)=0:=by
  rw [orderedTriple,sharp_create,sharp_create,sharp_create,sharp_vacuum]
  simp only [map_zero]

private theorem sharp_basis_zero(dual:Bool)(phi:Scalar)(w:WedgeIndex):
    GaussFullHamiltonian.adjointMap phi (fiberBasis dual w)=0:=by
  have h: fiberBasis dual w=sourcePhase dual w • namedCARBasis dual w:=by
    rw [actual_named_CAR_basis,smul_smul,actual_source_phase_square,one_smul]
  rw [h,map_smul,namedCARBasis,actual_sharp_named_triple_zero,smul_zero]

/-- The literal independent sharp Yukawa vanishes on the complete named wedge220 external source; no scalar-vacuum specialization is used. -/
theorem actual_sharp_named_wedge_zero(dual:Bool)(phi:Scalar)(a:WedgeFiber):
    GaussFullHamiltonian.adjointMap phi (wedgeFiber dual a)=0:=by
  simp only [wedgeFiber,map_sum,map_smul,sharp_basis_zero,smul_zero,Finset.sum_const_zero]

/-- Original primal Yukawa output is orthogonal to every named external source, even across the two branch choices. -/
theorem actual_Y_named_orthogonal(left right:Bool)(phi:Scalar)(a b:WedgeFiber):
    inner ℂ (wedgeFiber left a) (GaussYukawaCoefficient.sourceMap phi (wedgeFiber right b))=0:=by
  rw [←ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (GaussFullHamiltonian.adjointMap phi (wedgeFiber left a)) (wedgeFiber right b)=0
  rw [actual_sharp_named_wedge_zero,inner_zero_left]

/-- The same field-dependent sharp source vanishes on the actual normalized epsilon quantum test. -/
theorem actual_epsilon_sharp_Y_zero(dual:Bool)(e:Epsilon20)(f:ScalarTest):
    GaussFullHamiltonian.adjointAction (epsilonSection dual e f)=0:=by
  apply DFunLike.ext
  intro z
  change GaussFullHamiltonian.adjointMap (GaussNativePotential.scalarField z) (epsilonSection dual e f z)=0
  rw [epsilon_section_value,map_smul]
  change f z • GaussFullHamiltonian.adjointMap (GaussNativePotential.scalarField z)
    (wedgeFiber dual (epsilon20Coordinates dual e))=0
  rw [actual_sharp_named_wedge_zero,smul_zero]

/-- The external sharp fullsource equation is returned to its actual complete H0 expression by the original Y grade. -/
theorem actual_epsilon_sharp_full_source(dual:Bool)(e:Epsilon20)(f:ScalarTest):
    GaussFullHamiltonian.sharpAction (epsilonSection dual e f)=
      GaussDiagonalHistory.diagonalAction (epsilonSection dual e f):=by
  rw [GaussFullHamiltonian.sharpAction,LinearMap.add_apply,actual_epsilon_sharp_Y_zero,add_zero]

theorem actual_named_wedge_grade_zero(dual:Bool)(a:WedgeFiber):
    GaussYukawaGrade.fiberGrade (wedgeFiber dual a)=0:=by
  have hb(w:WedgeIndex):GaussYukawaGrade.fiberGrade (fiberBasis dual w)=0:=by
    have he:(occupation dual w.val).filter (fun i=>i∈target)=∅:=by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi
      obtain ⟨j,hj,rfl⟩:=Finset.mem_map.mp hi
      exact actual_named_outside_Y_target dual j
    rw [fiberBasis,GaussYukawaGrade.fiberGrade,GaussFockLabel.blockWeight_basis]
    change ((SourceGradeTransport.count target (occupation dual w.val):ℕ):ℂ) • _=0
    rw [SourceGradeTransport.count,he,Finset.card_empty,Nat.cast_zero,zero_smul]
  simp only [wedgeFiber,map_sum,map_smul,hb,smul_zero,Finset.sum_const_zero]

theorem actual_epsilon_grade_zero(dual:Bool)(e:Epsilon20)(f:ScalarTest):
    GaussYukawaGrade.gradeCore (epsilonSection dual e f)=0:=by
  apply DFunLike.ext
  intro z
  change GaussYukawaGrade.fiberGrade (epsilonSection dual e f z)=0
  rw [epsilon_section_value,map_smul]
  change f z • GaussYukawaGrade.fiberGrade (wedgeFiber dual (epsilon20Coordinates dual e))=0
  rw [actual_named_wedge_grade_zero,smul_zero]

private theorem fiber_grade_pair(x y:FockFiber):
    inner ℂ (GaussYukawaGrade.fiberGrade x) y=inner ℂ x (GaussYukawaGrade.fiberGrade y):=by
  simp only [GaussYukawaGrade.fiberGrade,PiLp.inner_apply,GaussFockLabel.blockWeight_apply,RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro word _
  change y word*star (((NativeHistoryGrade.sourceGrade word).val:ℂ)*x word)=
    (((NativeHistoryGrade.sourceGrade word).val:ℂ)*y word)*star (x word)
  simp only [star_mul,star_natCast]
  ring

/-- The actual lowering adjoint annihilates the entire bottom grade, as a consequence of the original raising law. -/
theorem actual_sharp_bottom_zero(phi:Scalar)(q:FockFiber)(hq:GaussYukawaGrade.fiberGrade q=0):
    GaussFullHamiltonian.adjointMap phi q=0:=by
  have he:GaussYukawaGrade.fiberGrade (GaussFullHamiltonian.adjointMap phi q)=
      -GaussFullHamiltonian.adjointMap phi q:=by
    apply ext_inner_left ℂ
    intro x
    rw [←fiber_grade_pair]
    change inner ℂ (GaussYukawaGrade.fiberGrade x) ((GaussYukawaCoefficient.sourceMap phi).adjoint q)=_
    rw [ContinuousLinearMap.adjoint_inner_right]
    have hy:=GaussYukawaGrade.fiber_source_grade phi x
    have hr:GaussYukawaCoefficient.sourceMap phi (GaussYukawaGrade.fiberGrade x)=
        GaussYukawaGrade.fiberGrade (GaussYukawaCoefficient.sourceMap phi x)-GaussYukawaCoefficient.sourceMap phi x:=by
      rw [hy,add_sub_cancel_right]
    rw [hr,inner_sub_left,fiber_grade_pair,hq,inner_zero_right,zero_sub,inner_neg_right]
    change -inner ℂ (GaussYukawaCoefficient.sourceMap phi x) q=
      -inner ℂ x ((GaussYukawaCoefficient.sourceMap phi).adjoint q)
    rw [ContinuousLinearMap.adjoint_inner_right]
  apply PiLp.ext
  intro word
  have h:=congrArg (fun v:FockFiber=>v word) he
  simp only [GaussYukawaGrade.fiberGrade,GaussFockLabel.blockWeight_apply,PiLp.neg_apply] at h
  change ((NativeHistoryGrade.sourceGrade word).val:ℂ)*GaussFullHamiltonian.adjointMap phi q word=
    -GaussFullHamiltonian.adjointMap phi q word at h
  have hc:((NativeHistoryGrade.sourceGrade word).val:ℂ)+1≠0:=by
    exact_mod_cast Nat.succ_ne_zero (NativeHistoryGrade.sourceGrade word).val
  change GaussFullHamiltonian.adjointMap phi q word=0
  apply (mul_eq_zero.mp (show (((NativeHistoryGrade.sourceGrade word).val:ℂ)+1)*
      GaussFullHamiltonian.adjointMap phi q word=0 by
    linear_combination h)).resolve_left hc


end LowEnergy.NamedColorQtNext
