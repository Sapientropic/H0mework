import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterYukawaLeakage
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYLiteralCoreResolvent
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open GaussYukawaGrade FullYDynamicSource FullYSourceResolventGraphSplice
open SourceClockYukawaCubicCurrent SourceScalarPairedTransport
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussDensityCore
open scoped BigOperators InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
attribute [local irreducible] embed literalSharpResolvent GaussDiagonalHistory.diagonalAction GaussYukawaGrade.grade

theorem actual_bottom_sharp_action(f:QuantumTest)(hf:gradeCore f=0):
    GaussFullHamiltonian.adjointAction f=0:=by
  apply DFunLike.ext
  intro z
  have h:=congrArg (fun u:QuantumTest=>u z) hf
  change fiberGrade (f z)=0 at h
  exact actual_sharp_bottom_zero (GaussNativePotential.scalarField z) (f z) h

private theorem resolvent_embed(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f):=by
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_embed(F:Index)(f:QuantumTest):
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f):=by
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem finite_resolvent_grade(F:Index)(z:ℂ)(hz:z.im≠0):
    Commute GaussYukawaGrade.grade (finiteResolvent F z):=by
  have hc:Commute GaussYukawaGrade.grade (GaussGradedCompression.compression F-z • 1):=
    (FullYSourceCutoffVolterra.source_compression_grade F).sub_right
      ((Commute.one_right _).smul_right z)
  obtain ⟨u,hu⟩:=resolvent_isUnit (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) z hz
  unfold finiteResolvent FullYSourceResolventGraphSplice.resolvent
  rw [←hu] at hc ⊢
  rw [Ring.inverse_unit]
  exact hc.units_inv_right

private theorem resolvent_bottom(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest)(hf:gradeCore f=0):
    gradeCore (resolventCore F z hz f)=0:=by
  apply embed_injective
  rw [←grade_core,resolvent_embed,map_zero]
  have h:=congrArg (fun T:H→L[ℂ]H=>T (embed f)) (finite_resolvent_grade F z hz).eq
  simp only [mul_apply_eq_comp] at h
  have hg:GaussYukawaGrade.grade (embed f)=0:=
    (grade_core f).trans ((congrArg embed hf).trans (map_zero embed))
  exact h.trans ((congrArg (finiteResolvent F z) hg).trans (map_zero (finiteResolvent F z)))

private theorem base_core_equation(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    compressionCore F (resolventCore F z hz f)-z • resolventCore F z hz f=f:=by
  apply embed_injective
  simp only [map_sub,map_smul,compression_embed,resolvent_embed]
  exact congrArg (fun T:H→L[ℂ]H=>T (embed f))
    (resolvent_right (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) z hz)

/-- The literal full sharp inverse collapses on its actual bottom-grade forcing, for every cutoff and every nonreal frequency. -/
theorem actual_bottom_sharp_resolvent(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest)(hf:gradeCore f=0):
    literalSharpResolvent F z hz f=resolventCore F z hz f:=by
  have hs:literalSharpShift F z (resolventCore F z hz f)=f:=by
    simp only [literalSharpShift,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,
      Module.End.one_apply,actual_bottom_sharp_action _ (resolvent_bottom F z hz f hf),add_zero]
    exact base_core_equation F z hz f
  calc
    literalSharpResolvent F z hz f=
        literalSharpResolvent F z hz (literalSharpShift F z (resolventCore F z hz f)):=by rw [hs]
    _=resolventCore F z hz f:=LinearMap.congr_fun (literal_sharp_left_inverse F z hz) _

/-- This is an identity for the actual fullY sharp response to the generated epsilon source, without a cutoff-membership premise. -/
theorem actual_epsilon_sharp_resolvent(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(e:Epsilon20)(f:ScalarTest):
    embed (literalSharpResolvent F z hz (epsilonSection dual e f))=
      finiteResolvent F z (embed (epsilonSection dual e f)):=by
  rw [actual_bottom_sharp_resolvent F z hz _ (actual_epsilon_grade_zero dual e f),resolvent_embed]

/-- The source-generated sharp response has one cutoff-independent nonreal-frequency price. -/
theorem actual_epsilon_sharp_uniform_bound(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(e:Epsilon20)(f:ScalarTest):
    ‖embed (literalSharpResolvent F z hz (epsilonSection dual e f))‖≤
      (1/|z.im|)*(‖e‖*‖scalarLp 3 f‖):=by
  rw [actual_epsilon_sharp_resolvent]
  calc
    _≤‖finiteResolvent F z‖*‖embed (epsilonSection dual e f)‖:=(finiteResolvent F z).le_opNorm _
    _≤(1/|z.im|)*‖embed (epsilonSection dual e f)‖:=
      mul_le_mul_of_nonneg_right (finite_resolvent_norm F z hz) (norm_nonneg _)
    _=_:=by
      change (1/|z.im|)*‖embed (epsilon20Test dual e f)‖=_
      rw [actual_epsilon20_source_norm]

end LowEnergy.NamedColorQtNext
