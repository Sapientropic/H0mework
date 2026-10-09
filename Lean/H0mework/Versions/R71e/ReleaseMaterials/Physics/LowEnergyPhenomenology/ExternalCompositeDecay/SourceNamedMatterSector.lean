import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterBottomResponse
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussFockPair
open FullYDynamicSource FullYSourceResolventGraphSplice SourceClockYukawaCubicCurrent
open GaussCoreLabel GaussYukawaGrade GaussYukawaInteraction NativeHistoryGrade GaussFockLabel
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open NamedMatterWedgeQt GaussYukawaCoefficient GaussYukawaOperator
open scoped BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance sectorLabelFintype:Fintype Label:=Fintype.ofFinite _
attribute [local irreducible] embed sourcePair GaussCoreLabel.project NativeHistoryGrade.projection
  GaussGradedCompression.compression GaussYukawaGrade.grade

private theorem nonzero_eigen{a b v:ℂ}(h:a*v=b*v)(hne:a≠b):v=0:=by
  have hz:(a-b)*v=0:=by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

private theorem count_word_bound {ι:Type*}[LinearOrder ι](s word:Finset ι):
    SourceGradeTransport.count s word≤word.card:=Finset.card_filter_le _ _

/-- The original occupation label is simultaneously the literal CAR number and target grade. -/
theorem actual_fiber_sector(n:Fin 505)(k:Fin 57)(q:FockFiber):
    fiberPiece (n,k) q=q ↔
      fiberNumber q=(n.val:ℂ) • q ∧ fiberGrade q=(k.val:ℂ) • q:=by
  constructor
  · intro h
    constructor
    · apply PiLp.ext
      intro word
      have hw:=congrArg (fun v:FockFiber=>v word) h
      rw [fiberPiece_apply] at hw
      simp only [fiberNumber_apply,PiLp.smul_apply,smul_eq_mul]
      by_cases he:sourceLabel word=(n,k)
      · have hn:word.card=n.val:=congrArg (fun l:Label=>l.1.val) he
        rw [hn]
      · simp only [if_neg he] at hw
        rw [←hw,mul_zero,mul_zero]
    · apply PiLp.ext
      intro word
      have hw:=congrArg (fun v:FockFiber=>v word) h
      rw [fiberPiece_apply] at hw
      simp only [fiberGrade,blockWeight_apply,PiLp.smul_apply,smul_eq_mul]
      change ((sourceGrade word).val:ℂ)*q word=(k.val:ℂ)*q word
      by_cases he:sourceLabel word=(n,k)
      · have hk:(sourceGrade word).val=k.val:=congrArg (fun l:Label=>l.2.val) he
        rw [hk]
      · simp only [if_neg he] at hw
        rw [←hw,mul_zero,mul_zero]
  · rintro ⟨hn,hk⟩
    apply PiLp.ext
    intro word
    rw [fiberPiece_apply]
    split_ifs with he
    · rfl
    · have hnum:=congrArg (fun v:FockFiber=>v word) hn
      have hgrade:=congrArg (fun v:FockFiber=>v word) hk
      simp only [fiberNumber_apply,PiLp.smul_apply,smul_eq_mul] at hnum
      simp only [fiberGrade,blockWeight_apply,PiLp.smul_apply,smul_eq_mul] at hgrade
      change ((sourceGrade word).val:ℂ)*q word=(k.val:ℂ)*q word at hgrade
      by_cases hc:word.card=n.val
      · have hg:(sourceGrade word).val≠k.val:=by
          intro hh
          exact he (Prod.ext (Fin.ext hc) (Fin.ext hh))
        exact (nonzero_eigen hgrade (by exact_mod_cast hg)).symm
      · exact (nonzero_eigen hnum (by exact_mod_cast hc)).symm

/-- A sector beyond its actual particle count is empty on the original full504 Fock carrier. -/
theorem actual_empty_sector(n:Fin 505)(k:Fin 57)(h:n.val<k.val)(f:QuantumTest):
    project (n,k) f=0:=by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  rw [project_apply,fiberPiece_apply]
  change (if sourceLabel word=(n,k) then f z word else 0)=0
  have he:sourceLabel word≠(n,k):=by
    intro he
    have hn:word.card=n.val:=congrArg (fun l:Label=>l.1.val) he
    have hk:(sourceGrade word).val=k.val:=congrArg (fun l:Label=>l.2.val) he
    have hb:(sourceGrade word).val≤word.card:=@count_word_bound Mode modeOrder target word
    omega
  simp only [if_neg he]

private theorem source_number(phi:SourceQuantumScalarChart.Scalar)(q:FockFiber):
    fiberNumber (sourceMap phi q)=sourceMap phi (fiberNumber q):=by
  rw [source_map_return]
  exact congrArg (fun A:FockFiber→L[ℂ]FockFiber=>A q) (GaussQuantumMultiplier.number_commute _).eq

/-- Every actual original-Y update retains Number and raises exactly one grade. -/
theorem actual_Y_sector_successor(n:Fin 505)(k:Fin 57)(hk:k.val+1<57)(f:QuantumTest)
    (hf:project (n,k) f=f):
    project (n,⟨k.val+1,hk⟩) (originalAction f)=originalAction f:=by
  apply DFunLike.ext
  intro z
  have hs:=congrArg (fun q:QuantumTest=>q z) hf
  rw [project_apply] at hs
  obtain ⟨hn,hg⟩:=(actual_fiber_sector n k (f z)).mp hs
  rw [project_apply]
  change fiberPiece (n,⟨k.val+1,hk⟩) (sourceMap (GaussNativePotential.scalarField z) (f z))=_
  apply (actual_fiber_sector n ⟨k.val+1,hk⟩ _).mpr
  constructor
  · rw [source_number,hn,map_smul]
  · rw [fiber_source_grade,hg,map_smul]
    simp only [Nat.cast_add,Nat.cast_one,add_smul,one_smul]

private theorem finite_resolvent_label(F:Index)(l:Label)(z:ℂ)(hz:z.im≠0):
    Commute (projection l) (finiteResolvent F z):=by
  have hc:Commute (projection l) (GaussGradedCompression.compression F-z • 1):=
    (GaussGradedCompression.compression_commutes F l).sub_right ((Commute.one_right _).smul_right z)
  obtain ⟨u,hu⟩:=resolvent_isUnit (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) z hz
  unfold finiteResolvent FullYSourceResolventGraphSplice.resolvent
  rw [←hu] at hc ⊢
  rw [Ring.inverse_unit]
  exact hc.units_inv_right

private theorem core_embed(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f):=by
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

/-- The original cutoff resolvent preserves the same Number/grade sector before every Y insertion. -/
theorem actual_resolvent_sector(F:Index)(l:Label)(z:ℂ)(hz:z.im≠0)(f:QuantumTest)
    (hf:project l f=f):project l (resolventCore F z hz f)=resolventCore F z hz f:=by
  apply embed_injective
  rw [embed_project,core_embed]
  have h:=congrArg (fun A:H→L[ℂ]H=>A (embed f)) (finite_resolvent_label F l z hz).eq
  simp only [mul_apply_eq_comp] at h
  have hf':projection l (embed f)=embed f:=(embed_project l f).symm.trans (congrArg embed hf)
  exact h.trans (congrArg (finiteResolvent F z) hf')

/-- The actual named220 source begins at Number three and grade zero on either independent branch. -/
theorem actual_wedge_bottom_sector(dual:Bool)(a:WedgeFiber)(f:GaussDensityCore.ScalarTest):
    project (3,0) (wedgeTest dual a f)=wedgeTest dual a f:=by
  apply DFunLike.ext
  intro z
  rw [project_apply,actual_wedge_test_value,map_smul]
  congr 1
  apply (actual_fiber_sector 3 0 _).mpr
  constructor
  · have hb(w:WedgeIndex):fiberNumber (fiberBasis dual w)=(3:ℂ) • fiberBasis dual w:=by
      apply PiLp.ext
      intro word
      simp only [fiberNumber_apply,PiLp.smul_apply,smul_eq_mul]
      by_cases he:word=occupation dual w.val
      · subst word
        rw [occupation_card,w.property]
        norm_num
      · simp [fiberBasis,EuclideanSpace.single,he]
    simp only [wedgeFiber,map_sum,map_smul,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [hb]
    exact smul_comm (a w) (3:ℂ) (fiberBasis dual w)
  · simpa only [Fin.val_zero,Nat.cast_zero,zero_smul] using actual_named_wedge_grade_zero dual a

end LowEnergy.NamedColorQtNext
