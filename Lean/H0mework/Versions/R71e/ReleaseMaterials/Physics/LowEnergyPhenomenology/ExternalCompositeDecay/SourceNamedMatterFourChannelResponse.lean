import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterSector
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussFockPair
open FullYDynamicSource FullYSourceResolventGraphSplice SourceClockYukawaCubicCurrent
open GaussCoreLabel GaussYukawaGrade NativeHistoryGrade NamedMatterWedgeQt GaussYukawaOperator
open GaussDensityCore SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace
attribute [local irreducible] embed sourcePair GaussCoreLabel.project NativeHistoryGrade.projection
  GaussGradedCompression.compression literalCoreResolvent

def originalWedgeLeg(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(a:WedgeFiber)(f:ScalarTest)(j:ℕ):QuantumTest:=
  ((literalStep F z hz)^j) (resolventCore F z hz (wedgeTest dual a f))

private theorem step_sector(F:Index)(n:Fin 505)(k:Fin 57)(hk:k.val+1<57)(z:ℂ)(hz:z.im≠0)
    (f:QuantumTest)(hf:project (n,k) f=f):
    project (n,⟨k.val+1,hk⟩) (literalStep F z hz f)=literalStep F z hz f:=by
  have h:=actual_resolvent_sector F (n,⟨k.val+1,hk⟩) z hz (originalAction f)
    (actual_Y_sector_successor n k hk f hf)
  simpa only [literalStep,LinearMap.neg_apply,Module.End.mul_apply,map_neg] using congrArg Neg.neg h

private theorem leg_sector(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(a:WedgeFiber)(f:ScalarTest):
    ∀(j:ℕ)(hj:j<57),project (3,⟨j,hj⟩) (originalWedgeLeg F z hz dual a f j)=originalWedgeLeg F z hz dual a f j:=by
  intro j
  induction j with
  | zero=>
    intro hj
    simp only [originalWedgeLeg,pow_zero,Module.End.one_apply]
    exact actual_resolvent_sector F (3,0) z hz _ (actual_wedge_bottom_sector dual a f)
  | succ j ih=>
    intro hj
    have h:=step_sector F 3 ⟨j,by omega⟩ hj z hz (originalWedgeLeg F z hz dual a f j) (ih (by omega))
    simpa only [originalWedgeLeg,pow_succ',Module.End.mul_apply] using h

/-- The original interleaved resolvent/Y chain terminates after three insertions because Number three cannot carry grade four. -/
theorem actual_fourth_wedge_leg_zero(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(a:WedgeFiber)(f:ScalarTest):
    originalWedgeLeg F z hz dual a f 4=0:=
  (leg_sector F z hz dual a f 4 (by decide)).symm.trans (actual_empty_sector 3 4 (by decide) _)

private theorem long_leg_zero(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(a:WedgeFiber)(f:ScalarTest)
    (j:ℕ)(hj:4≤j):originalWedgeLeg F z hz dual a f j=0:=by
  let T:=literalStep F z hz
  let q:=resolventCore F z hz (wedgeTest dual a f)
  change (T^j) q=0
  calc
    _=(T^(j-4)*T^4) q:=by rw [←pow_add,Nat.sub_add_cancel hj]
    _=(T^(j-4)) (originalWedgeLeg F z hz dual a f 4):=rfl
    _=0:=by rw [actual_fourth_wedge_leg_zero,map_zero]

/-- Complete fullY response of the named220 source, with all three leakage channels retained as actual noncommuting source words. -/
theorem actual_fullY_four_channel_response(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(a:WedgeFiber)(f:ScalarTest):
    literalCoreResolvent F z hz (wedgeTest dual a f)=∑j:Fin 4,originalWedgeLeg F z hz dual a f j.val:=by
  simp only [literalCoreResolvent,Module.End.mul_apply,LinearMap.sum_apply,originalWedgeLeg]
  rw [Fin.sum_univ_eq_sum_range (fun j:ℕ=>((literalStep F z hz)^j)
    (resolventCore F z hz (wedgeTest dual a f))) 4]
  symm
  apply Finset.sum_subset (Finset.range_mono (by decide:4≤57))
  intro j _ hj
  exact long_leg_zero F z hz dual a f j (by simpa only [Finset.mem_range,not_lt] using hj)

/-- Each original response word belongs to its distinct physical output grade. -/
theorem actual_four_channel_sector(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(a:WedgeFiber)(f:ScalarTest)(j:Fin 4):
    project (3,⟨j.val,by omega⟩) (originalWedgeLeg F z hz dual a f j.val)=originalWedgeLeg F z hz dual a f j.val:=
  leg_sector F z hz dual a f j.val (by omega)

theorem actual_four_channel_recurrence(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(a:WedgeFiber)(f:ScalarTest)(j:ℕ):
    originalWedgeLeg F z hz dual a f (j+1)=
      -resolventCore F z hz (originalAction (originalWedgeLeg F z hz dual a f j)):=by
  simp only [originalWedgeLeg,pow_succ',Module.End.mul_apply,literalStep,LinearMap.neg_apply]

private theorem channels_orthogonal(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(a:WedgeFiber)(f:ScalarTest)
    (i j:Fin 4)(hij:i≠j):
    inner ℂ (embed (originalWedgeLeg F z hz dual a f i.val))
      (embed (originalWedgeLeg F z hz dual a f j.val))=0:=by
  let li:Label:=(3,⟨i.val,by omega⟩)
  let lj:Label:=(3,⟨j.val,by omega⟩)
  have hi:projection li (embed (originalWedgeLeg F z hz dual a f i.val))=
      embed (originalWedgeLeg F z hz dual a f i.val):=
    (embed_project li _).symm.trans (congrArg embed (actual_four_channel_sector F z hz dual a f i))
  have hj:projection lj (embed (originalWedgeLeg F z hz dual a f j.val))=
      embed (originalWedgeLeg F z hz dual a f j.val):=
    (embed_project lj _).symm.trans (congrArg embed (actual_four_channel_sector F z hz dual a f j))
  have hneq:li≠lj:=by intro h; exact hij (Fin.ext (congrArg (fun l:Label=>l.2.val) h))
  have he:projection li (projection lj (embed (originalWedgeLeg F z hz dual a f j.val)))=0:=by
    have h:=congrArg (fun T:H→L[ℂ]H=>T (embed (originalWedgeLeg F z hz dual a f j.val))) (projection_product li lj)
    simpa only [if_neg hneq,mul_apply_eq_comp,zero_apply] using h
  calc
    _=inner ℂ (projection li (embed (originalWedgeLeg F z hz dual a f i.val)))
        (projection lj (embed (originalWedgeLeg F z hz dual a f j.val))):=by rw [hi,hj]
    _=inner ℂ (embed (originalWedgeLeg F z hz dual a f i.val))
        (projection li (projection lj (embed (originalWedgeLeg F z hz dual a f j.val)))):=
      projection_symmetric li _ _
    _=0:=by rw [he,inner_zero_right]

/-- The complete physical norm separates into four nonnegative actual-Y channel intensities. -/
theorem actual_fullY_four_channel_norm(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(a:WedgeFiber)(f:ScalarTest):
    ‖embed (literalCoreResolvent F z hz (wedgeTest dual a f))‖^2=
      ∑j:Fin 4,‖embed (originalWedgeLeg F z hz dual a f j.val)‖^2:=by
  have hp(i j:Fin 4):inner ℂ (embed (originalWedgeLeg F z hz dual a f i.val))
      (embed (originalWedgeLeg F z hz dual a f j.val))=
        if i=j then (‖embed (originalWedgeLeg F z hz dual a f i.val)‖^2:ℂ) else 0:=by
    by_cases hij:i=j
    · subst j
      simp only [if_true,inner_self_eq_norm_sq_to_K]
      norm_cast
    · rw [if_neg hij]
      exact channels_orthogonal F z hz dual a f i j hij
  have h:inner ℂ (embed (literalCoreResolvent F z hz (wedgeTest dual a f)))
      (embed (literalCoreResolvent F z hz (wedgeTest dual a f)))=
      ∑j:Fin 4,(‖embed (originalWedgeLeg F z hz dual a f j.val)‖:ℂ)^2:=by
    rw [actual_fullY_four_channel_response,map_sum,sum_inner]
    simp only [inner_sum,hp]
    simp
  rw [inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_sum,Complex.ofReal_pow] using! h)

/-- The sharp kernel retains its independently generated action, which annihilates this source's actual bottom grade. -/
theorem actual_wedge_sharp_response(F:Index)(z:ℂ)(hz:z.im≠0)(dual:Bool)(a:WedgeFiber)(f:ScalarTest):
    literalSharpResolvent F z hz (wedgeTest dual a f)=resolventCore F z hz (wedgeTest dual a f):=by
  apply actual_bottom_sharp_resolvent
  apply DFunLike.ext
  intro x
  change fiberGrade (wedgeTest dual a f x)=0
  rw [actual_wedge_test_value,map_smul,actual_named_wedge_grade_zero,smul_zero]

end LowEnergy.NamedColorQtNext
