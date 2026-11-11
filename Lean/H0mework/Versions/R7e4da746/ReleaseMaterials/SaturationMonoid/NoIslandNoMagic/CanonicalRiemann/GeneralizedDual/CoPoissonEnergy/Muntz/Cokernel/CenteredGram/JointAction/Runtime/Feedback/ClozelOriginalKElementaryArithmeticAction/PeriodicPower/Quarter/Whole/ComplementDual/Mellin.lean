import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.PowerPrice

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mellin
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPower
open scoped Topology InnerProductSpace
open private log_top_bound logSource_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
open private compact_mellin_read from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ComplementMoment
open private mellin_source_ae from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.ResolventSource
local notation "q" => (1/4:ℝ)

private theorem origin_bound (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    fullFloorRaw c=O[𝓝[>] 0](fun x:ℝ=>x^(-(0:ℝ))):=by
  obtain ⟨B,_,bound⟩:=actual_full_floor_bound c zero
  apply Asymptotics.IsBigO.of_bound B
  filter_upwards with x
  simpa only [neg_zero,Real.rpow_zero,norm_one,mul_one] using bound x

private theorem log_origin_bound (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (j:ℕ) (b:ℝ) (positive:0<b):
    logSource (fullFloorRaw c) j=O[𝓝[>] 0](fun x:ℝ=>x^(-b)):=by
  have logarithm:(fun x:ℝ=>(Real.log x)^j)=O[𝓝[>] 0](fun x:ℝ=>x^(-b)):=by
    apply Asymptotics.IsBigO.of_norm_left
    simpa only [Real.norm_eq_abs,abs_pow,Real.rpow_natCast] using
      (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (j:ℝ) (by linarith:-b<0)).isBigO
  have product:=logarithm.smul (origin_bound c zero)
  apply product.congr' (EventuallyEq.refl _ _)
  filter_upwards with x
  change x^(-b)*x^(-(0:ℝ))=x^(-b)
  simp

private theorem log_local (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (j:ℕ):
    LocallyIntegrableOn (logSource (fullFloorRaw c) j) (Ioi 0):=by
  have logarithm:ContinuousOn (fun x:ℝ=>(Real.log x)^j) (Ioi 0):=by
    intro x positive
    exact ((Real.continuousAt_log positive.ne').pow j).continuousWithinAt
  exact LocallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed
    (((actual_full_floor_memLp c zero).locallyIntegrable (by norm_num)).locallyIntegrableOn _) logarithm

/-- The full unweighted counting field supplies every logarithmic Mellin domain on the positive half-plane. -/
theorem actual_floor_log_mellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (j:ℕ) (z:ℂ) (positive:0<z.re):MellinConvergent (logSource (fullFloorRaw c) j) z:=
  mellinConvergent_of_isBigO_rpow (log_local c zero j)
    (log_top_bound (fullFloorRaw c) q (actual_floor_outer_zero c.value c.belowOne) j (z.re+1))
    (by linarith) (log_origin_bound c zero j (z.re/2) (by linarith)) (by linarith)

theorem actual_floor_hasMellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (z:ℂ) (positive:0<z.re):
    HasMellin (fullFloorValue c zero:ℝ→ℂ) z (mellin (fullFloorRaw c) z):=
  mellin_source_ae _ _ _ _ (ae_restrict_of_ae (actual_full_floor_raw c zero))
    ⟨by simpa only [logSource_zero] using actual_floor_log_mellin c zero 0 z positive,rfl⟩

theorem actual_floor_log_derivative (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (j:ℕ) (z:ℂ) (positive:0<z.re):
    HasDerivAt (mellin (logSource (fullFloorRaw c) j))
      (mellin (logSource (fullFloorRaw c) (j+1)) z) z:=by
  have source:=(mellin_hasDerivAt_of_isBigO_rpow (log_local c zero j)
    (log_top_bound (fullFloorRaw c) q (actual_floor_outer_zero c.value c.belowOne) j (z.re+1))
    (by linarith : z.re<z.re+1) (log_origin_bound c zero j (z.re/2) (by linarith))
    (by linarith : z.re/2<z.re)).2
  have field:(fun x:ℝ=>Real.log x • logSource (fullFloorRaw c) j x)=logSource (fullFloorRaw c) (j+1):=by
    funext x
    simp only [logSource,smul_smul,pow_succ,mul_comm]
  rwa [field] at source

theorem actual_floor_iterated_mellin (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (j:ℕ) (z:ℂ) (positive:0<z.re):
    iteratedDeriv j (mellin (fullFloorRaw c)) z=mellin (logSource (fullFloorRaw c) j) z:=by
  induction j generalizing z with
  | zero => simp only [iteratedDeriv_zero,logSource_zero]
  | succ j previous =>
    rw [iteratedDeriv_succ]
    have same:iteratedDeriv j (mellin (fullFloorRaw c))=ᶠ[𝓝 z]
        mellin (logSource (fullFloorRaw c) j):=by
      filter_upwards [isOpen_lt continuous_const continuous_re |>.mem_nhds positive] with u inside
      exact previous u inside
    rw [same.deriv_eq]
    exact (actual_floor_log_derivative c zero j z positive).deriv

private theorem ordinary_log_read (c:BurnolCompletedMellinCoordinate) (j:ℕ) (z:ℂ):
    mellin (logSource (fullFloorRaw c) j) z=
      ∫x:ℝ in (0:ℝ)..q,(x:ℂ)^(z-1)*(Real.log x:ℂ)^j*fullFloorRaw c x:=by
  have compact:OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin.compactRaw (fullFloorRaw c)=fullFloorRaw c:=by
    funext x
    by_cases inside:x∈symmetricInterval q
    · exact indicator_of_mem inside _
    · rw [OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin.compactRaw,indicator_of_notMem inside]
      exact (actual_floor_outer_zero c.value c.belowOne x
        (lt_of_not_ge (fun bounded=>inside (abs_le.mp bounded)))).symm
  have source:=compact_mellin_read (fullFloorRaw c) (1-z) j
  rw [compact,show 1-(1-z)=z by ring] at source
  simpa only [OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ComplementMoment.quarterMoment,
    OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ComplementMoment.logWeight,show -(1-z)=z-1 by ring] using source

private theorem ordinary_log_domain (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (j:ℕ) (z:ℂ) (positive:0<z.re):
    IntervalIntegrable (fun x:ℝ=>(x:ℂ)^(z-1)*(Real.log x:ℂ)^j*fullFloorRaw c x) volume 0 q:=by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤q)]
  have domain:=actual_floor_log_mellin c zero j z positive
  change IntegrableOn (fun x:ℝ=>(x:ℂ)^(z-1) • logSource (fullFloorRaw c) j x) (Ioi 0) at domain
  apply (domain.mono_set Ioc_subset_Ioi_self).congr
  filter_upwards with x
  simp only [logSource,smul_eq_mul,Complex.real_smul,Complex.ofReal_pow]
  ring

/-- The actual quarter log bank is the complete finite combination of the same source Mellin jets. -/
theorem actual_log_moment_jet (c d:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (k:ℕ):
    logMoment d k (fullFloorRaw c)=
      ∑j∈Finset.range (k+1),(k.choose j:ℂ)*(Real.log q:ℂ)^(k-j)*(-1:ℂ)^j*
        iteratedDeriv j (mellin (fullFloorRaw c)) d.value:=by
  have positive:0<d.value.re:=by linarith [d.rightHalf]
  let a:ℕ→ℂ:=fun j=>(k.choose j:ℂ)*(Real.log q:ℂ)^(k-j)*(-1:ℂ)^j
  have expansion:(∫x:ℝ in (0:ℝ)..q,(x:ℂ)^(d.value-1)*(Real.log (q/x):ℂ)^k*fullFloorRaw c x)=
      ∫x:ℝ in (0:ℝ)..q,∑j∈Finset.range (k+1),
        a j*((x:ℂ)^(d.value-1)*(Real.log x:ℂ)^j*fullFloorRaw c x):=by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x inside
    dsimp only
    rw [Real.log_div (by norm_num : q≠0) inside.1.ne',Complex.ofReal_sub,
      show (Real.log q:ℂ)-(Real.log x:ℂ)=-(Real.log x:ℂ)+(Real.log q:ℂ) by ring,
      add_pow,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j member
    rw [neg_pow]
    dsimp only [a]
    ring
  rw [logMoment,expansion,intervalIntegral.integral_finsetSum
    (fun j _=>(ordinary_log_domain c zero j d.value positive).const_mul (a j))]
  apply Finset.sum_congr rfl
  intro j member
  rw [intervalIntegral.integral_const_mul,←ordinary_log_read,
    actual_floor_iterated_mellin c zero j d.value positive]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
