import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.SourceJet
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.LeadingJet
open Complex Filter Set
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open scoped Topology BigOperators
local notation "order" => generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "bare" => generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
open NoIslandNoMagic.CanonicalRiemann.OriginalUnitXiConjugateOrderSource
open private bare_factor bare_analytic bare_nonzero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.XiConjugateOrderSource

private theorem factor_jet (a:BurnolCompletedMellinCoordinate) (j:ℕ) (atMost:j≤order a.value) :
    CoefficientJet.zetaJet j a.value=
      if j=order a.value then (j.factorial:ℂ)*bare a.value a.value else 0 := by
  have source:iteratedDeriv j riemannZeta a.value=
      iteratedDeriv j (fun z:ℂ=>(z-a.value)^order a.value*bare a.value z) a.value :=
    (bare_factor a).iteratedDeriv_eq j
  unfold CoefficientJet.zetaJet
  rw [source]
  have polynomial:AnalyticAt ℂ (fun z:ℂ=>(z-a.value)^order a.value) a.value := by fun_prop
  rw [iteratedDeriv_fun_mul polynomial.contDiffAt (bare_analytic a).contDiffAt]
  have powers (i:ℕ) : iteratedDeriv i (fun z:ℂ=>(z-a.value)^order a.value) a.value=
      if i=order a.value then (i.factorial:ℂ) else 0 := by
    rw [iteratedDeriv_comp_sub_const i (fun z:ℂ=>z^order a.value) a.value]
    dsimp only
    rw [sub_self,iteratedDeriv_fun_pow_zero]
    by_cases same:i=order a.value <;> simp only [same,ite_true,ite_false,Nat.cast_zero]
  by_cases same:j=order a.value
  · rw [if_pos same]
    rw [Finset.sum_eq_single j]
    · rw [powers,if_pos same,Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,iteratedDeriv_zero]
    · intro i member apart
      have earlier:i<order a.value:=by have := Finset.mem_range.mp member; omega
      rw [powers,if_neg earlier.ne,mul_zero,zero_mul]
    · intro absent
      exact False.elim (absent (Finset.mem_range.mpr (Nat.lt_succ_self j)))
  · rw [if_neg same]
    apply Finset.sum_eq_zero
    intro i member
    have earlier:i<order a.value:=by have := Finset.mem_range.mp member; omega
    rw [powers,if_neg earlier.ne,mul_zero,zero_mul]

def multiplicity (c:BurnolCompletedMellinCoordinate) : ℕ := order c.value
def leading (c:BurnolCompletedMellinCoordinate) : ℂ :=
  ((multiplicity c).factorial:ℂ)*bare (star c.value) (star c.value)

theorem low_zero (c:BurnolCompletedMellinCoordinate) (j:ℕ) (before:j<multiplicity c) :
    CoefficientJet.zetaJet j (star c.value)=0 := by
  have value:(barC c).value=star c.value:=rfl
  have same:=actual_original_Xi_order_conjugate c
  have earlier:j<order (barC c).value := by
    rw [value,same]
    exact before
  have paid:=factor_jet (barC c) j earlier.le
  rw [if_neg earlier.ne,value] at paid
  exact paid

theorem top_source (c:BurnolCompletedMellinCoordinate) :
    CoefficientJet.zetaJet (multiplicity c) (star c.value)=leading c := by
  have value:(barC c).value=star c.value:=rfl
  have same:=actual_original_Xi_order_conjugate c
  have atMost:multiplicity c≤order (barC c).value := by rw [value,same]; exact le_rfl
  have paid:=factor_jet (barC c) (multiplicity c) atMost
  rw [value,same,if_pos (show multiplicity c=order c.value from rfl)] at paid
  exact paid

theorem leading_ne_zero (c:BurnolCompletedMellinCoordinate) : leading c≠0 := by
  apply mul_ne_zero
  · exact_mod_cast Nat.factorial_ne_zero (multiplicity c)
  · exact bare_nonzero (barC c)

/-- The low terms remain explicit source moments; the exact-m source alone eliminates their coefficients. -/
def convolution (c:BurnolCompletedMellinCoordinate) (moments:ℕ→ℂ) (j N:ℕ) : ℂ :=
  ∑i∈Finset.range (j+1),(j.choose i:ℂ)*CoefficientJet.jet i N (star c.value)*moments (j-i)

theorem convolution_tendsto (c:BurnolCompletedMellinCoordinate) (moments:ℕ→ℂ) :
    Tendsto (fun N=>convolution c moments (multiplicity c) N) atTop
      (𝓝 (leading c*moments 0)) := by
  have positive:0<(star c.value).re:=by simpa only [Complex.star_def,Complex.conj_re] using lt_trans (by norm_num:(0:ℝ)<1/2) c.rightHalf
  have notOne:star c.value≠1:=by
    intro equal
    have re:=congrArg Complex.re equal
    simp only [Complex.star_def,Complex.conj_re,Complex.one_re] at re
    linarith [c.belowOne]
  have all:=tendsto_finsetSum (Finset.range (multiplicity c+1))
    (fun i _=>((CoefficientJet.jet_tendsto (star c.value) positive notOne i).const_mul ((multiplicity c).choose i:ℂ)).mul_const (moments (multiplicity c-i)))
  have triangle:(∑i∈Finset.range (multiplicity c+1),((multiplicity c).choose i:ℂ)*
      CoefficientJet.zetaJet i (star c.value)*moments (multiplicity c-i))=leading c*moments 0 := by
    rw [Finset.sum_eq_single (multiplicity c)]
    · rw [top_source,Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self]
    · intro i member apart
      have before:i<multiplicity c:=by have := Finset.mem_range.mp member; omega
      rw [low_zero c i before,mul_zero,zero_mul]
    · intro absent
      exact False.elim (absent (Finset.mem_range.mpr (Nat.lt_succ_self _)))
  rw [triangle] at all
  exact all

theorem low_convolution_tendsto (c:BurnolCompletedMellinCoordinate) (moments:ℕ→ℂ)
    (j:ℕ) (before:j<multiplicity c) :
    Tendsto (fun N=>convolution c moments j N) atTop (𝓝 0) := by
  have positive:0<(star c.value).re:=by simpa only [Complex.star_def,Complex.conj_re] using lt_trans (by norm_num:(0:ℝ)<1/2) c.rightHalf
  have notOne:star c.value≠1:=by
    intro equal
    have re:=congrArg Complex.re equal
    simp only [Complex.star_def,Complex.conj_re,Complex.one_re] at re
    linarith [c.belowOne]
  have all:=tendsto_finsetSum (Finset.range (j+1))
    (fun i _=>((CoefficientJet.jet_tendsto (star c.value) positive notOne i).const_mul (j.choose i:ℂ)).mul_const (moments (j-i)))
  have triangle:(∑i∈Finset.range (j+1),(j.choose i:ℂ)*CoefficientJet.zetaJet i (star c.value)*moments (j-i))=0 := by
    apply Finset.sum_eq_zero
    intro i member
    have earlier:i<multiplicity c:=by have := Finset.mem_range.mp member; omega
    rw [low_zero c i earlier,mul_zero,zero_mul]
  rw [triangle] at all
  exact all
run_cmd IO.eprintln "leading jet: original Xi multiplicity gives the nonzero triangular coefficient"

/-- Only the observer changes. The original K, paired action, and both original B columns stay fixed. -/
def fixedMoment (c:BurnolCompletedMellinCoordinate) (j:ℕ) : ℂ :=
  inner ℂ (SourceJet.column (barC c) j) (OriginalKPairedBEulerJunctionSource.sourceSecond c)
def sigma0 (c:BurnolCompletedMellinCoordinate) : ℂ :=
  -2*OriginalWholeDebtRAdjointContactSource.sigma c c

/-- This is the literal whole finite source read, with both means and its actual outside field removed explicitly. -/
def fixedWholeRead (c:BurnolCompletedMellinCoordinate) (j N:ℕ) : ℂ :=
  inner ℂ (SourceJet.wholeParticle (barC c) j N) (OriginalKPairedBEulerJunctionSource.sourceAction c)-
  SourceJet.wholeInventory (barC c) j N (OriginalKPairedBEulerJunctionSource.sourceAction c)-
  inner ℂ (SourceJet.logSource (barC c) j+
    rankSource (burnolMeanZeroTruncatedFourier (SourceJet.first (barC c) j)))
    (OriginalKPairedBEulerJunctionSource.sourceSecond c)+
  inner ℂ (oppositeSource (N+1) (SourceJet.first (barC c) j))
    (OriginalKPairedBEulerJunctionSource.sourceFirst c)

/-- The Γ observer word includes the linear sigma factor's complete 1-jet. -/
def jointSource (c:BurnolCompletedMellinCoordinate) (j N:ℕ) : ℂ :=
  sigma0 c*fixedWholeRead c j N-(2*(j:ℂ))*fixedWholeRead c (j-1) N
/-- Every lower observer moment remains a separate log-power source read. -/
def gammaMoment (c:BurnolCompletedMellinCoordinate) (j:ℕ) : ℂ :=
  sigma0 c*fixedMoment c j-(2*(j:ℂ))*fixedMoment c (j-1)

theorem fixedMoment_zero (c:BurnolCompletedMellinCoordinate) :
    fixedMoment c 0=OriginalWholeDebtRJointMobiusContactClosureSource.finitePrice c c := by
  have column:SourceJet.column (barC c) 0=SingularCounting.centeredPower (barC c) := by
    simp only [SourceJet.column,SourceJet.rawColumn,SourceJet.logCoefficient,
      Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
      Nat.cast_one,Nat.sub_self,pow_zero,mul_one,Nat.factorial_zero,zero_add,one_smul,
      OriginalKFiniteOrderRelease.UnitPowerJordanSource.dividedLogColumn]
    rfl
  rw [fixedMoment,column]
  rfl

theorem gammaMoment_zero (c:BurnolCompletedMellinCoordinate) :
    gammaMoment c 0=OriginalWholeDebtRJointMobiusContactClosureSource.coefficient c c := by
  rw [gammaMoment,fixedMoment_zero]
  simp only [Nat.cast_zero,mul_zero,zero_mul,sub_zero]
  rfl

/-- All finite counterterms are generated before this equality recognizes their fixed original B read. -/
theorem fixed_whole_source (c:BurnolCompletedMellinCoordinate) (j N:ℕ) :
    fixedWholeRead c j N=convolution c (fixedMoment c) j N := by
  have whole:=SourceJet.complete_counted_read (barC c) j N (OriginalKPairedBEulerJunctionSource.sourceAction c)
  have firstRead:burnolAmbientMeanZeroFirstCorrection (OriginalKPairedBEulerJunctionSource.sourceAction c)=
      OriginalKPairedBEulerJunctionSource.sourceFirst c:=rfl
  have secondRead:burnolAmbientMeanZeroSecondCorrection (OriginalKPairedBEulerJunctionSource.sourceAction c)=
      OriginalKPairedBEulerJunctionSource.sourceSecond c:=rfl
  rw [firstRead,secondRead] at whole
  have extraction:fixedWholeRead c j N=
      SourceJet.countedRead (barC c) j N (OriginalKPairedBEulerJunctionSource.sourceAction c) := by
    unfold fixedWholeRead
    linear_combination whole
  rw [extraction,SourceJet.counted_read_source]
  have value:(barC c).value=star c.value:=rfl
  rw [value]
  rfl

/-- Exact finite all-order Leibniz source equation: no lower jet or sigma cross term is omitted. -/
theorem joint_source_equation (c:BurnolCompletedMellinCoordinate) (j N:ℕ) :
    jointSource c j N=sigma0 c*convolution c (fixedMoment c) j N-
      (2*(j:ℂ))*convolution c (fixedMoment c) (j-1) N := by
  rw [jointSource,fixed_whole_source,fixed_whole_source]

private theorem leibniz_convolution (c:BurnolCompletedMellinCoordinate) (moments:ℕ→ℂ) (j N:ℕ) :
    sigma0 c*convolution c moments j N-(2*(j:ℂ))*convolution c moments (j-1) N=
      convolution c (fun k=>sigma0 c*moments k-(2*(k:ℂ))*moments (k-1)) j N := by
  cases j with
  | zero => simp only [convolution,Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_self,Nat.cast_zero,mul_zero,zero_mul,sub_zero,zero_add]; ring
  | succ j =>
    unfold convolution
    simp only [Nat.add_sub_cancel]
    rw [Finset.mul_sum,Finset.mul_sum]
    have expansion:(∑i∈Finset.range (j+1+1),((j+1).choose i:ℂ)*CoefficientJet.jet i N (star c.value)*
        (sigma0 c*moments (j+1-i)-(2*((j+1-i:ℕ):ℂ))*moments (j+1-i-1)))=
        (∑i∈Finset.range (j+1+1),sigma0 c*(((j+1).choose i:ℂ)*CoefficientJet.jet i N (star c.value)*moments (j+1-i)))-
        ∑i∈Finset.range (j+1+1),((j+1).choose i:ℂ)*((j+1-i:ℕ):ℂ)*
          (2*CoefficientJet.jet i N (star c.value)*moments (j+1-i-1)) := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [expansion]
    congr 1
    rw [Finset.sum_range_succ (f:=fun i=>((j+1).choose i:ℂ)*((j+1-i:ℕ):ℂ)*
      (2*CoefficientJet.jet i N (star c.value)*moments (j+1-i-1)))]
    simp only [Nat.sub_self,Nat.cast_zero,mul_zero,zero_mul,add_zero]
    apply Finset.sum_congr rfl
    intro i member
    have choose:((j+1).choose i:ℂ)*((j+1-i:ℕ):ℂ)=(j.choose i:ℂ)*((j+1:ℕ):ℂ) := by
      exact_mod_cast (Nat.choose_mul_succ_eq j i).symm
    rw [choose,show j+1-i-1=j-i by omega]
    push_cast
    ring

theorem joint_source_all_j (c:BurnolCompletedMellinCoordinate) (j N:ℕ) :
    jointSource c j N=convolution c (gammaMoment c) j N := by
  rw [joint_source_equation,leibniz_convolution]
  rfl

/-- The original exact Xi multiplicity leaves a nonzero coefficient multiplying the original fixed Γ. -/
theorem actual_joint_source_tendsto (c:BurnolCompletedMellinCoordinate) :
    Tendsto (fun N=>jointSource c (multiplicity c) N) atTop
      (𝓝 (leading c*OriginalWholeDebtRJointMobiusContactClosureSource.coefficient c c)) := by
  have generated:=convolution_tendsto c (gammaMoment c)
  rw [gammaMoment_zero] at generated
  exact generated.congr' (Eventually.of_forall (fun N=>(joint_source_all_j c (multiplicity c) N).symm))

/-- The completed source identifies Γ from its own computed scalar limit, without a Γ-valued constructor input. -/
theorem actual_fixed_gamma_readback (c:BurnolCompletedMellinCoordinate) :
    Tendsto (fun N=>(leading c)⁻¹*jointSource c (multiplicity c) N) atTop
      (𝓝 (OriginalWholeDebtRJointMobiusContactClosureSource.coefficient c c)) := by
  have source:=(actual_joint_source_tendsto c).const_mul (leading c)⁻¹
  simpa only [←mul_assoc,inv_mul_cancel₀ (leading_ne_zero c),one_mul] using source
run_cmd IO.eprintln "leading jet: actual complete whole source has nondecaying leading times the original fixed Gamma"
end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur.LeadingJet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env=>Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CountedSchur.LeadingJet"
