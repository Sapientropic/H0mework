import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceGaugeCoframeJets
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceJointScaleBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.SourceInverseFirstCurrentInputEscape
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceGaugeCoframeJets SourceJointScaleBudget SourceRetardedIncrement
open FullYSourceResolventGraphSplice Filter
/-- The actual retarded state stays in its source input span at every nonreal frequency. -/
theorem actual_input_escape_zero (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    (1-(inputSpan F g).starProjection) (finiteResolvent F z (g : H))=0 := by
  change finiteResolvent F z (g : H)-(inputSpan F g).starProjection (finiteResolvent F z (g : H))=0
  rw [Submodule.starProjection_eq_self_iff.mpr (resolvent_input_span F z hz g),sub_self]

/-- One source-generated compression threshold precedes every frequency and every left or middle reader;
    only the two fixed right gauge derivatives enter its support requirement. -/
theorem actual_gauge_prefix_escape_zero (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ z : ℂ,∀ _hz : z.im≠0,∀ A : H →L[ℂ] H,∀ k : H,
      ∀ j : Fin 3,
      inner ℂ k ((finiteResolvent F z*A*(1-(inputSpan F g).starProjection)*
        finiteResolvent F z) (embed ((G^j.val) (coreEquiv.symm g))))=0 := by
  filter_upwards [source_eventually_mem_support (coreEquiv (G (coreEquiv.symm g))),
    source_eventually_mem_support (coreEquiv (G (G (coreEquiv.symm g))))] with F h1 h2 z hz A k j
  change embed (G (coreEquiv.symm g))∈supportSpan F at h1
  change embed (G (G (coreEquiv.symm g)))∈supportSpan F at h2
  have hbase : embed (coreEquiv.symm g)=(g : H) := congrArg Subtype.val (coreEquiv.apply_symm_apply g)
  have hzero (u : QuantumTest) (hu : embed u∈supportSpan F) :
      (1-(inputSpan F g).starProjection) (finiteResolvent F z (embed u))=0 := by
    have hmem : finiteResolvent F z (embed u)∈inputSpan F g :=
      Submodule.mem_sup_left (resolvent_mem_support F z hz (embed u) hu)
    change finiteResolvent F z (embed u)-(inputSpan F g).starProjection
      (finiteResolvent F z (embed u))=0
    rw [Submodule.starProjection_eq_self_iff.mpr hmem,sub_self]
  have hh : (1-(inputSpan F g).starProjection)
      (finiteResolvent F z (embed ((G^j.val) (coreEquiv.symm g))))=0 := by
    fin_cases j
    · simpa only [Fin.val_zero,pow_zero,Module.End.one_apply,hbase] using actual_input_escape_zero F g z hz
    · simpa only [pow_one] using hzero (G (coreEquiv.symm g)) h1
    · simpa only [pow_two,Module.End.mul_apply] using hzero (G (G (coreEquiv.symm g))) h2
  change inner ℂ k (finiteResolvent F z (A ((1-(inputSpan F g).starProjection)
    (finiteResolvent F z (embed ((G^j.val) (coreEquiv.symm g)))))))=0
  rw [hh,map_zero,map_zero,inner_zero_right]
end LowEnergy.SourceInverseFirstCurrentInputEscape
