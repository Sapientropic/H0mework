import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceSupportLeakage

/-! The actual escaped channel is fed only by the original source deficiency projection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceEscapeDefectFeed
open Filter GaussCoreHilbert GaussDiagonalHistory
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion reader)
open SourceFamilyHilbert SourceFamilyOperator
open FullYSourceResolventGraphSplice SourceMinimalGraphParticular
open SourceRetardedIncrement SymmetricGraphClosure
open scoped Topology InnerProductSpace

private theorem family_eq_of_eventually (f g : Family H sourceFilter)
    (h : ∀ᶠ F in (sourceFilter : Filter Index), value f F=value g F) :
    (f : HistorySpace)=(g : HistorySpace) := by
  have hn : ‖f-g‖≤0 := norm_le_of_eventually sourceFilter (f-g) 0 (by
    filter_upwards [h] with F hF
    change ‖value f F-value g F‖≤0
    rw [hF,sub_self,norm_zero])
  apply sub_eq_zero.mp
  rw [←UniformSpace.Completion.coe_sub]
  apply norm_eq_zero.mp
  rw [UniformSpace.Completion.norm_coe]
  exact le_antisymm hn (norm_nonneg _)

private theorem resolvent_core_shift (z : ℂ) (hz : z.im≠0) (x : diagonal.domain) :
    sameResolvent z hz (inclusion (diagonal x-z • (x : H)))=inclusion (x : H) := by
  change lift sourceFilter (resolventFamily z hz)
    ((SourceFamilyHilbert.constant sourceFilter (diagonal x-z • (x : H))) : HistorySpace)=
      ((SourceFamilyHilbert.constant sourceFilter (x : H)) : HistorySpace)
  rw [lift_coe]
  apply family_eq_of_eventually
  filter_upwards [GaussGradedCompression.eventually_exact x] with F hF
  change finiteResolvent F z (diagonal x-z • (x : H))=(x : H)
  rw [←hF]
  exact congrArg (fun T : H →L[ℂ] H => T (x : H))
    (resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz)

private theorem graph_extension {E K : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup K] [NormedSpace ℂ K]
    (T : E →ₗ.[ℂ] E) (J : E →L[ℂ] K) (R : K →L[ℂ] K) (z : ℂ)
    (core : ∀ x : T.domain, R (J (T x-z • (x : E)))=J (x : E))
    {x h : E} (hx : (x,h)∈closedGraph T) : R (J (h-z • x))=J x := by
  have he : Set.EqOn
      (fun p : E×E => R (J (p.2-z • p.1)))
      (fun p : E×E => J p.1) (T.graph : Set (E×E)) := by
    intro p hp
    obtain ⟨v,hv,hact⟩ := T.mem_graph_iff.mp hp
    change (v : E)=p.1 at hv
    change T v=p.2 at hact
    change R (J (p.2-z • p.1))=J p.1
    rw [←hv,←hact]
    exact core v
  exact he.closure
    (R.continuous.comp (J.continuous.comp
      (continuous_snd.sub (continuous_fst.const_smul z))))
    (J.continuous.comp continuous_fst) hx

theorem resolvent_minimal_graph (z : ℂ) (hz : z.im≠0) {x h : H}
    (hx : (x,h)∈closedGraph diagonal) :
    sameResolvent z hz (inclusion (h-z • x))=inclusion x :=
  graph_extension diagonal inclusion.toContinuousLinearMap (sameResolvent z hz) z
    (resolvent_core_shift z hz) hx

/-- The right-input decomposition uses G_z itself, whose original minimal graph is generated. -/
theorem source_right_particular_split (z : ℂ) (hz : z.im≠0) (g : H) :
    sameResolvent z hz (inclusion g)=inclusion (sourceParticular z g)+
      sameResolvent z hz (inclusion (sourceDefect z g)) := by
  have hr := resolvent_minimal_graph z hz (source_particular_graph z hz g)
  have hs := congrArg (fun T : H →L[ℂ] H => T g) (graphAction_shift diagonal z)
  change sourceGraphAction z g-z • sourceParticular z g=g-sourceDefect z g at hs
  rw [hs,map_sub,map_sub] at hr
  exact sub_eq_iff_eq_add.mp hr

private theorem escaped_inclusion_core (x : diagonal.domain) :
    escaped (inclusion (x : H))=0 := by
  change lift sourceFilter escapeFamily
    ((SourceFamilyHilbert.constant sourceFilter (x : H)) : HistorySpace)=0
  rw [lift_coe]
  have hz : (((0 : Family H sourceFilter)) : HistorySpace)=0 :=
    UniformSpace.Completion.coe_zero
  rw [←hz]
  apply family_eq_of_eventually
  filter_upwards [source_eventually_mem_support x] with F hF
  change escapeProjection F (x : H)=0
  change (x : H)-(supportSpan F).starProjection (x : H)=0
  rw [Submodule.starProjection_eq_self_iff.mpr hF,sub_self]

theorem escaped_inclusion_zero (g : H) : escaped (inclusion g)=0 := by
  have he : Set.EqOn (fun x : H => escaped (inclusion x)) (fun _ => 0)
      (diagonal.domain : Set H) := by
    intro x hx
    exact escaped_inclusion_core ⟨x,hx⟩
  exact he.closure (escaped.continuous.comp inclusion.continuous)
    continuous_const (diagonal_dense g)

/-- This exact feed retains the same R_z, E₀, reader and original Q_z. -/
theorem escape_original_defect_feed (z : ℂ) (hz : z.im≠0)
    (A : H →L[ℂ] H) (g : H) :
    escaped (reader A (sameResolvent z hz (inclusion g)))=
      escaped (reader A
        (sameResolvent z hz (inclusion (sourceDefect z g)))) := by
  have h := congrArg (fun v : HistorySpace => escaped (reader A v))
    (source_right_particular_split z hz g)
  have hadd := (congrArg escaped ((reader A).map_add
      (inclusion (sourceParticular z g))
      (sameResolvent z hz (inclusion (sourceDefect z g))))).trans
    (escaped.map_add _ _)
  have hzero : escaped (reader A (inclusion (sourceParticular z g)))=0 :=
    (congrArg escaped (GaussUnitaryHistory.reader_inclusion A (sourceParticular z g))).trans
      (escaped_inclusion_zero _)
  exact (h.trans hadd).trans ((congrArg
    (fun v : HistorySpace => v+escaped (reader A
      (sameResolvent z hz (inclusion (sourceDefect z g))))) hzero).trans (zero_add _))

#print axioms resolvent_minimal_graph
#print axioms source_right_particular_split
#print axioms escaped_inclusion_zero
#print axioms escape_original_defect_feed
end LowEnergy.SourceEscapeDefectFeed
