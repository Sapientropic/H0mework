import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCompressionShape

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualMixedCompressionShape
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open GaussUnitaryHistory SourceScalarVirialBulk SourceScalarGaugeScale
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped InnerProductSpace BigOperators Topology
open Lean Meta Elab Term
abbrev Op := H →L[ℂ] H

elab "paid_scalar_rank_derivative%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarCompressionJet 0) "LowEnergy")
    "ActualScalarCompressionJet") "rank_jet_derivative")
elab "paid_gauge_rank_derivative%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceGaugeScaleTransport 0) "LowEnergy")
    "SourceGaugeScaleTransport") "rank_jet_derivative")

elab "paid_source_conjugate_rank%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarCompressionJet 0) "LowEnergy")
    "ActualScalarCompressionJet") "conjugate_rank")

abbrev SpanIndex (F : Index) := Fin (Module.finrank ℂ (FiniteCoreEvolution.coreSpan diagonal F))
def spanBasis (F : Index) := stdOrthonormalBasis ℂ (FiniteCoreEvolution.coreSpan diagonal F)
def spanTest (F : Index) (i : SpanIndex F) : QuantumTest :=
  coreEquiv.symm ⟨(spanBasis F i : H),FiniteCoreEvolution.coreSpan_le diagonal F (spanBasis F i).property⟩

@[simp] theorem actual_span_test_embed (F : Index) (i : SpanIndex F) :
    embed (spanTest F i)=(spanBasis F i : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

attribute [local irreducible] spanBasis spanTest projectionCore GaussCoreHilbert.embed

/-- The paid scalar strong jet, on the original ungraded finite span rather than its grade closure. -/
def scalarProjectionJet (F : Index) (n : ℕ) (t : ℝ) : Op :=
  ∑ i : SpanIndex F, ActualScalarCompressionJet.rankJet n 0 0 (spanTest F i) (spanTest F i) t

def gaugeProjectionJet (F : Index) (n : ℕ) (t : ℝ) : Op :=
  ∑ i : SpanIndex F, SourceGaugeScaleTransport.rankJet n 0 0 (spanTest F i) (spanTest F i) t

theorem actual_scalar_projection_derivative (F : Index) (n : ℕ) (t : ℝ) :
    HasDerivAt (scalarProjectionJet F n) (scalarProjectionJet F (n+1) t) t := by
  unfold scalarProjectionJet
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (paid_scalar_rank_derivative%) n 0 0 (spanTest F i) (spanTest F i) t) using 1
  funext s
  simp only [Finset.sum_apply]

theorem actual_gauge_projection_derivative (F : Index) (n : ℕ) (t : ℝ) :
    HasDerivAt (gaugeProjectionJet F n) (gaugeProjectionJet F (n+1) t) t := by
  unfold gaugeProjectionJet
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (paid_gauge_rank_derivative%) n 0 0 (spanTest F i) (spanTest F i) t) using 1
  funext s
  simp only [Finset.sum_apply]

theorem actual_scalar_projection_orbit (F : Index) (t : ℝ) :
    scalarProjectionJet F 0 t=(SourceScalarAffineScaleTransport.hilbertFlow t).conjStarAlgEquiv
      (FiniteCoreEvolution.coreSpan diagonal F).starProjection := by
  have hp := congrArg (SourceScalarAffineScaleTransport.hilbertFlow t).conjStarAlgEquiv
    (spanBasis F).starProjection_eq_sum_rankOne
  rw [map_sum] at hp
  change (∑ i : SpanIndex F, ActualScalarCompressionJet.rankJet 0 0 0 (spanTest F i) (spanTest F i) t)=_
  apply Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) hp.symm
  change InnerProductSpace.rankOne ℂ
    (embed (SourceScalarAffineScaleTransport.coreFlow t (spanTest F i)))
    (embed (SourceScalarAffineScaleTransport.coreFlow t (spanTest F i)))=_
  have he : embed (SourceScalarAffineScaleTransport.coreFlow t (spanTest F i))=
      SourceScalarAffineScaleTransport.hilbertFlow t (spanBasis F i : H) :=
    (SourceScalarAffineScaleTransport.hilbertFlow_on_core t (spanTest F i)).symm.trans
      (congrArg (SourceScalarAffineScaleTransport.hilbertFlow t) (actual_span_test_embed F i))
  exact (congrArg₂ (fun x y : H => InnerProductSpace.rankOne ℂ x y) he he).trans
    ((paid_source_conjugate_rank%) (SourceScalarAffineScaleTransport.hilbertFlow t)
      (spanBasis F i : H) (spanBasis F i : H)).symm

theorem actual_gauge_projection_orbit (F : Index) (t : ℝ) :
    gaugeProjectionJet F 0 t=(SourceGaugeScaleTransport.hilbertFlow t).conjStarAlgEquiv
      (FiniteCoreEvolution.coreSpan diagonal F).starProjection := by
  have hp := congrArg (SourceGaugeScaleTransport.hilbertFlow t).conjStarAlgEquiv
    (spanBasis F).starProjection_eq_sum_rankOne
  rw [map_sum] at hp
  change (∑ i : SpanIndex F, SourceGaugeScaleTransport.rankJet 0 0 0 (spanTest F i) (spanTest F i) t)=_
  apply Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) hp.symm
  change InnerProductSpace.rankOne ℂ
    (embed (SourceGaugeScaleTransport.coreFlow t (spanTest F i)))
    (embed (SourceGaugeScaleTransport.coreFlow t (spanTest F i)))=_
  have he : embed (SourceGaugeScaleTransport.coreFlow t (spanTest F i))=
      SourceGaugeScaleTransport.hilbertFlow t (spanBasis F i : H) :=
    (SourceGaugeScaleTransport.hilbertFlow_on_core t (spanTest F i)).symm.trans
      (congrArg (SourceGaugeScaleTransport.hilbertFlow t) (actual_span_test_embed F i))
  exact (congrArg₂ (fun x y : H => InnerProductSpace.rankOne ℂ x y) he he).trans
    ((paid_source_conjugate_rank%) (SourceGaugeScaleTransport.hilbertFlow t)
      (spanBasis F i : H) (spanBasis F i : H)).symm

private theorem projection_rank_core (F : Index) (f : QuantumTest) :
    projectionCore F f=∑ i : SpanIndex F, inner ℂ (spanBasis F i : H) (embed f) • spanTest F i := by
  apply embed_injective
  simp only [map_sum,map_smul,actual_span_test_embed,actual_projection_core_embed]
  rw [(spanBasis F).starProjection_eq_sum_rankOne]
  simp only [sum_apply,InnerProductSpace.rankOne_apply]

private theorem scalar_skew (f g : QuantumTest) :
    sourcePair f (SourceScalarAffineScaleTransport.generator g)=
      -sourcePair (SourceScalarAffineScaleTransport.generator f) g := by
  have h := (SourceScalarAffineScaleTransport.strong_core_derivative f 0).inner ℂ
    (SourceScalarAffineScaleTransport.strong_core_derivative g 0)
  have ht : HasDerivAt (fun t => sourcePair (SourceScalarAffineScaleTransport.coreFlow t f)
      (SourceScalarAffineScaleTransport.coreFlow t g))
      (sourcePair f (SourceScalarAffineScaleTransport.generator g)+
        sourcePair (SourceScalarAffineScaleTransport.generator f) g) 0 := by
    simpa only [sourcePair,SourceScalarAffineScaleTransport.coreFlow_zero] using! h
  have hc := ht.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun t => (SourceScalarAffineScaleTransport.coreFlow_pair t f g).symm))
  exact eq_neg_of_add_eq_zero_left (hc.unique (hasDerivAt_const 0 (sourcePair f g)))

private theorem gauge_skew (f g : QuantumTest) :
    sourcePair f (SourceGaugeScaleTransport.generator g)=
      -sourcePair (SourceGaugeScaleTransport.generator f) g := by
  have h := (SourceGaugeScaleTransport.strong_core_derivative f 0).inner ℂ
    (SourceGaugeScaleTransport.strong_core_derivative g 0)
  have ht : HasDerivAt (fun t => sourcePair (SourceGaugeScaleTransport.coreFlow t f)
      (SourceGaugeScaleTransport.coreFlow t g))
      (sourcePair f (SourceGaugeScaleTransport.generator g)+
        sourcePair (SourceGaugeScaleTransport.generator f) g) 0 := by
    simpa only [sourcePair,SourceGaugeScaleTransport.coreFlow_zero] using! h
  have hc := ht.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun t => (SourceGaugeScaleTransport.coreFlow_pair t f g).symm))
  exact eq_neg_of_add_eq_zero_left (hc.unique (hasDerivAt_const 0 (sourcePair f g)))

private theorem finite_rank_commutator {V E ι : Type*}
    [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]
    (e : V →ₗ[ℂ] E) (G P : V →ₗ[ℂ] V) (v : ι → V)
    (hP : ∀ f, P f=∑ i, inner ℂ (e (v i)) (e f) • v i)
    (hG : ∀ f g, inner ℂ (e f) (e (G g))= -inner ℂ (e (G f)) (e g)) (f : V) :
    e ((G*P-P*G) f)=
      (∑ i, (InnerProductSpace.rankOne ℂ (e (G (v i))) (e (v i))+
        InnerProductSpace.rankOne ℂ (e (v i)) (e (G (v i))))) (e f) := by
  change e (G (P f)-P (G f))=_
  rw [map_sub,hP f,hP (G f)]
  simp only [map_sum,map_smul,map_neg,sum_apply,add_apply,InnerProductSpace.rankOne_apply,
    Finset.sum_add_distrib,hG,neg_smul,Finset.sum_neg_distrib,sub_neg_eq_add]

private theorem rank_core_commutator (F : Index) (G : End)
    (hG : ∀ f g, sourcePair f (G g)= -sourcePair (G f) g) (f : QuantumTest) :
    embed ((G*projectionCore F-projectionCore F*G) f)=
      (∑ i : SpanIndex F, (InnerProductSpace.rankOne ℂ (embed (G (spanTest F i))) (spanBasis F i : H)+
        InnerProductSpace.rankOne ℂ (spanBasis F i : H) (embed (G (spanTest F i))))) (embed f) := by
  have hp (q : QuantumTest) : projectionCore F q=
      ∑ i : SpanIndex F, inner ℂ (embed (spanTest F i)) (embed q) • spanTest F i := by
    simpa only [actual_span_test_embed] using projection_rank_core F q
  have hg (q r : QuantumTest) : inner ℂ (embed q) (embed (G r))=
      -inner ℂ (embed (G q)) (embed r) := hG q r
  simpa only [actual_span_test_embed] using
    finite_rank_commutator embed G (projectionCore F) (spanTest F) hp hg f

/-- The actual scalar moving projection jet is exactly the core shape derivative. -/
theorem actual_scalar_projection_jet_core (F : Index) (f : QuantumTest) :
    embed (deltaPhi (projectionCore F) f)=scalarProjectionJet F 1 0 (embed f) := by
  rw [←SourceScalarAffineScaleTransport.generator_commutator]
  simpa only [scalarProjectionJet,ActualScalarCompressionJet.rankJet,SourceScalarAffineScaleTransport.strongJet,
    Nat.zero_add,pow_one,pow_zero,Module.End.one_apply,SourceScalarAffineScaleTransport.coreFlow_zero,
    actual_span_test_embed] using rank_core_commutator F _ scalar_skew f

/-- Gauge and scalar use the same original finite span and retain the literal source normalization. -/
theorem actual_gauge_projection_jet_core (F : Index) (f : QuantumTest) :
    embed (deltaGauge (projectionCore F) f)=gaugeProjectionJet F 1 0 (embed f) := by
  rw [←SourceGaugeScaleTransport.generator_commutator]
  simpa only [gaugeProjectionJet,SourceGaugeScaleTransport.rankJet,SourceGaugeScaleTransport.strongJet,
    Nat.zero_add,pow_one,pow_zero,Module.End.one_apply,SourceGaugeScaleTransport.coreFlow_zero,
    actual_span_test_embed] using rank_core_commutator F _ gauge_skew f

end LowEnergy.ActualMixedCompressionShape
