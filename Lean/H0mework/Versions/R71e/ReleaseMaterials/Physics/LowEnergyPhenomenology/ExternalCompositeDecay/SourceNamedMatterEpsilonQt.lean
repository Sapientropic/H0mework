import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterEpsilonGram
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterWedgeResponse
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussDensityCore GaussUnitaryHistory
open SaturationMonoid.PhysicsCore QuantizationCheck.Fermion NamedMatterWedgeQt
open FullYDynamicSource FullYDynamicResponse CompositeFullYBorn
open MeasureTheory
open scoped BigOperators InnerProductSpace ContDiff ENNReal
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=SourceRealScalarFock.branchOrder.toDecidableEq

def termIndex(s:SpinTriple)(p:Fin 6):WedgeIndex:=
  ⟨{(s.val 0,colorPerm p 0),(s.val 1,colorPerm p 1),(s.val 2,colorPerm p 2)},by
    fin_cases p <;> simp [colorPerm,Prod.mk.injEq]⟩
def termPhase(dual:Bool)(s:SpinTriple)(p:Fin 6):ℂ:=
  sign (rootMode dual (s.val 1,colorPerm p 1)) {rootMode dual (s.val 2,colorPerm p 2)}*
  sign (rootMode dual (s.val 0,colorPerm p 0))
    {rootMode dual (s.val 1,colorPerm p 1),rootMode dual (s.val 2,colorPerm p 2)}

private def wedgeLinear(dual:Bool):WedgeFiber→ₗ[ℂ]FockFiber where
  toFun:=wedgeFiber dual
  map_add' a b:=by
    simp only [wedgeFiber,PiLp.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c a:=by
    simp only [wedgeFiber,PiLp.smul_apply,smul_eq_mul,smul_smul,Finset.smul_sum,RingHom.id_apply]

private theorem wedge_single(dual:Bool)(w:WedgeIndex):
    wedgeLinear dual (EuclideanSpace.single w 1)=fiberBasis dual w:=by
  classical
  change wedgeFiber dual (EuclideanSpace.single w 1)=_
  simp only [wedgeFiber,PiLp.single_apply,ite_smul,one_smul,zero_smul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- Coefficients carry the actual mother-order CAR phase, never a chosen order on 504 modes. -/
def epsilonCoordinates(dual:Bool)(s:SpinTriple):WedgeFiber:=
  (epsilonScale s:ℂ)⁻¹ • ∑p:Fin 6,(colorSign p*termPhase dual s p) • EuclideanSpace.single (termIndex s p) 1

theorem actual_epsilon_coordinates_return(dual:Bool)(s:SpinTriple):
    wedgeFiber dual (epsilonCoordinates dual s)=normalizedEpsilon dual s:=by
  change wedgeLinear dual (epsilonCoordinates dual s)=_
  rw [epsilonCoordinates,map_smul,map_sum,normalizedEpsilon,epsilonFiber]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [map_smul,wedge_single,actual_epsilon_term_source,smul_smul]
  have hf:fiberBasis dual (termIndex s p)=occupationFiber dual
      {(s.val 0,colorPerm p 0),(s.val 1,colorPerm p 1),(s.val 2,colorPerm p 2)}:=by
    apply PiLp.ext
    intro v
    simp [fiberBasis,occupationFiber,termIndex,EuclideanSpace.single]
  rw [hf]
  rfl

theorem actual_epsilon_coordinates_pair(dual:Bool)(s t:SpinTriple):
    inner ℂ (epsilonCoordinates dual s) (epsilonCoordinates dual t)=if s=t then 1 else 0:=by
  rw [←actual_wedge_fiber_pair dual,actual_epsilon_coordinates_return,actual_epsilon_coordinates_return]
  exact actual_normalized_epsilon_pair dual s t

abbrev Epsilon20:=EuclideanSpace ℂ SpinTriple
def epsilon20Coordinates(dual:Bool)(a:Epsilon20):WedgeFiber:=
  ∑s:SpinTriple,a s • epsilonCoordinates dual s

theorem actual_epsilon20_coordinates_pair(dual:Bool)(a b:Epsilon20):
    inner ℂ (epsilon20Coordinates dual a) (epsilon20Coordinates dual b)=inner ℂ a b:=by
  classical
  simp only [epsilon20Coordinates,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    actual_epsilon_coordinates_pair,starRingEnd_apply]
  simp [mul_ite,PiLp.inner_apply,RCLike.inner_apply,mul_comm]

def epsilon20Test(dual:Bool)(a:Epsilon20)(f:ScalarTest):QuantumTest:=
  wedgeTest dual (epsilon20Coordinates dual a) f

/-- The normalized twenty-column epsilon source enters the actual Number-three weighted μ₀ pairing. -/
theorem actual_epsilon20_source_pair(dual:Bool)(a b:Epsilon20)(f g:ScalarTest):
    sourcePair (epsilon20Test dual a f) (epsilon20Test dual b g)=
      inner ℂ a b*GaussDensityCore.pair 3 f g:=by
  rw [epsilon20Test,epsilon20Test,actual_wedge_source_pair,actual_epsilon20_coordinates_pair]

theorem actual_epsilon20_source_norm(dual:Bool)(a:Epsilon20)(f:ScalarTest):
    ‖embed (epsilon20Test dual a f)‖=‖a‖*‖scalarLp 3 f‖:=by
  rw [epsilon20Test,actual_wedge_source_norm]
  have h:=actual_epsilon20_coordinates_pair dual a a
  have he:‖epsilon20Coordinates dual a‖=‖a‖:=by
    have hs:‖epsilon20Coordinates dual a‖^2=‖a‖^2:=by
      simp only [inner_self_eq_norm_sq_to_K] at h
      exact_mod_cast h
    nlinarith [norm_nonneg (epsilon20Coordinates dual a),norm_nonneg a]
  rw [he]

attribute [local irreducible] embed literalCoreResolvent literalSharpResolvent epsilon20Test

theorem actual_epsilon20_response_measure(F:Index)(dual sharp advanced:Bool)
    (a:Epsilon20)(f:ScalarTest)(μ:ℝ)(hμ:0<μ):
    Integrable (fun w:ℝ=>‖embed (literalResponse F sharp (epsilon20Test dual a f) advanced μ hμ w)‖^2) ∧
    IsFiniteMeasure (wedgeResponseMeasure F dual sharp advanced (epsilon20Coordinates dual a) f μ hμ):=
  ⟨by simpa only [epsilon20Test,wedgeResponse] using
      actual_wedge_response_frequency F dual sharp advanced (epsilon20Coordinates dual a) f μ hμ,
    (actual_wedge_response_measure F dual sharp advanced (epsilon20Coordinates dual a) f μ hμ).2⟩

theorem actual_epsilon20_full_source_return(F:Index)(dual:Bool)(a:Epsilon20)(f:ScalarTest):
    ∃K₀:Index,F⊆K₀ ∧ ∀K:Index,K₀⊆K → ∀z:ℂ,∀hz:z.im≠0,
      literalCoreResolvent K z hz
        ((GaussFullHamiltonian.fullAction-z • (1:QuantumTest→ₗ[ℂ]QuantumTest)) (epsilon20Test dual a f))=
        epsilon20Test dual a f ∧
      literalSharpResolvent K z hz
        ((GaussFullHamiltonian.sharpAction-z • (1:QuantumTest→ₗ[ℂ]QuantumTest)) (epsilon20Test dual a f))=
        epsilon20Test dual a f:=
  by simpa only [epsilon20Test] using actual_wedge_full_source_return F dual (epsilon20Coordinates dual a) f

end LowEnergy.NamedColorQtNext
