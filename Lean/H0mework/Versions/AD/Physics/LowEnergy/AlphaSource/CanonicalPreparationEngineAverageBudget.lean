import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineActualRadial
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalSourceBudget

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineBudget
open PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal PreparationVacuumMoyalBudget
open PreparationVacuumEngineSmooth PreparationVacuumClockSymbol PreparationVacuumMoyalSymmetry
open scoped BigOperators ContDiff

abbrev RealSymbol := PreparationVacuumCanonicalMoyal.Symbol
abbrev SourcePhase := PreparationVacuumCanonicalMoyal.Phase
abbrev JetMajorant := ℕ → ℝ
abbrev PolynomialMajorant := AngularExponent → JetMajorant

def SymbolBound (f : RealSymbol) (B : JetMajorant) (x : SourcePhase) : Prop :=
  ∀ m (w : Word m),|jet m f w x|≤B m

def PolynomialBound (P : AngularPolynomial) (B : PolynomialMajorant) (x : SourcePhase) : Prop :=
  ∀ u,SymbolBound (MvPolynomial.coeff u P) (B u) x

def averageMajorant (P : AngularPolynomial) (B : PolynomialMajorant) : JetMajorant :=
  fun m => ∑ u∈P.support,|angularMoment u| *B u m

theorem jet_scale (c : ℝ) (f : RealSymbol) (hf : SmoothSymbol f)
    (m : ℕ) (w : Word m) (x : SourcePhase) (hx : x∈poleDomain) :
    jet m (fun y => c*f y) w x=c*jet m f w x := by
  unfold jet
  rw [←listJet_ofFn poleDomain_open (contDiffOn_const.mul hf) m _ x hx,
    listJet_scale poleDomain_open c f hf _ hx]
  dsimp only
  rw [listJet_ofFn poleDomain_open hf m _ x hx]

theorem average_jet (P : AngularPolynomial) (sp : SmoothPolynomial P)
    (m : ℕ) (w : Word m) (x : SourcePhase) (hx : x∈poleDomain) :
    jet m (average P) w x=∑ u∈P.support,angularMoment u*jet m (MvPolynomial.coeff u P) w x := by
  have representation : average P=(fun y => ∑ u∈P.support,angularMoment u*MvPolynomial.coeff u P y) := by
    funext y
    simp only [average,Finset.sum_apply]
  rw [representation]
  rw [jet_sum poleDomain_open P.support _ (fun u _ => contDiffOn_const.mul (sp u)) m w x hx]
  apply Finset.sum_congr rfl
  intro u _
  exact jet_scale (angularMoment u) _ (sp u) m w x hx

theorem average_budget (P : AngularPolynomial) (B : PolynomialMajorant)
    (sp : SmoothPolynomial P) (x : SourcePhase) (hx : x∈poleDomain) (bound : PolynomialBound P B x) :
    SymbolBound (average P) (averageMajorant P B) x := by
  intro m w
  rw [average_jet P sp m w x hx]
  calc
    _≤∑ u∈P.support,|angularMoment u*jet m (MvPolynomial.coeff u P) w x| := Finset.abs_sum_le_sum_abs _ _
    _≤_ := by
      apply Finset.sum_le_sum
      intro u _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (bound u m w) (abs_nonneg _)

theorem symbolBound_nonnegative (f : RealSymbol) (B : JetMajorant) (x : SourcePhase)
    (bound : SymbolBound f B x) (m : ℕ) : 0≤B m :=
  (abs_nonneg _).trans (bound m (fun _ => (0,false)))

theorem symbolBound_zero (x : SourcePhase) : SymbolBound 0 (fun _ => 0) x := by
  intro m w
  simp [jet]

theorem symbolBound_add {f g : RealSymbol} {B D : JetMajorant} (sf : SmoothSymbol f) (sg : SmoothSymbol g)
    (x : SourcePhase) (hx : x∈poleDomain) (bf : SymbolBound f B x) (bg : SymbolBound g D x) :
    SymbolBound (f+g) (fun m => B m+D m) x := by
  intro m w
  have formula : jet m (f+g) w x=jet m f w x+jet m g w x := by
    unfold jet
    change iteratedFDeriv ℝ m (fun y => f y+g y) x (fun a => slotDirection (w a))=_
    rw [←listJet_ofFn poleDomain_open (sf.add sg) m _ x hx,
      listJet_add poleDomain_open _ _ sf sg _ hx]
    dsimp only
    rw [listJet_ofFn poleDomain_open sf m _ x hx,listJet_ofFn poleDomain_open sg m _ x hx]
  rw [formula]
  exact (abs_add_le _ _).trans (add_le_add (bf m w) (bg m w))

theorem symbolBound_scale (c : ℝ) {f : RealSymbol} {B : JetMajorant} (sf : SmoothSymbol f)
    (x : SourcePhase) (hx : x∈poleDomain) (bf : SymbolBound f B x) :
    SymbolBound (fun y => c*f y) (fun m => |c| *B m) x := by
  intro m w
  rw [jet_scale c f sf m w x hx,abs_mul]
  exact mul_le_mul_of_nonneg_left (bf m w) (abs_nonneg _)

theorem polynomialBound_zero (x : SourcePhase) : PolynomialBound 0 (fun _ _ => 0) x := by
  intro u
  simpa only [MvPolynomial.coeff_zero] using symbolBound_zero x

theorem polynomialBound_add {P Q : AngularPolynomial} {B D : PolynomialMajorant}
    (sp : SmoothPolynomial P) (sq : SmoothPolynomial Q) (x : SourcePhase) (hx : x∈poleDomain)
    (bp : PolynomialBound P B x) (bq : PolynomialBound Q D x) :
    PolynomialBound (P+Q) (fun u m => B u m+D u m) x := by
  intro u
  simpa only [MvPolynomial.coeff_add] using symbolBound_add (sp u) (sq u) x hx (bp u) (bq u)

def weightedMajorant (r : ℕ) (P Q : AngularPolynomial) (B D : PolynomialMajorant) : PolynomialMajorant :=
  fun target m => ∑ u∈P.support,∑ v∈Q.support,
    if u+v=target then moyalScale r*convolution m r (B u) (D v) else 0

theorem weighted_budget (r : ℕ) (P Q : AngularPolynomial) (B D : PolynomialMajorant)
    (sp : SmoothPolynomial P) (sq : SmoothPolynomial Q) (x : SourcePhase) (hx : x∈poleDomain)
    (bp : PolynomialBound P B x) (bq : PolynomialBound Q D x) :
    PolynomialBound (weighted r P Q) (weightedMajorant r P Q B D) x := by
  intro target m w
  exact weighted_coefficient_budget poleDomain_open r m P Q target w x hx B D
    (fun u _ => sp u) (fun v _ => sq v)
    (fun u _ n => symbolBound_nonnegative _ _ x (bp u) n)
    (fun u _ n _ word => bp u n word) (fun v _ n _ word => bq v n word)

end LowEnergy.PreparationVacuumEngineBudget
