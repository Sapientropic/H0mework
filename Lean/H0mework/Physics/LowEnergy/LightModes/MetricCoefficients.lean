import H0mework.Physics.LowEnergy.LightModes.Wave

/-! The original g00 source numerator, with its explicit finite-coefficient
separation from zero on the generated axial branch. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightModes
noncomputable section

def metricRaw {R : Type*} [CommRing R] (v w : R) : R :=
  -18596183472000*v^6 - 41446020708000*v^5*w - 340819830714240*v^5 + 434216821500000*v^4*w^2 + 367830877749120*v^4*w - 1678841863096032*v^4 + 651419197798500*v^3*w^3 + 2053972077783840*v^3*w^2 + 863278195689864*v^3*w - 6848127468360000*v^3 - 72615234375000*v^2*w^4 - 3249883667587500*v^2*w^3 - 14143148665204500*v^2*w^2 - 18878196531510000*v^2*w - 24712372131408000*v^2 - 266967773437500*v*w^5 - 3406942771875000*v*w^4 - 7826715408656250*v*w^3 + 15613203972600000*v*w^2 + 23409241218000000*v*w - 9937946700000000*v + 160180664062500*w^5 + 1915009277343750*w^4 + 3047637656250000*w^3 - 10121025937500000*w^2 + 4182637500000000*w

def metricLinear (r : ℝ) : ℝ := 4182637500000000 - 9937946700000000*r
def metricTerms : List Term := [⟨6,9,-18596183472000⟩, ⟨5,9,-41446020708000⟩, ⟨5,7,-340819830714240⟩, ⟨4,9,434216821500000⟩, ⟨4,7,367830877749120⟩, ⟨4,5,-1678841863096032⟩, ⟨3,9,651419197798500⟩, ⟨3,7,2053972077783840⟩, ⟨3,5,863278195689864⟩, ⟨3,3,-6848127468360000⟩, ⟨2,9,-72615234375000⟩, ⟨2,7,-3249883667587500⟩, ⟨2,5,-14143148665204500⟩, ⟨2,3,-18878196531510000⟩, ⟨2,1,-24712372131408000⟩, ⟨1,9,-266967773437500⟩, ⟨1,7,-3406942771875000⟩, ⟨1,5,-7826715408656250⟩, ⟨1,3,15613203972600000⟩, ⟨1,1,23409241218000000⟩, ⟨0,7,160180664062500⟩, ⟨0,5,1915009277343750⟩, ⟨0,3,3047637656250000⟩, ⟨0,1,-10121025937500000⟩]
def metricMargin : ℝ := 2988633915000000

theorem metric_normalized (r q : ℝ) :
    metricRaw (q^2*r) (q^2)=q^2*(metricLinear r+q*value metricTerms r q) := by
  norm_num [metricRaw,metricLinear,metricTerms,value]
  ring

theorem metric_margin_positive : 0<metricMargin := by norm_num [metricMargin]

theorem metric_remainder_small : momentumRadius*coefficientBound metricTerms≤metricMargin/2 := by
  norm_num [momentumRadius,coefficientBound,metricTerms,metricMargin]

theorem metric_linear_negative (r : ℝ) (lower : (125/162 : ℝ)-1/20≤r) :
    metricLinear r≤ -metricMargin := by
  unfold metricLinear metricMargin
  linarith

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightModes
