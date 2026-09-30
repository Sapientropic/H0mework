import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Weights

set_option autoImplicit false
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticPower

theorem inner_power {p r q d t s u v x y : ℝ}
    (d0 : 0 ≤ d) (t0 : 0 ≤ t) (s0 : 0 ≤ s) (v0 : 0 ≤ v) (x0 : 0 ≤ x)
    (hp : p^2*d ≤ u) (hr : r^2*s ≤ 2*u) (hq : q^4*s ≤ u)
    (hs : s ≤ 2*t) (hd : d ≤ v*y) (htx : t ≤ v*x) (hty : t ≤ v*y) :
    (s*d*t*p*r*q)^8 ≤ 64*u^10*v^14*x^7*y^7 := by
  calc
    _ = (p^2*d)^4*(r^2*s)^4*(q^4*s)^2*s^2*d^4*t^8 := by ring
    _ ≤ u^4*(2*u)^4*u^2*(2*t)^2*d^4*t^8 := by gcongr
    _ = 64*u^10*d^4*t^7*t^3 := by ring
    _ ≤ 64*u^10*(v*y)^4*(v*x)^7*(v*y)^3 := by gcongr
    _ = _ := by ring

theorem outer_power {p r q d t s u v x y : ℝ}
    (p0 : 0 ≤ p) (r0 : 0 ≤ r) (d0 : 0 ≤ d) (t0 : 0 ≤ t) (s0 : 0 ≤ s) (v0 : 0 ≤ v) (x0 : 0 ≤ x)
    (hp : p*r*d ≤ u) (hq : q^4*s ≤ u) (hs : s ≤ 2*t) (htx : t ≤ v*x) (hty : t ≤ v*y) :
    (s*d*t*p*r*q)^8 ≤ 64*u^10*v^14*x^7*y^7 := by
  calc
    _ = (p*r*d)^8*(q^4*s)^2*s^6*t^8 := by ring
    _ ≤ u^8*u^2*(2*t)^6*t^8 := by gcongr
    _ = 64*u^10*t^7*t^7 := by ring
    _ ≤ 64*u^10*(v*x)^7*(v*y)^7 := by gcongr
    _ = _ := by ring

end SaturationMonoid.NavierStokes.NativeUnheatedQuinticPower
