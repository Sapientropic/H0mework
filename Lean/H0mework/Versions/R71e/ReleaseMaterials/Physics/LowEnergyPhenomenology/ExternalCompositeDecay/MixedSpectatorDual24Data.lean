import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorContactVertices

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
noncomputable section
namespace LowEnergy.MixedSpectatorDual24Data
open scoped BigOperators Matrix

def numerator0 (x r : ℂ) : ℂ :=
  ((91854/78125) + ((-5832/3125) * (r ^ 2)) + ((-459/1000) * (x ^ 4)) + ((-243/3125) * (x ^ 2)) + ((-9/80) * (r ^ 6)) + ((9/80) * (x ^ 6)) + ((891/1000) * (r ^ 4)) + ((-9/80) * (r ^ 4) * (x ^ 2)) + ((9/80) * (r ^ 2) * (x ^ 4)) + ((189/250) * (r ^ 2) * (x ^ 2)) + ((-297/250) * Complex.I * x * (r ^ 3)) + ((-189/125) * Complex.I * r * (x ^ 3)) + ((9/20) * Complex.I * (r ^ 3) * (x ^ 3)) + ((9/40) * Complex.I * r * (x ^ 5)) + ((9/40) * Complex.I * x * (r ^ 5)) + ((3888/3125) * Complex.I * r * x))

def numerator1 (x r : ℂ) : ℂ :=
  ((-13122/15625) + ((-486/625) * (x ^ 2)) + ((-189/200) * (r ^ 4)) + ((3/16) * (r ^ 6)) + ((3/16) * (x ^ 6)) + ((27/200) * (x ^ 4)) + ((972/625) * (r ^ 2)) + ((-81/100) * (r ^ 2) * (x ^ 2)) + ((9/16) * (r ^ 2) * (x ^ 4)) + ((9/16) * (r ^ 4) * (x ^ 2)))

def numerator2 (x r : ℂ) : ℂ :=
  ((-13122/15625) + ((-189/200) * (r ^ 4)) + ((-3/16) * (x ^ 6)) + ((3/16) * (r ^ 6)) + ((81/200) * (x ^ 4)) + ((243/625) * (x ^ 2)) + ((972/625) * (r ^ 2)) + ((-3/16) * (r ^ 2) * (x ^ 4)) + ((3/16) * (r ^ 4) * (x ^ 2)) + ((-972/625) * Complex.I * r * x) + ((-3/4) * Complex.I * (r ^ 3) * (x ^ 3)) + ((-3/8) * Complex.I * r * (x ^ 5)) + ((-3/8) * Complex.I * x * (r ^ 5)) + ((27/25) * Complex.I * r * (x ^ 3)) + ((81/50) * Complex.I * x * (r ^ 3)))

def numerator3 (x r : ℂ) : ℂ :=
  (((-891/1250) * (x ^ 3)) + ((-27/100) * (x ^ 5)) + ((1/4) * (x ^ 7)) + ((4374/15625) * x) + ((-22599/15625) * Complex.I * r) + ((-567/400) * Complex.I * (r ^ 5)) + ((-261/200) * (r ^ 2) * (x ^ 3)) + ((-207/200) * x * (r ^ 4)) + ((1/4) * Complex.I * (r ^ 7)) + ((1/4) * x * (r ^ 6)) + ((3/4) * (r ^ 2) * (x ^ 5)) + ((3/4) * (r ^ 4) * (x ^ 3)) + ((486/625) * x * (r ^ 2)) + ((3159/1250) * Complex.I * (r ^ 3)) + ((-261/400) * Complex.I * r * (x ^ 4)) + ((-207/100) * Complex.I * (r ^ 3) * (x ^ 2)) + ((1/4) * Complex.I * r * (x ^ 6)) + ((3/4) * Complex.I * (r ^ 3) * (x ^ 4)) + ((3/4) * Complex.I * (r ^ 5) * (x ^ 2)) + ((486/625) * Complex.I * r * (x ^ 2)))

def numerator4 (x r : ℂ) : ℂ :=
  (((-729/3125) * Complex.I * r) + ((-9/80) * Complex.I * (r ^ 5)) + ((81/250) * Complex.I * (r ^ 3)) + ((-81/250) * Complex.I * r * (x ^ 2)) + ((-9/40) * Complex.I * (r ^ 3) * (x ^ 2)) + ((-9/80) * Complex.I * r * (x ^ 4)))

def numerator5 (x r : ℂ) : ℂ :=
  (((-81/250) * Complex.I * (r ^ 3)) + ((9/80) * Complex.I * (r ^ 5)) + ((729/3125) * Complex.I * r) + ((9/40) * Complex.I * (r ^ 3) * (x ^ 2)) + ((9/80) * Complex.I * r * (x ^ 4)) + ((81/250) * Complex.I * r * (x ^ 2)))

def numerator6 (x r : ℂ) : ℂ :=
  (((-9/20) * (x ^ 5)) + ((81/250) * (x ^ 3)) + ((4374/3125) * x) + ((-729/3125) * Complex.I * r) + ((-162/125) * x * (r ^ 2)) + ((-9/40) * (r ^ 2) * (x ^ 3)) + ((-9/80) * Complex.I * (r ^ 5)) + ((9/40) * x * (r ^ 4)) + ((81/250) * Complex.I * (r ^ 3)) + ((-63/80) * Complex.I * r * (x ^ 4)) + ((-9/10) * Complex.I * (r ^ 3) * (x ^ 2)) + ((243/125) * Complex.I * r * (x ^ 2)))

def numerator7 (x r : ℂ) : ℂ :=
  ((91854/78125) + ((-5832/3125) * (r ^ 2)) + ((-459/1000) * (x ^ 4)) + ((-243/3125) * (x ^ 2)) + ((-9/80) * (r ^ 6)) + ((9/80) * (x ^ 6)) + ((891/1000) * (r ^ 4)) + ((-9/80) * (r ^ 4) * (x ^ 2)) + ((9/80) * (r ^ 2) * (x ^ 4)) + ((189/250) * (r ^ 2) * (x ^ 2)) + ((-3888/3125) * Complex.I * r * x) + ((-9/20) * Complex.I * (r ^ 3) * (x ^ 3)) + ((-9/40) * Complex.I * r * (x ^ 5)) + ((-9/40) * Complex.I * x * (r ^ 5)) + ((189/125) * Complex.I * r * (x ^ 3)) + ((297/250) * Complex.I * x * (r ^ 3)))

def numerator8 (x r : ℂ) : ℂ :=
  ((-13122/15625) + ((-189/200) * (r ^ 4)) + ((-3/16) * (x ^ 6)) + ((3/16) * (r ^ 6)) + ((81/200) * (x ^ 4)) + ((243/625) * (x ^ 2)) + ((972/625) * (r ^ 2)) + ((-3/16) * (r ^ 2) * (x ^ 4)) + ((3/16) * (r ^ 4) * (x ^ 2)) + ((-81/50) * Complex.I * x * (r ^ 3)) + ((-27/25) * Complex.I * r * (x ^ 3)) + ((3/4) * Complex.I * (r ^ 3) * (x ^ 3)) + ((3/8) * Complex.I * r * (x ^ 5)) + ((3/8) * Complex.I * x * (r ^ 5)) + ((972/625) * Complex.I * r * x))

def numerator9 (x r : ℂ) : ℂ :=
  (((-891/1250) * (x ^ 3)) + ((-27/100) * (x ^ 5)) + ((1/4) * (x ^ 7)) + ((4374/15625) * x) + ((-3159/1250) * Complex.I * (r ^ 3)) + ((-261/200) * (r ^ 2) * (x ^ 3)) + ((-207/200) * x * (r ^ 4)) + ((-1/4) * Complex.I * (r ^ 7)) + ((1/4) * x * (r ^ 6)) + ((3/4) * (r ^ 2) * (x ^ 5)) + ((3/4) * (r ^ 4) * (x ^ 3)) + ((486/625) * x * (r ^ 2)) + ((567/400) * Complex.I * (r ^ 5)) + ((22599/15625) * Complex.I * r) + ((-486/625) * Complex.I * r * (x ^ 2)) + ((-3/4) * Complex.I * (r ^ 3) * (x ^ 4)) + ((-3/4) * Complex.I * (r ^ 5) * (x ^ 2)) + ((-1/4) * Complex.I * r * (x ^ 6)) + ((207/100) * Complex.I * (r ^ 3) * (x ^ 2)) + ((261/400) * Complex.I * r * (x ^ 4)))

def numerator10 (x r : ℂ) : ℂ :=
  (((-9/20) * (x ^ 5)) + ((81/250) * (x ^ 3)) + ((4374/3125) * x) + ((-162/125) * x * (r ^ 2)) + ((-81/250) * Complex.I * (r ^ 3)) + ((-9/40) * (r ^ 2) * (x ^ 3)) + ((9/40) * x * (r ^ 4)) + ((9/80) * Complex.I * (r ^ 5)) + ((729/3125) * Complex.I * r) + ((-243/125) * Complex.I * r * (x ^ 2)) + ((9/10) * Complex.I * (r ^ 3) * (x ^ 2)) + ((63/80) * Complex.I * r * (x ^ 4)))

def numerator11 (x r : ℂ) : ℂ :=
  (((-4374/3125) * x) + ((-81/250) * (x ^ 3)) + ((9/20) * (x ^ 5)) + ((-729/3125) * Complex.I * r) + ((-9/40) * x * (r ^ 4)) + ((-9/80) * Complex.I * (r ^ 5)) + ((9/40) * (r ^ 2) * (x ^ 3)) + ((81/250) * Complex.I * (r ^ 3)) + ((162/125) * x * (r ^ 2)) + ((-63/80) * Complex.I * r * (x ^ 4)) + ((-9/10) * Complex.I * (r ^ 3) * (x ^ 2)) + ((243/125) * Complex.I * r * (x ^ 2)))

def numerator12 (x r : ℂ) : ℂ :=
  (((-4374/15625) * x) + ((-1/4) * (x ^ 7)) + ((27/100) * (x ^ 5)) + ((891/1250) * (x ^ 3)) + ((-22599/15625) * Complex.I * r) + ((-567/400) * Complex.I * (r ^ 5)) + ((-486/625) * x * (r ^ 2)) + ((-3/4) * (r ^ 2) * (x ^ 5)) + ((-3/4) * (r ^ 4) * (x ^ 3)) + ((-1/4) * x * (r ^ 6)) + ((1/4) * Complex.I * (r ^ 7)) + ((207/200) * x * (r ^ 4)) + ((261/200) * (r ^ 2) * (x ^ 3)) + ((3159/1250) * Complex.I * (r ^ 3)) + ((-261/400) * Complex.I * r * (x ^ 4)) + ((-207/100) * Complex.I * (r ^ 3) * (x ^ 2)) + ((1/4) * Complex.I * r * (x ^ 6)) + ((3/4) * Complex.I * (r ^ 3) * (x ^ 4)) + ((3/4) * Complex.I * (r ^ 5) * (x ^ 2)) + ((486/625) * Complex.I * r * (x ^ 2)))

def numerator13 (x r : ℂ) : ℂ :=
  (((-4374/3125) * x) + ((-81/250) * (x ^ 3)) + ((9/20) * (x ^ 5)) + ((-81/250) * Complex.I * (r ^ 3)) + ((-9/40) * x * (r ^ 4)) + ((9/40) * (r ^ 2) * (x ^ 3)) + ((9/80) * Complex.I * (r ^ 5)) + ((162/125) * x * (r ^ 2)) + ((729/3125) * Complex.I * r) + ((-243/125) * Complex.I * r * (x ^ 2)) + ((9/10) * Complex.I * (r ^ 3) * (x ^ 2)) + ((63/80) * Complex.I * r * (x ^ 4)))

def numerator14 (x r : ℂ) : ℂ :=
  (((-4374/15625) * x) + ((-1/4) * (x ^ 7)) + ((27/100) * (x ^ 5)) + ((891/1250) * (x ^ 3)) + ((-3159/1250) * Complex.I * (r ^ 3)) + ((-486/625) * x * (r ^ 2)) + ((-3/4) * (r ^ 2) * (x ^ 5)) + ((-3/4) * (r ^ 4) * (x ^ 3)) + ((-1/4) * Complex.I * (r ^ 7)) + ((-1/4) * x * (r ^ 6)) + ((207/200) * x * (r ^ 4)) + ((261/200) * (r ^ 2) * (x ^ 3)) + ((567/400) * Complex.I * (r ^ 5)) + ((22599/15625) * Complex.I * r) + ((-486/625) * Complex.I * r * (x ^ 2)) + ((-3/4) * Complex.I * (r ^ 3) * (x ^ 4)) + ((-3/4) * Complex.I * (r ^ 5) * (x ^ 2)) + ((-1/4) * Complex.I * r * (x ^ 6)) + ((207/100) * Complex.I * (r ^ 3) * (x ^ 2)) + ((261/400) * Complex.I * r * (x ^ 4)))

def numerator15 (x r : ℂ) : ℂ :=
  ((13122/15625) + ((-972/625) * (r ^ 2)) + ((-27/200) * (x ^ 4)) + ((-3/16) * (r ^ 6)) + ((-3/16) * (x ^ 6)) + ((189/200) * (r ^ 4)) + ((486/625) * (x ^ 2)) + ((-9/16) * (r ^ 2) * (x ^ 4)) + ((-9/16) * (r ^ 4) * (x ^ 2)) + ((81/100) * (r ^ 2) * (x ^ 2)))

def numerator16 (x r : ℂ) : ℂ :=
  ((13122/15625) + ((-972/625) * (r ^ 2)) + ((-243/625) * (x ^ 2)) + ((-81/200) * (x ^ 4)) + ((-3/16) * (r ^ 6)) + ((3/16) * (x ^ 6)) + ((189/200) * (r ^ 4)) + ((-3/16) * (r ^ 4) * (x ^ 2)) + ((3/16) * (r ^ 2) * (x ^ 4)) + ((-81/50) * Complex.I * x * (r ^ 3)) + ((-27/25) * Complex.I * r * (x ^ 3)) + ((3/4) * Complex.I * (r ^ 3) * (x ^ 3)) + ((3/8) * Complex.I * r * (x ^ 5)) + ((3/8) * Complex.I * x * (r ^ 5)) + ((972/625) * Complex.I * r * x))

def numerator17 (x r : ℂ) : ℂ :=
  ((13122/15625) + ((-972/625) * (r ^ 2)) + ((-243/625) * (x ^ 2)) + ((-81/200) * (x ^ 4)) + ((-3/16) * (r ^ 6)) + ((3/16) * (x ^ 6)) + ((189/200) * (r ^ 4)) + ((-3/16) * (r ^ 4) * (x ^ 2)) + ((3/16) * (r ^ 2) * (x ^ 4)) + ((-972/625) * Complex.I * r * x) + ((-3/4) * Complex.I * (r ^ 3) * (x ^ 3)) + ((-3/8) * Complex.I * r * (x ^ 5)) + ((-3/8) * Complex.I * x * (r ^ 5)) + ((27/25) * Complex.I * r * (x ^ 3)) + ((81/50) * Complex.I * x * (r ^ 3)))

def numerator18 (x r : ℂ) : ℂ :=
  (((-729/1250) * (x ^ 2)) + ((-459/1000) * (x ^ 4)) + ((-27/200) * (r ^ 4)) + ((-3/20) * (r ^ 6)) + ((3/20) * (x ^ 6)) + ((-513/500) * (r ^ 2) * (x ^ 2)) + ((-3/20) * (r ^ 4) * (x ^ 2)) + ((3/20) * (r ^ 2) * (x ^ 4)) + ((-27/50) * Complex.I * x * (r ^ 3)) + ((-27/250) * Complex.I * r * (x ^ 3)) + ((3/5) * Complex.I * (r ^ 3) * (x ^ 3)) + ((3/10) * Complex.I * r * (x ^ 5)) + ((3/10) * Complex.I * x * (r ^ 5)))

def numerator19 (x r : ℂ) : ℂ :=
  (((-189/1000) * (x ^ 4)) + ((-9/40) * (r ^ 6)) + ((-9/40) * (x ^ 6)) + ((27/200) * (r ^ 4)) + ((729/1250) * (x ^ 2)) + ((-27/40) * (r ^ 2) * (x ^ 4)) + ((-27/40) * (r ^ 4) * (x ^ 2)) + ((-27/500) * (r ^ 2) * (x ^ 2)))

def numerator20 (x r : ℂ) : ℂ :=
  (((-729/1250) * (x ^ 2)) + ((-27/40) * (r ^ 4)) + ((-27/200) * (x ^ 4)) + ((3/8) * (r ^ 6)) + ((3/8) * (x ^ 6)) + ((-81/100) * (r ^ 2) * (x ^ 2)) + ((9/8) * (r ^ 2) * (x ^ 4)) + ((9/8) * (r ^ 4) * (x ^ 2)))

def numerator21 (x r : ℂ) : ℂ :=
  (((27/40) * (r ^ 4)) + ((27/200) * (x ^ 4)) + ((729/1250) * (x ^ 2)) + ((81/100) * (r ^ 2) * (x ^ 2)) + ((-27/50) * Complex.I * r * (x ^ 3)) + ((-27/50) * Complex.I * x * (r ^ 3)))

def numerator22 (x r : ℂ) : ℂ :=
  (((-243/625) * (x ^ 3)) + ((-27/200) * (x ^ 5)) + ((1/4) * (x ^ 7)) + ((-99/200) * x * (r ^ 4)) + ((-81/250) * x * (r ^ 2)) + ((-63/100) * (r ^ 2) * (x ^ 3)) + ((-27/40) * Complex.I * (r ^ 5)) + ((1/4) * Complex.I * (r ^ 7)) + ((1/4) * x * (r ^ 6)) + ((3/4) * (r ^ 2) * (x ^ 5)) + ((3/4) * (r ^ 4) * (x ^ 3)) + ((-99/100) * Complex.I * (r ^ 3) * (x ^ 2)) + ((-81/250) * Complex.I * r * (x ^ 2)) + ((-63/200) * Complex.I * r * (x ^ 4)) + ((1/4) * Complex.I * r * (x ^ 6)) + ((3/4) * Complex.I * (r ^ 3) * (x ^ 4)) + ((3/4) * Complex.I * (r ^ 5) * (x ^ 2)))

def numerator23 (x r : ℂ) : ℂ :=
  (((9/200) * (x ^ 5)) + ((243/625) * (x ^ 3)) + ((-9/40) * Complex.I * (r ^ 5)) + ((9/100) * (r ^ 2) * (x ^ 3)) + ((9/200) * x * (r ^ 4)) + ((81/250) * x * (r ^ 2)) + ((-81/250) * Complex.I * r * (x ^ 2)) + ((-9/20) * Complex.I * (r ^ 3) * (x ^ 2)) + ((-9/40) * Complex.I * r * (x ^ 4)))

def numerator24 (x r : ℂ) : ℂ :=
  (((9/40) * (x ^ 5)) + ((-81/250) * x * (r ^ 2)) + ((-9/40) * Complex.I * (r ^ 5)) + ((9/20) * (r ^ 2) * (x ^ 3)) + ((9/40) * x * (r ^ 4)) + ((-81/250) * Complex.I * r * (x ^ 2)) + ((-9/20) * Complex.I * (r ^ 3) * (x ^ 2)) + ((-9/40) * Complex.I * r * (x ^ 4)))

def numerator25 (x r : ℂ) : ℂ :=
  (((9/40) * (x ^ 5)) + ((9/20) * (r ^ 2) * (x ^ 3)) + ((9/40) * Complex.I * (r ^ 5)) + ((9/40) * x * (r ^ 4)) + ((81/250) * x * (r ^ 2)) + ((-81/250) * Complex.I * r * (x ^ 2)) + ((9/20) * Complex.I * (r ^ 3) * (x ^ 2)) + ((9/40) * Complex.I * r * (x ^ 4)))

def numerator26 (x r : ℂ) : ℂ :=
  (((-729/1250) * (x ^ 2)) + ((-459/1000) * (x ^ 4)) + ((-27/200) * (r ^ 4)) + ((-3/20) * (r ^ 6)) + ((3/20) * (x ^ 6)) + ((-513/500) * (r ^ 2) * (x ^ 2)) + ((-3/20) * (r ^ 4) * (x ^ 2)) + ((3/20) * (r ^ 2) * (x ^ 4)) + ((-3/5) * Complex.I * (r ^ 3) * (x ^ 3)) + ((-3/10) * Complex.I * r * (x ^ 5)) + ((-3/10) * Complex.I * x * (r ^ 5)) + ((27/50) * Complex.I * x * (r ^ 3)) + ((27/250) * Complex.I * r * (x ^ 3)))

def numerator27 (x r : ℂ) : ℂ :=
  (((27/40) * (r ^ 4)) + ((27/200) * (x ^ 4)) + ((729/1250) * (x ^ 2)) + ((81/100) * (r ^ 2) * (x ^ 2)) + ((27/50) * Complex.I * r * (x ^ 3)) + ((27/50) * Complex.I * x * (r ^ 3)))

def numerator28 (x r : ℂ) : ℂ :=
  (((9/200) * (x ^ 5)) + ((243/625) * (x ^ 3)) + ((9/40) * Complex.I * (r ^ 5)) + ((9/100) * (r ^ 2) * (x ^ 3)) + ((9/200) * x * (r ^ 4)) + ((81/250) * x * (r ^ 2)) + ((9/20) * Complex.I * (r ^ 3) * (x ^ 2)) + ((9/40) * Complex.I * r * (x ^ 4)) + ((81/250) * Complex.I * r * (x ^ 2)))

def numerator29 (x r : ℂ) : ℂ :=
  (((-243/625) * (x ^ 3)) + ((-27/200) * (x ^ 5)) + ((1/4) * (x ^ 7)) + ((-99/200) * x * (r ^ 4)) + ((-81/250) * x * (r ^ 2)) + ((-63/100) * (r ^ 2) * (x ^ 3)) + ((-1/4) * Complex.I * (r ^ 7)) + ((1/4) * x * (r ^ 6)) + ((3/4) * (r ^ 2) * (x ^ 5)) + ((3/4) * (r ^ 4) * (x ^ 3)) + ((27/40) * Complex.I * (r ^ 5)) + ((-3/4) * Complex.I * (r ^ 3) * (x ^ 4)) + ((-3/4) * Complex.I * (r ^ 5) * (x ^ 2)) + ((-1/4) * Complex.I * r * (x ^ 6)) + ((63/200) * Complex.I * r * (x ^ 4)) + ((81/250) * Complex.I * r * (x ^ 2)) + ((99/100) * Complex.I * (r ^ 3) * (x ^ 2)))

def numerator30 (x r : ℂ) : ℂ :=
  (((9/40) * (x ^ 5)) + ((-9/40) * Complex.I * (r ^ 5)) + ((9/20) * (r ^ 2) * (x ^ 3)) + ((9/40) * x * (r ^ 4)) + ((81/250) * x * (r ^ 2)) + ((-9/20) * Complex.I * (r ^ 3) * (x ^ 2)) + ((-9/40) * Complex.I * r * (x ^ 4)) + ((81/250) * Complex.I * r * (x ^ 2)))

def numerator31 (x r : ℂ) : ℂ :=
  (((9/40) * (x ^ 5)) + ((-81/250) * x * (r ^ 2)) + ((9/20) * (r ^ 2) * (x ^ 3)) + ((9/40) * Complex.I * (r ^ 5)) + ((9/40) * x * (r ^ 4)) + ((9/20) * Complex.I * (r ^ 3) * (x ^ 2)) + ((9/40) * Complex.I * r * (x ^ 4)) + ((81/250) * Complex.I * r * (x ^ 2)))

def numerator32 (x r : ℂ) : ℂ :=
  (((-9/40) * (x ^ 5)) + ((-9/20) * (r ^ 2) * (x ^ 3)) + ((-9/40) * Complex.I * (r ^ 5)) + ((-9/40) * x * (r ^ 4)) + ((81/250) * x * (r ^ 2)) + ((-81/250) * Complex.I * r * (x ^ 2)) + ((-9/20) * Complex.I * (r ^ 3) * (x ^ 2)) + ((-9/40) * Complex.I * r * (x ^ 4)))

def numerator33 (x r : ℂ) : ℂ :=
  (((-9/40) * (x ^ 5)) + ((-81/250) * x * (r ^ 2)) + ((-9/20) * (r ^ 2) * (x ^ 3)) + ((-9/40) * x * (r ^ 4)) + ((9/40) * Complex.I * (r ^ 5)) + ((-81/250) * Complex.I * r * (x ^ 2)) + ((9/20) * Complex.I * (r ^ 3) * (x ^ 2)) + ((9/40) * Complex.I * r * (x ^ 4)))

def numerator34 (x r : ℂ) : ℂ :=
  (((-1/4) * (x ^ 7)) + ((27/200) * (x ^ 5)) + ((243/625) * (x ^ 3)) + ((-27/40) * Complex.I * (r ^ 5)) + ((-3/4) * (r ^ 2) * (x ^ 5)) + ((-3/4) * (r ^ 4) * (x ^ 3)) + ((-1/4) * x * (r ^ 6)) + ((1/4) * Complex.I * (r ^ 7)) + ((63/100) * (r ^ 2) * (x ^ 3)) + ((81/250) * x * (r ^ 2)) + ((99/200) * x * (r ^ 4)) + ((-99/100) * Complex.I * (r ^ 3) * (x ^ 2)) + ((-81/250) * Complex.I * r * (x ^ 2)) + ((-63/200) * Complex.I * r * (x ^ 4)) + ((1/4) * Complex.I * r * (x ^ 6)) + ((3/4) * Complex.I * (r ^ 3) * (x ^ 4)) + ((3/4) * Complex.I * (r ^ 5) * (x ^ 2)))

def numerator35 (x r : ℂ) : ℂ :=
  (((-243/625) * (x ^ 3)) + ((-9/200) * (x ^ 5)) + ((-81/250) * x * (r ^ 2)) + ((-9/40) * Complex.I * (r ^ 5)) + ((-9/100) * (r ^ 2) * (x ^ 3)) + ((-9/200) * x * (r ^ 4)) + ((-81/250) * Complex.I * r * (x ^ 2)) + ((-9/20) * Complex.I * (r ^ 3) * (x ^ 2)) + ((-9/40) * Complex.I * r * (x ^ 4)))

def numerator36 (x r : ℂ) : ℂ :=
  (((-9/40) * (x ^ 5)) + ((-81/250) * x * (r ^ 2)) + ((-9/20) * (r ^ 2) * (x ^ 3)) + ((-9/40) * Complex.I * (r ^ 5)) + ((-9/40) * x * (r ^ 4)) + ((-9/20) * Complex.I * (r ^ 3) * (x ^ 2)) + ((-9/40) * Complex.I * r * (x ^ 4)) + ((81/250) * Complex.I * r * (x ^ 2)))

def numerator37 (x r : ℂ) : ℂ :=
  (((-9/40) * (x ^ 5)) + ((-9/20) * (r ^ 2) * (x ^ 3)) + ((-9/40) * x * (r ^ 4)) + ((9/40) * Complex.I * (r ^ 5)) + ((81/250) * x * (r ^ 2)) + ((9/20) * Complex.I * (r ^ 3) * (x ^ 2)) + ((9/40) * Complex.I * r * (x ^ 4)) + ((81/250) * Complex.I * r * (x ^ 2)))

def numerator38 (x r : ℂ) : ℂ :=
  (((-243/625) * (x ^ 3)) + ((-9/200) * (x ^ 5)) + ((-81/250) * x * (r ^ 2)) + ((-9/100) * (r ^ 2) * (x ^ 3)) + ((-9/200) * x * (r ^ 4)) + ((9/40) * Complex.I * (r ^ 5)) + ((9/20) * Complex.I * (r ^ 3) * (x ^ 2)) + ((9/40) * Complex.I * r * (x ^ 4)) + ((81/250) * Complex.I * r * (x ^ 2)))

def numerator39 (x r : ℂ) : ℂ :=
  (((-1/4) * (x ^ 7)) + ((27/200) * (x ^ 5)) + ((243/625) * (x ^ 3)) + ((-3/4) * (r ^ 2) * (x ^ 5)) + ((-3/4) * (r ^ 4) * (x ^ 3)) + ((-1/4) * Complex.I * (r ^ 7)) + ((-1/4) * x * (r ^ 6)) + ((27/40) * Complex.I * (r ^ 5)) + ((63/100) * (r ^ 2) * (x ^ 3)) + ((81/250) * x * (r ^ 2)) + ((99/200) * x * (r ^ 4)) + ((-3/4) * Complex.I * (r ^ 3) * (x ^ 4)) + ((-3/4) * Complex.I * (r ^ 5) * (x ^ 2)) + ((-1/4) * Complex.I * r * (x ^ 6)) + ((63/200) * Complex.I * r * (x ^ 4)) + ((81/250) * Complex.I * r * (x ^ 2)) + ((99/100) * Complex.I * (r ^ 3) * (x ^ 2)))

def numerator40 (x r : ℂ) : ℂ :=
  (((-27/500) * (x ^ 4)) + ((-3/20) * (r ^ 6)) + ((3/20) * (x ^ 6)) + ((27/100) * (r ^ 4)) + ((-27/125) * (r ^ 2) * (x ^ 2)) + ((-3/20) * (r ^ 4) * (x ^ 2)) + ((3/20) * (r ^ 2) * (x ^ 4)) + ((-27/50) * Complex.I * x * (r ^ 3)) + ((-27/250) * Complex.I * r * (x ^ 3)) + ((3/5) * Complex.I * (r ^ 3) * (x ^ 3)) + ((3/10) * Complex.I * r * (x ^ 5)) + ((3/10) * Complex.I * x * (r ^ 5)))

def numerator41 (x r : ℂ) : ℂ :=
  (((-27/100) * (r ^ 4)) + ((-27/500) * (x ^ 4)) + ((3/20) * (r ^ 6)) + ((3/20) * (x ^ 6)) + ((-81/250) * (r ^ 2) * (x ^ 2)) + ((9/20) * (r ^ 2) * (x ^ 4)) + ((9/20) * (r ^ 4) * (x ^ 2)))

def numerator42 (x r : ℂ) : ℂ :=
  (((27/100) * (r ^ 4)) + ((27/100) * (x ^ 4)) + ((27/50) * (r ^ 2) * (x ^ 2)))

def numerator43 (x r : ℂ) : ℂ :=
  (((-27/100) * (r ^ 4)) + ((27/100) * (x ^ 4)) + ((27/50) * Complex.I * r * (x ^ 3)) + ((27/50) * Complex.I * x * (r ^ 3)))

def numerator44 (x r : ℂ) : ℂ :=
  (((-27/500) * (x ^ 4)) + ((-3/20) * (r ^ 6)) + ((3/20) * (x ^ 6)) + ((27/100) * (r ^ 4)) + ((-27/125) * (r ^ 2) * (x ^ 2)) + ((-3/20) * (r ^ 4) * (x ^ 2)) + ((3/20) * (r ^ 2) * (x ^ 4)) + ((-3/5) * Complex.I * (r ^ 3) * (x ^ 3)) + ((-3/10) * Complex.I * r * (x ^ 5)) + ((-3/10) * Complex.I * x * (r ^ 5)) + ((27/50) * Complex.I * x * (r ^ 3)) + ((27/250) * Complex.I * r * (x ^ 3)))

def numerator45 (x r : ℂ) : ℂ :=
  (((-27/100) * (r ^ 4)) + ((27/100) * (x ^ 4)) + ((-27/50) * Complex.I * r * (x ^ 3)) + ((-27/50) * Complex.I * x * (r ^ 3)))

def numerator46 (_x _r : ℂ) : ℂ :=
  (9/40)

def numerator47 (x r : ℂ) : ℂ :=
  (((1/4) * x) + ((-1/4) * Complex.I * r))

def numerator48 (x r : ℂ) : ℂ :=
  (((-1/4) * x) + ((1/4) * Complex.I * r))

def numerator49 (x r : ℂ) : ℂ :=
  (((1/4) * x) + ((1/4) * Complex.I * r))

def numerator50 (x r : ℂ) : ℂ :=
  (((-1/4) * x) + ((-1/4) * Complex.I * r))

def numeratorPolynomial (x r : ℂ) (a : Fin 51) : ℂ :=
  ![numerator0 x r, numerator1 x r, numerator2 x r, numerator3 x r, numerator4 x r, numerator5 x r, numerator6 x r, numerator7 x r, numerator8 x r, numerator9 x r, numerator10 x r, numerator11 x r, numerator12 x r, numerator13 x r, numerator14 x r, numerator15 x r, numerator16 x r, numerator17 x r, numerator18 x r, numerator19 x r, numerator20 x r, numerator21 x r, numerator22 x r, numerator23 x r, numerator24 x r, numerator25 x r, numerator26 x r, numerator27 x r, numerator28 x r, numerator29 x r, numerator30 x r, numerator31 x r, numerator32 x r, numerator33 x r, numerator34 x r, numerator35 x r, numerator36 x r, numerator37 x r, numerator38 x r, numerator39 x r, numerator40 x r, numerator41 x r, numerator42 x r, numerator43 x r, numerator44 x r, numerator45 x r, numerator46 x r, numerator47 x r, numerator48 x r, numerator49 x r, numerator50 x r] a

def denominator (x r : ℂ) (a : Fin 6) : ℂ :=
  ![((3779136/390625) + (r ^ 8) + (x ^ 8) + ((-361584/15625) * (r ^ 2)) + ((-3564/625) * (x ^ 4)) + ((-189/25) * (r ^ 6)) + ((-36/25) * (x ^ 6)) + ((12636/625) * (r ^ 4)) + ((69984/15625) * (x ^ 2)) + (4 * (r ^ 2) * (x ^ 6)) + (4 * (r ^ 6) * (x ^ 2)) + (6 * (r ^ 4) * (x ^ 4)) + ((-414/25) * (r ^ 4) * (x ^ 2)) + ((-261/25) * (r ^ 2) * (x ^ 4)) + ((7776/625) * (r ^ 2) * (x ^ 2))),
    ((r ^ 8) + (x ^ 8) + ((-1944/625) * (x ^ 4)) + ((-18/5) * (r ^ 6)) + ((-18/25) * (x ^ 6)) + (4 * (r ^ 2) * (x ^ 6)) + (4 * (r ^ 6) * (x ^ 2)) + (6 * (r ^ 4) * (x ^ 4)) + ((-648/125) * (r ^ 2) * (x ^ 2)) + ((-198/25) * (r ^ 4) * (x ^ 2)) + ((-126/25) * (r ^ 2) * (x ^ 4))),
    ((81/100) + (x ^ 2) + ((-1) * (r ^ 2)) + ((-2) * Complex.I * r * x)),
    ((81/100) + (x ^ 2) + ((-1) * (r ^ 2)) + (2 * Complex.I * r * x)),
    ((81/100) + (x ^ 2) + ((-1) * (r ^ 2)) + (2 * Complex.I * r * x)),
    ((81/100) + (x ^ 2) + ((-1) * (r ^ 2)) + ((-2) * Complex.I * r * x))] a

def axialInverse (x r : ℂ) (a b : Fin 24) : ℂ :=
  let entry : ℂ := match a.val, b.val with
    | 0, 0 => numeratorPolynomial x r 0 / denominator x r 0
    | 0, 4 => numeratorPolynomial x r 1 / denominator x r 0
    | 0, 6 => numeratorPolynomial x r 1 / denominator x r 0
    | 0, 10 => numeratorPolynomial x r 2 / denominator x r 0
    | 0, 12 => numeratorPolynomial x r 3 / denominator x r 0
    | 0, 16 => numeratorPolynomial x r 4 / denominator x r 0
    | 0, 18 => numeratorPolynomial x r 5 / denominator x r 0
    | 0, 22 => numeratorPolynomial x r 6 / denominator x r 0
    | 4, 0 => numeratorPolynomial x r 1 / denominator x r 0
    | 4, 4 => numeratorPolynomial x r 7 / denominator x r 0
    | 4, 6 => numeratorPolynomial x r 8 / denominator x r 0
    | 4, 10 => numeratorPolynomial x r 1 / denominator x r 0
    | 4, 12 => numeratorPolynomial x r 5 / denominator x r 0
    | 4, 16 => numeratorPolynomial x r 9 / denominator x r 0
    | 4, 18 => numeratorPolynomial x r 10 / denominator x r 0
    | 4, 22 => numeratorPolynomial x r 4 / denominator x r 0
    | 6, 0 => numeratorPolynomial x r 1 / denominator x r 0
    | 6, 4 => numeratorPolynomial x r 8 / denominator x r 0
    | 6, 6 => numeratorPolynomial x r 7 / denominator x r 0
    | 6, 10 => numeratorPolynomial x r 1 / denominator x r 0
    | 6, 12 => numeratorPolynomial x r 5 / denominator x r 0
    | 6, 16 => numeratorPolynomial x r 11 / denominator x r 0
    | 6, 18 => numeratorPolynomial x r 12 / denominator x r 0
    | 6, 22 => numeratorPolynomial x r 4 / denominator x r 0
    | 10, 0 => numeratorPolynomial x r 2 / denominator x r 0
    | 10, 4 => numeratorPolynomial x r 1 / denominator x r 0
    | 10, 6 => numeratorPolynomial x r 1 / denominator x r 0
    | 10, 10 => numeratorPolynomial x r 0 / denominator x r 0
    | 10, 12 => numeratorPolynomial x r 13 / denominator x r 0
    | 10, 16 => numeratorPolynomial x r 4 / denominator x r 0
    | 10, 18 => numeratorPolynomial x r 5 / denominator x r 0
    | 10, 22 => numeratorPolynomial x r 14 / denominator x r 0
    | 12, 0 => numeratorPolynomial x r 14 / denominator x r 0
    | 12, 4 => numeratorPolynomial x r 4 / denominator x r 0
    | 12, 6 => numeratorPolynomial x r 4 / denominator x r 0
    | 12, 10 => numeratorPolynomial x r 6 / denominator x r 0
    | 12, 12 => numeratorPolynomial x r 0 / denominator x r 0
    | 12, 16 => numeratorPolynomial x r 15 / denominator x r 0
    | 12, 18 => numeratorPolynomial x r 1 / denominator x r 0
    | 12, 22 => numeratorPolynomial x r 16 / denominator x r 0
    | 16, 0 => numeratorPolynomial x r 5 / denominator x r 0
    | 16, 4 => numeratorPolynomial x r 12 / denominator x r 0
    | 16, 6 => numeratorPolynomial x r 10 / denominator x r 0
    | 16, 10 => numeratorPolynomial x r 5 / denominator x r 0
    | 16, 12 => numeratorPolynomial x r 15 / denominator x r 0
    | 16, 16 => numeratorPolynomial x r 7 / denominator x r 0
    | 16, 18 => numeratorPolynomial x r 17 / denominator x r 0
    | 16, 22 => numeratorPolynomial x r 1 / denominator x r 0
    | 18, 0 => numeratorPolynomial x r 4 / denominator x r 0
    | 18, 4 => numeratorPolynomial x r 11 / denominator x r 0
    | 18, 6 => numeratorPolynomial x r 9 / denominator x r 0
    | 18, 10 => numeratorPolynomial x r 4 / denominator x r 0
    | 18, 12 => numeratorPolynomial x r 1 / denominator x r 0
    | 18, 16 => numeratorPolynomial x r 17 / denominator x r 0
    | 18, 18 => numeratorPolynomial x r 7 / denominator x r 0
    | 18, 22 => numeratorPolynomial x r 15 / denominator x r 0
    | 22, 0 => numeratorPolynomial x r 13 / denominator x r 0
    | 22, 4 => numeratorPolynomial x r 5 / denominator x r 0
    | 22, 6 => numeratorPolynomial x r 5 / denominator x r 0
    | 22, 10 => numeratorPolynomial x r 3 / denominator x r 0
    | 22, 12 => numeratorPolynomial x r 16 / denominator x r 0
    | 22, 16 => numeratorPolynomial x r 1 / denominator x r 0
    | 22, 18 => numeratorPolynomial x r 15 / denominator x r 0
    | 22, 22 => numeratorPolynomial x r 0 / denominator x r 0
    | 1, 1 => numeratorPolynomial x r 18 / denominator x r 1
    | 1, 3 => numeratorPolynomial x r 19 / denominator x r 1
    | 1, 7 => numeratorPolynomial x r 20 / denominator x r 1
    | 1, 9 => numeratorPolynomial x r 21 / denominator x r 1
    | 1, 13 => numeratorPolynomial x r 22 / denominator x r 1
    | 1, 15 => numeratorPolynomial x r 23 / denominator x r 1
    | 1, 19 => numeratorPolynomial x r 24 / denominator x r 1
    | 1, 21 => numeratorPolynomial x r 25 / denominator x r 1
    | 3, 1 => numeratorPolynomial x r 19 / denominator x r 1
    | 3, 3 => numeratorPolynomial x r 26 / denominator x r 1
    | 3, 7 => numeratorPolynomial x r 27 / denominator x r 1
    | 3, 9 => numeratorPolynomial x r 20 / denominator x r 1
    | 3, 13 => numeratorPolynomial x r 28 / denominator x r 1
    | 3, 15 => numeratorPolynomial x r 29 / denominator x r 1
    | 3, 19 => numeratorPolynomial x r 30 / denominator x r 1
    | 3, 21 => numeratorPolynomial x r 31 / denominator x r 1
    | 7, 1 => numeratorPolynomial x r 20 / denominator x r 1
    | 7, 3 => numeratorPolynomial x r 27 / denominator x r 1
    | 7, 7 => numeratorPolynomial x r 26 / denominator x r 1
    | 7, 9 => numeratorPolynomial x r 19 / denominator x r 1
    | 7, 13 => numeratorPolynomial x r 32 / denominator x r 1
    | 7, 15 => numeratorPolynomial x r 33 / denominator x r 1
    | 7, 19 => numeratorPolynomial x r 34 / denominator x r 1
    | 7, 21 => numeratorPolynomial x r 35 / denominator x r 1
    | 9, 1 => numeratorPolynomial x r 21 / denominator x r 1
    | 9, 3 => numeratorPolynomial x r 20 / denominator x r 1
    | 9, 7 => numeratorPolynomial x r 19 / denominator x r 1
    | 9, 9 => numeratorPolynomial x r 18 / denominator x r 1
    | 9, 13 => numeratorPolynomial x r 36 / denominator x r 1
    | 9, 15 => numeratorPolynomial x r 37 / denominator x r 1
    | 9, 19 => numeratorPolynomial x r 38 / denominator x r 1
    | 9, 21 => numeratorPolynomial x r 39 / denominator x r 1
    | 13, 1 => numeratorPolynomial x r 39 / denominator x r 1
    | 13, 3 => numeratorPolynomial x r 35 / denominator x r 1
    | 13, 7 => numeratorPolynomial x r 31 / denominator x r 1
    | 13, 9 => numeratorPolynomial x r 25 / denominator x r 1
    | 13, 13 => numeratorPolynomial x r 40 / denominator x r 1
    | 13, 15 => numeratorPolynomial x r 41 / denominator x r 1
    | 13, 19 => numeratorPolynomial x r 42 / denominator x r 1
    | 13, 21 => numeratorPolynomial x r 43 / denominator x r 1
    | 15, 1 => numeratorPolynomial x r 38 / denominator x r 1
    | 15, 3 => numeratorPolynomial x r 34 / denominator x r 1
    | 15, 7 => numeratorPolynomial x r 30 / denominator x r 1
    | 15, 9 => numeratorPolynomial x r 24 / denominator x r 1
    | 15, 13 => numeratorPolynomial x r 41 / denominator x r 1
    | 15, 15 => numeratorPolynomial x r 44 / denominator x r 1
    | 15, 19 => numeratorPolynomial x r 45 / denominator x r 1
    | 15, 21 => numeratorPolynomial x r 42 / denominator x r 1
    | 19, 1 => numeratorPolynomial x r 37 / denominator x r 1
    | 19, 3 => numeratorPolynomial x r 33 / denominator x r 1
    | 19, 7 => numeratorPolynomial x r 29 / denominator x r 1
    | 19, 9 => numeratorPolynomial x r 23 / denominator x r 1
    | 19, 13 => numeratorPolynomial x r 42 / denominator x r 1
    | 19, 15 => numeratorPolynomial x r 45 / denominator x r 1
    | 19, 19 => numeratorPolynomial x r 44 / denominator x r 1
    | 19, 21 => numeratorPolynomial x r 41 / denominator x r 1
    | 21, 1 => numeratorPolynomial x r 36 / denominator x r 1
    | 21, 3 => numeratorPolynomial x r 32 / denominator x r 1
    | 21, 7 => numeratorPolynomial x r 28 / denominator x r 1
    | 21, 9 => numeratorPolynomial x r 22 / denominator x r 1
    | 21, 13 => numeratorPolynomial x r 43 / denominator x r 1
    | 21, 15 => numeratorPolynomial x r 42 / denominator x r 1
    | 21, 19 => numeratorPolynomial x r 41 / denominator x r 1
    | 21, 21 => numeratorPolynomial x r 40 / denominator x r 1
    | 2, 2 => numeratorPolynomial x r 46 / denominator x r 2
    | 2, 14 => numeratorPolynomial x r 47 / denominator x r 2
    | 14, 2 => numeratorPolynomial x r 48 / denominator x r 2
    | 14, 14 => numeratorPolynomial x r 46 / denominator x r 2
    | 5, 5 => numeratorPolynomial x r 46 / denominator x r 3
    | 5, 17 => numeratorPolynomial x r 49 / denominator x r 3
    | 17, 5 => numeratorPolynomial x r 50 / denominator x r 3
    | 17, 17 => numeratorPolynomial x r 46 / denominator x r 3
    | 8, 8 => numeratorPolynomial x r 46 / denominator x r 4
    | 8, 20 => numeratorPolynomial x r 50 / denominator x r 4
    | 20, 8 => numeratorPolynomial x r 49 / denominator x r 4
    | 20, 20 => numeratorPolynomial x r 46 / denominator x r 4
    | 11, 11 => numeratorPolynomial x r 46 / denominator x r 5
    | 11, 23 => numeratorPolynomial x r 48 / denominator x r 5
    | 23, 11 => numeratorPolynomial x r 47 / denominator x r 5
    | 23, 23 => numeratorPolynomial x r 46 / denominator x r 5
    | _, _ => 0
  entry / (SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse : ℂ)

def axialSourceMap (a : Fin 24) (b : Fin 97) : ℂ :=
  match a.val, b.val with
  | 0, 74 => ((3/25) * (Real.sqrt 15 : ℂ))
  | 0, 84 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 0, 94 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 4, 74 => ((3/25) * (Real.sqrt 15 : ℂ))
  | 4, 84 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 4, 94 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 6, 74 => ((3/25) * (Real.sqrt 15 : ℂ))
  | 6, 84 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 6, 94 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 10, 74 => ((3/25) * (Real.sqrt 15 : ℂ))
  | 10, 84 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 10, 94 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 12, 73 => ((3/25) * (Real.sqrt 15 : ℂ))
  | 12, 90 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 12, 95 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 13, 75 => ((-3/25) * (Real.sqrt 15 : ℂ))
  | 13, 79 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 13, 83 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 13, 86 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 13, 88 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 13, 93 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 15, 75 => ((-3/25) * (Real.sqrt 15 : ℂ))
  | 15, 79 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 15, 83 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 15, 86 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 15, 88 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 15, 93 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 16, 73 => ((-3/25) * (Real.sqrt 15 : ℂ))
  | 16, 90 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 16, 95 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 18, 73 => ((3/25) * (Real.sqrt 15 : ℂ))
  | 18, 90 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 18, 95 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 19, 75 => ((-3/25) * (Real.sqrt 15 : ℂ))
  | 19, 79 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 19, 83 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 19, 86 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 19, 88 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 19, 93 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 21, 75 => ((-3/25) * (Real.sqrt 15 : ℂ))
  | 21, 79 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 21, 83 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 21, 86 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 21, 88 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 21, 93 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 22, 73 => ((-3/25) * (Real.sqrt 15 : ℂ))
  | 22, 90 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 22, 95 => ((1/2) * (Real.sqrt 2 : ℂ))
  | _, _ => 0

end LowEnergy.MixedSpectatorDual24Data
