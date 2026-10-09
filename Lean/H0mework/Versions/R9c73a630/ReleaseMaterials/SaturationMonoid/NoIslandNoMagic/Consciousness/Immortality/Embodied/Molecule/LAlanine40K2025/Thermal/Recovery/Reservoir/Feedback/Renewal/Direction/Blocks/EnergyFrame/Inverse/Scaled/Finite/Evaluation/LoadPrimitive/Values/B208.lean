import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B138
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B139

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3329_pa : Scalar.QComplex := ((999999377569455326492640488782 : Int)/10^30,(-1115733257515985214195849273 : Int)/10^30)
theorem v3329_pa_checked : Scalar.distance (sourceCoefficient 44 52 1 0) v3329_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3329_pb : Scalar.QComplex := ((-481413819066880000591437 : Int)/10^30,(-431477251553843844395102904 : Int)/10^30)
theorem v3329_pb_checked : Scalar.distance (sourceCoefficient 44 52 1 1) v3329_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3329_pg : Scalar.QComplex := ((-93086371861995788299346 : Int)/10^30,(103859625553332209671 : Int)/10^30)
theorem v3329_pg_checked : Scalar.distance (sourceCoefficient 44 52 1 2) v3329_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3329_mb : Scalar.QComplex := ((-853759074891458105769596 : Int)/10^30,(-431476675456699825157655645 : Int)/10^30)
theorem v3329_mb_checked : Scalar.distance (sourceCoefficient 44 52 3 1) v3329_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3329_mg : Scalar.QComplex := ((-93086247575506098085823 : Int)/10^30,(184188933343991926483 : Int)/10^30)
theorem v3329_mg_checked : Scalar.distance (sourceCoefficient 44 52 3 2) v3329_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3329_upper : Scalar.QComplex := ((999995962533466673223327304496 : Int)/10^30,(-2841639802212367944515097870 : Int)/10^30)
theorem v3329_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 52 5) 1) 14) v3329_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3329 : Material (44 : Basis) (52 : Basis) where
  plus := ![v3329_pa,v3329_pb,v3329_pg]
  minus := ![(Primitive.Addresses.material3329 1).one,v3329_mb,v3329_mg]
  upper := v3329_upper
  lower := (Primitive.Addresses.material3329 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3329_pa_checked.trans (by decide +kernel)
    · exact v3329_pb_checked.trans (by decide +kernel)
    · exact v3329_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 52 Primitive.Addresses.material3329
    · exact v3329_mb_checked.trans (by decide +kernel)
    · exact v3329_mg_checked.trans (by decide +kernel)
  upper_error := v3329_upper_checked
  lower_error := reuse_lower_error 44 52 Primitive.Addresses.material3329

def v3330_pa : Scalar.QComplex := ((999999373431386135712607432495 : Int)/10^30,(-1119435945081426668997083067 : Int)/10^30)
theorem v3330_pa_checked : Scalar.distance (sourceCoefficient 44 53 1 0) v3330_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3330_pb : Scalar.QComplex := ((-483011445448264973734560 : Int)/10^30,(-431477249708396100714393535 : Int)/10^30)
theorem v3330_pb_checked : Scalar.distance (sourceCoefficient 44 53 1 1) v3330_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3330_pg : Scalar.QComplex := ((-93086371470329430878499 : Int)/10^30,(104204295512229976877 : Int)/10^30)
theorem v3330_pg_checked : Scalar.distance (sourceCoefficient 44 53 1 2) v3330_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3330_mb : Scalar.QComplex := ((-855356699085435475074960 : Int)/10^30,(-431476672232573155907394465 : Int)/10^30)
theorem v3330_mb_checked : Scalar.distance (sourceCoefficient 44 53 3 1) v3330_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3330_mg : Scalar.QComplex := ((-93086246886405235330182 : Int)/10^30,(184533602836562889341 : Int)/10^30)
theorem v3330_mg_checked : Scalar.distance (sourceCoefficient 44 53 3 2) v3330_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3330_upper : Scalar.QComplex := ((999995952004900812851300661874 : Int)/10^30,(-2845342477121159198244334073 : Int)/10^30)
theorem v3330_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 53 5) 1) 14) v3330_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3330 : Material (44 : Basis) (53 : Basis) where
  plus := ![v3330_pa,v3330_pb,v3330_pg]
  minus := ![(Primitive.Addresses.material3330 1).one,v3330_mb,v3330_mg]
  upper := v3330_upper
  lower := (Primitive.Addresses.material3330 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3330_pa_checked.trans (by decide +kernel)
    · exact v3330_pb_checked.trans (by decide +kernel)
    · exact v3330_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 53 Primitive.Addresses.material3330
    · exact v3330_mb_checked.trans (by decide +kernel)
    · exact v3330_mg_checked.trans (by decide +kernel)
  upper_error := v3330_upper_checked
  lower_error := reuse_lower_error 44 53 Primitive.Addresses.material3330

def v3331_pa : Scalar.QComplex := ((999999371322309704745390378154 : Int)/10^30,(-1121318413901631664571034396 : Int)/10^30)
theorem v3331_pa_checked : Scalar.distance (sourceCoefficient 44 54 1 0) v3331_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3331_pb : Scalar.QComplex := ((-483823688391362426489780 : Int)/10^30,(-431477248767134931946058109 : Int)/10^30)
theorem v3331_pb_checked : Scalar.distance (sourceCoefficient 44 54 1 1) v3331_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3331_pg : Scalar.QComplex := ((-93086371270632969584808 : Int)/10^30,(104379527810125032617 : Int)/10^30)
theorem v3331_pg_checked : Scalar.distance (sourceCoefficient 44 54 1 2) v3331_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3331_mb : Scalar.QComplex := ((-856168940913831762960939 : Int)/10^30,(-431476670590383259784675259 : Int)/10^30)
theorem v3331_mb_checked : Scalar.distance (sourceCoefficient 44 54 3 1) v3331_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3331_mg : Scalar.QComplex := ((-93086246535491267478903 : Int)/10^30,(184708834896881899960 : Int)/10^30)
theorem v3331_mg_checked : Scalar.distance (sourceCoefficient 44 54 3 2) v3331_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3331_upper : Scalar.QComplex := ((999995946646857115669193892100 : Int)/10^30,(-2847224939497573430513905769 : Int)/10^30)
theorem v3331_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 54 5) 1) 14) v3331_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3331 : Material (44 : Basis) (54 : Basis) where
  plus := ![v3331_pa,v3331_pb,v3331_pg]
  minus := ![(Primitive.Addresses.material3331 1).one,v3331_mb,v3331_mg]
  upper := v3331_upper
  lower := (Primitive.Addresses.material3331 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3331_pa_checked.trans (by decide +kernel)
    · exact v3331_pb_checked.trans (by decide +kernel)
    · exact v3331_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 54 Primitive.Addresses.material3331
    · exact v3331_mb_checked.trans (by decide +kernel)
    · exact v3331_mg_checked.trans (by decide +kernel)
  upper_error := v3331_upper_checked
  lower_error := reuse_lower_error 44 54 Primitive.Addresses.material3331

def v3332_pa : Scalar.QComplex := ((999999353999540045701464646244 : Int)/10^30,(-1136662000153081043229567297 : Int)/10^30)
theorem v3332_pa_checked : Scalar.distance (sourceCoefficient 44 55 1 0) v3332_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3332_pb : Scalar.QComplex := ((-490444100624411590686504 : Int)/10^30,(-431477241019094523490118342 : Int)/10^30)
theorem v3332_pb_checked : Scalar.distance (sourceCoefficient 44 55 1 1) v3332_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3332_pg : Scalar.QComplex := ((-93086369628599222187291 : Int)/10^30,(105807807440924881256 : Int)/10^30)
theorem v3332_pg_checked : Scalar.distance (sourceCoefficient 44 55 1 2) v3332_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3332_mb : Scalar.QComplex := ((-862789343995588971295820 : Int)/10^30,(-431476657129228151455154332 : Int)/10^30)
theorem v3332_mb_checked : Scalar.distance (sourceCoefficient 44 55 3 1) v3332_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3332_mg : Scalar.QComplex := ((-93086243660917137431954 : Int)/10^30,(186137112578866796900 : Int)/10^30)
theorem v3332_mg_checked : Scalar.distance (sourceCoefficient 44 55 3 2) v3332_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3332_upper : Scalar.QComplex := ((999995902842475346125514649141 : Int)/10^30,(-2862568472999024549767967554 : Int)/10^30)
theorem v3332_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 55 5) 1) 14) v3332_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3332 : Material (44 : Basis) (55 : Basis) where
  plus := ![v3332_pa,v3332_pb,v3332_pg]
  minus := ![(Primitive.Addresses.material3332 1).one,v3332_mb,v3332_mg]
  upper := v3332_upper
  lower := (Primitive.Addresses.material3332 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3332_pa_checked.trans (by decide +kernel)
    · exact v3332_pb_checked.trans (by decide +kernel)
    · exact v3332_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 55 Primitive.Addresses.material3332
    · exact v3332_mb_checked.trans (by decide +kernel)
    · exact v3332_mg_checked.trans (by decide +kernel)
  upper_error := v3332_upper_checked
  lower_error := reuse_lower_error 44 55 Primitive.Addresses.material3332

def v3333_pa : Scalar.QComplex := ((999999349853796252232322168449 : Int)/10^30,(-1140303461717734639285689483 : Int)/10^30)
theorem v3333_pa_checked : Scalar.distance (sourceCoefficient 44 56 1 0) v3333_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3333_pb : Scalar.QComplex := ((-492015309348879801902804 : Int)/10^30,(-431477239160381783964690952 : Int)/10^30)
theorem v3333_pb_checked : Scalar.distance (sourceCoefficient 44 56 1 1) v3333_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3333_pg : Scalar.QComplex := ((-93086369235144777144699 : Int)/10^30,(106146778088495638152 : Int)/10^30)
theorem v3333_pg_checked : Scalar.distance (sourceCoefficient 44 56 1 2) v3333_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3333_mb : Scalar.QComplex := ((-864360550531038985710280 : Int)/10^30,(-431476653914633739411405053 : Int)/10^30)
theorem v3333_mb_checked : Scalar.distance (sourceCoefficient 44 56 3 1) v3333_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3333_mg : Scalar.QComplex := ((-93086242974946436708111 : Int)/10^30,(186476082760689824440 : Int)/10^30)
theorem v3333_mg_checked : Scalar.distance (sourceCoefficient 44 56 3 2) v3333_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3333_upper : Scalar.QComplex := ((999995892411905417475238918605 : Int)/10^30,(-2866209921984971212807451356 : Int)/10^30)
theorem v3333_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 56 5) 1) 14) v3333_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3333 : Material (44 : Basis) (56 : Basis) where
  plus := ![v3333_pa,v3333_pb,v3333_pg]
  minus := ![(Primitive.Addresses.material3333 1).one,v3333_mb,v3333_mg]
  upper := v3333_upper
  lower := (Primitive.Addresses.material3333 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3333_pa_checked.trans (by decide +kernel)
    · exact v3333_pb_checked.trans (by decide +kernel)
    · exact v3333_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 56 Primitive.Addresses.material3333
    · exact v3333_mb_checked.trans (by decide +kernel)
    · exact v3333_mg_checked.trans (by decide +kernel)
  upper_error := v3333_upper_checked
  lower_error := reuse_lower_error 44 56 Primitive.Addresses.material3333

def v3334_pa : Scalar.QComplex := ((999999336354106975219583181495 : Int)/10^30,(-1152081310335207853023131209 : Int)/10^30)
theorem v3334_pa_checked : Scalar.distance (sourceCoefficient 44 57 1 0) v3334_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3334_pb : Scalar.QComplex := ((-497097185981981980504036 : Int)/10^30,(-431477233096370179333654675 : Int)/10^30)
theorem v3334_pb_checked : Scalar.distance (sourceCoefficient 44 57 1 1) v3334_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3334_pg : Scalar.QComplex := ((-93086367952704633543650 : Int)/10^30,(107243135936763973335 : Int)/10^30)
theorem v3334_pg_checked : Scalar.distance (sourceCoefficient 44 57 1 2) v3334_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3334_mb : Scalar.QComplex := ((-869442420038957338719554 : Int)/10^30,(-431476643465193737549006701 : Int)/10^30)
theorem v3334_mb_checked : Scalar.distance (sourceCoefficient 44 57 3 1) v3334_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3334_mg : Scalar.QComplex := ((-93086240746399325687049 : Int)/10^30,(187572439094045941716 : Int)/10^30)
theorem v3334_mg_checked : Scalar.distance (sourceCoefficient 44 57 3 2) v3334_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3334_upper : Scalar.QComplex := ((999995858584738010985210683934 : Int)/10^30,(-2877987729761483424224890133 : Int)/10^30)
theorem v3334_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 57 5) 1) 14) v3334_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3334 : Material (44 : Basis) (57 : Basis) where
  plus := ![v3334_pa,v3334_pb,v3334_pg]
  minus := ![(Primitive.Addresses.material3334 1).one,v3334_mb,v3334_mg]
  upper := v3334_upper
  lower := (Primitive.Addresses.material3334 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3334_pa_checked.trans (by decide +kernel)
    · exact v3334_pb_checked.trans (by decide +kernel)
    · exact v3334_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 57 Primitive.Addresses.material3334
    · exact v3334_mb_checked.trans (by decide +kernel)
    · exact v3334_mg_checked.trans (by decide +kernel)
  upper_error := v3334_upper_checked
  lower_error := reuse_lower_error 44 57 Primitive.Addresses.material3334

def v3335_pa : Scalar.QComplex := ((999999328971253870248547032418 : Int)/10^30,(-1158471856360751119247991850 : Int)/10^30)
theorem v3335_pa_checked : Scalar.distance (sourceCoefficient 44 58 1 0) v3335_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3335_pb : Scalar.QComplex := ((-499854562768952740247346 : Int)/10^30,(-431477229772698374980049245 : Int)/10^30)
theorem v3335_pb_checked : Scalar.distance (sourceCoefficient 44 58 1 1) v3335_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3335_pg : Scalar.QComplex := ((-93086367250560480296000 : Int)/10^30,(107838009033039414390 : Int)/10^30)
theorem v3335_pg_checked : Scalar.distance (sourceCoefficient 44 58 1 2) v3335_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3335_mb : Scalar.QComplex := ((-872199792931051627793109 : Int)/10^30,(-431476637762031191234970932 : Int)/10^30)
theorem v3335_mb_checked : Scalar.distance (sourceCoefficient 44 58 3 1) v3335_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3335_mg : Scalar.QComplex := ((-93086239530906743883738 : Int)/10^30,(188167311362904161130 : Int)/10^30)
theorem v3335_mg_checked : Scalar.distance (sourceCoefficient 44 58 3 2) v3335_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3335_upper : Scalar.QComplex := ((999995840172393207625657610609 : Int)/10^30,(-2884378253526924379693790632 : Int)/10^30)
theorem v3335_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 58 5) 1) 14) v3335_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3335 : Material (44 : Basis) (58 : Basis) where
  plus := ![v3335_pa,v3335_pb,v3335_pg]
  minus := ![(Primitive.Addresses.material3335 1).one,v3335_mb,v3335_mg]
  upper := v3335_upper
  lower := (Primitive.Addresses.material3335 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3335_pa_checked.trans (by decide +kernel)
    · exact v3335_pb_checked.trans (by decide +kernel)
    · exact v3335_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 58 Primitive.Addresses.material3335
    · exact v3335_mb_checked.trans (by decide +kernel)
    · exact v3335_mg_checked.trans (by decide +kernel)
  upper_error := v3335_upper_checked
  lower_error := reuse_lower_error 44 58 Primitive.Addresses.material3335

def v3336_pa : Scalar.QComplex := ((999999308467340992177706330604 : Int)/10^30,(-1176037771416473728944678912 : Int)/10^30)
theorem v3336_pa_checked : Scalar.distance (sourceCoefficient 44 59 1 0) v3336_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3336_pb : Scalar.QComplex := ((-507433859739412358339714 : Int)/10^30,(-431477220515757682376903050 : Int)/10^30)
theorem v3336_pb_checked : Scalar.distance (sourceCoefficient 44 59 1 1) v3336_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3336_pg : Scalar.QComplex := ((-93086365297701954300697 : Int)/10^30,(109473157298232739856 : Int)/10^30)
theorem v3336_pg_checked : Scalar.distance (sourceCoefficient 44 59 1 2) v3336_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3336_mb : Scalar.QComplex := ((-879779079091069692215337 : Int)/10^30,(-431476621964502018770970104 : Int)/10^30)
theorem v3336_mb_checked : Scalar.distance (sourceCoefficient 44 59 3 1) v3336_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3336_mg : Scalar.QComplex := ((-93086236166989636509133 : Int)/10^30,(189802457334028103046 : Int)/10^30)
theorem v3336_mg_checked : Scalar.distance (sourceCoefficient 44 59 3 2) v3336_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3336_upper : Scalar.QComplex := ((999995789351335048912855696070 : Int)/10^30,(-2901944107032386424118382774 : Int)/10^30)
theorem v3336_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 59 5) 1) 14) v3336_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3336 : Material (44 : Basis) (59 : Basis) where
  plus := ![v3336_pa,v3336_pb,v3336_pg]
  minus := ![(Primitive.Addresses.material3336 1).one,v3336_mb,v3336_mg]
  upper := v3336_upper
  lower := (Primitive.Addresses.material3336 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3336_pa_checked.trans (by decide +kernel)
    · exact v3336_pb_checked.trans (by decide +kernel)
    · exact v3336_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 59 Primitive.Addresses.material3336
    · exact v3336_mb_checked.trans (by decide +kernel)
    · exact v3336_mg_checked.trans (by decide +kernel)
  upper_error := v3336_upper_checked
  lower_error := reuse_lower_error 44 59 Primitive.Addresses.material3336

def v3337_pa : Scalar.QComplex := ((999999284430880389597743616177 : Int)/10^30,(-1196301687360525113775709231 : Int)/10^30)
theorem v3337_pa_checked : Scalar.distance (sourceCoefficient 44 60 1 0) v3337_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3337_pb : Scalar.QComplex := ((-516177283282363106119770 : Int)/10^30,(-431477209616507524645310453 : Int)/10^30)
theorem v3337_pb_checked : Scalar.distance (sourceCoefficient 44 60 1 1) v3337_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3337_pg : Scalar.QComplex := ((-93086363003272387915016 : Int)/10^30,(111359452816454727963 : Int)/10^30)
theorem v3337_pg_checked : Scalar.distance (sourceCoefficient 44 60 1 2) v3337_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3337_mb : Scalar.QComplex := ((-888522489972882258640833 : Int)/10^30,(-431476603520075190940069310 : Int)/10^30)
theorem v3337_mb_checked : Scalar.distance (sourceCoefficient 44 60 3 1) v3337_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3337_mg : Scalar.QComplex := ((-93086232244772847815305 : Int)/10^30,(191688750169906683236 : Int)/10^30)
theorem v3337_mg_checked : Scalar.distance (sourceCoefficient 44 60 3 2) v3337_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3337_upper : Scalar.QComplex := ((999995730341229654478962638240 : Int)/10^30,(-2922207951310964947682476975 : Int)/10^30)
theorem v3337_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 60 5) 1) 14) v3337_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3337 : Material (44 : Basis) (60 : Basis) where
  plus := ![v3337_pa,v3337_pb,v3337_pg]
  minus := ![(Primitive.Addresses.material3337 1).one,v3337_mb,v3337_mg]
  upper := v3337_upper
  lower := (Primitive.Addresses.material3337 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3337_pa_checked.trans (by decide +kernel)
    · exact v3337_pb_checked.trans (by decide +kernel)
    · exact v3337_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 60 Primitive.Addresses.material3337
    · exact v3337_mb_checked.trans (by decide +kernel)
    · exact v3337_mg_checked.trans (by decide +kernel)
  upper_error := v3337_upper_checked
  lower_error := reuse_lower_error 44 60 Primitive.Addresses.material3337

def v3338_pa : Scalar.QComplex := ((999999277404181446554541530571 : Int)/10^30,(-1202161018733419889296843404 : Int)/10^30)
theorem v3338_pa_checked : Scalar.distance (sourceCoefficient 44 61 1 0) v3338_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3338_pb : Scalar.QComplex := ((-518705452845649595640023 : Int)/10^30,(-431477206420949130738561631 : Int)/10^30)
theorem v3338_pb_checked : Scalar.distance (sourceCoefficient 44 61 1 1) v3338_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3338_pg : Scalar.QComplex := ((-93086362331524309225289 : Int)/10^30,(111904877032649726156 : Int)/10^30)
theorem v3338_pg_checked : Scalar.distance (sourceCoefficient 44 61 1 2) v3338_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3338_mb : Scalar.QComplex := ((-891050655837192705358419 : Int)/10^30,(-431476598142821518299794692 : Int)/10^30)
theorem v3338_mb_checked : Scalar.distance (sourceCoefficient 44 61 3 1) v3338_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3338_mg : Scalar.QComplex := ((-93086231102348485666607 : Int)/10^30,(192234173603326981123 : Int)/10^30)
theorem v3338_mg_checked : Scalar.distance (sourceCoefficient 44 61 3 2) v3338_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3338_upper : Scalar.QComplex := ((999995713201866781651913616494 : Int)/10^30,(-2928067261829629010145320511 : Int)/10^30)
theorem v3338_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 61 5) 1) 14) v3338_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3338 : Material (44 : Basis) (61 : Basis) where
  plus := ![v3338_pa,v3338_pb,v3338_pg]
  minus := ![(Primitive.Addresses.material3338 1).one,v3338_mb,v3338_mg]
  upper := v3338_upper
  lower := (Primitive.Addresses.material3338 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3338_pa_checked.trans (by decide +kernel)
    · exact v3338_pb_checked.trans (by decide +kernel)
    · exact v3338_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 61 Primitive.Addresses.material3338
    · exact v3338_mb_checked.trans (by decide +kernel)
    · exact v3338_mg_checked.trans (by decide +kernel)
  upper_error := v3338_upper_checked
  lower_error := reuse_lower_error 44 61 Primitive.Addresses.material3338

def v3339_pa : Scalar.QComplex := ((999999267133509367061270814727 : Int)/10^30,(-1210674375780946462223336596 : Int)/10^30)
theorem v3339_pa_checked : Scalar.distance (sourceCoefficient 44 62 1 0) v3339_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3339_pb : Scalar.QComplex := ((-522378774717504102932172 : Int)/10^30,(-431477201742742841442746261 : Int)/10^30)
theorem v3339_pb_checked : Scalar.distance (sourceCoefficient 44 62 1 1) v3339_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3339_pg : Scalar.QComplex := ((-93086361348858974579556 : Int)/10^30,(112697355011864531748 : Int)/10^30)
theorem v3339_pg_checked : Scalar.distance (sourceCoefficient 44 62 1 2) v3339_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3339_mb : Scalar.QComplex := ((-894723972304220271583677 : Int)/10^30,(-431476590294705635779222236 : Int)/10^30)
theorem v3339_mb_checked : Scalar.distance (sourceCoefficient 44 62 3 1) v3339_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3339_mg : Scalar.QComplex := ((-93086229435810712732949 : Int)/10^30,(193026650439470090825 : Int)/10^30)
theorem v3339_mg_checked : Scalar.distance (sourceCoefficient 44 62 3 2) v3339_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3339_upper : Scalar.QComplex := ((999995688237928060805636726964 : Int)/10^30,(-2936580588471262048836658066 : Int)/10^30)
theorem v3339_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 62 5) 1) 14) v3339_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3339 : Material (44 : Basis) (62 : Basis) where
  plus := ![v3339_pa,v3339_pb,v3339_pg]
  minus := ![(Primitive.Addresses.material3339 1).one,v3339_mb,v3339_mg]
  upper := v3339_upper
  lower := (Primitive.Addresses.material3339 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3339_pa_checked.trans (by decide +kernel)
    · exact v3339_pb_checked.trans (by decide +kernel)
    · exact v3339_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 62 Primitive.Addresses.material3339
    · exact v3339_mb_checked.trans (by decide +kernel)
    · exact v3339_mg_checked.trans (by decide +kernel)
  upper_error := v3339_upper_checked
  lower_error := reuse_lower_error 44 62 Primitive.Addresses.material3339

def v3340_pa : Scalar.QComplex := ((999999236807227677314482336649 : Int)/10^30,(-1235469531061840193101607179 : Int)/10^30)
theorem v3340_pa_checked : Scalar.distance (sourceCoefficient 44 63 1 0) v3340_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3340_pb : Scalar.QComplex := ((-533077325814619332756316 : Int)/10^30,(-431477187879896448305097833 : Int)/10^30)
theorem v3340_pb_checked : Scalar.distance (sourceCoefficient 44 63 1 1) v3340_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3340_pg : Scalar.QComplex := ((-93086358441999609422172 : Int)/10^30,(115005447383917847679 : Int)/10^30)
theorem v3340_pg_checked : Scalar.distance (sourceCoefficient 44 63 1 2) v3340_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3340_mb : Scalar.QComplex := ((-905422507454763902158610 : Int)/10^30,(-431476567199496652456898303 : Int)/10^30)
theorem v3340_mb_checked : Scalar.distance (sourceCoefficient 44 63 3 1) v3340_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3340_mg : Scalar.QComplex := ((-93086224537172665471679 : Int)/10^30,(195334739443626419563 : Int)/10^30)
theorem v3340_mg_checked : Scalar.distance (sourceCoefficient 44 63 3 2) v3340_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3340_upper : Scalar.QComplex := ((999995615117502922586212976696 : Int)/10^30,(-2961375654482273614645967412 : Int)/10^30)
theorem v3340_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 63 5) 1) 14) v3340_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3340 : Material (44 : Basis) (63 : Basis) where
  plus := ![v3340_pa,v3340_pb,v3340_pg]
  minus := ![(Primitive.Addresses.material3340 1).one,v3340_mb,v3340_mg]
  upper := v3340_upper
  lower := (Primitive.Addresses.material3340 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3340_pa_checked.trans (by decide +kernel)
    · exact v3340_pb_checked.trans (by decide +kernel)
    · exact v3340_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 63 Primitive.Addresses.material3340
    · exact v3340_mb_checked.trans (by decide +kernel)
    · exact v3340_mg_checked.trans (by decide +kernel)
  upper_error := v3340_upper_checked
  lower_error := reuse_lower_error 44 63 Primitive.Addresses.material3340

def v3341_pa : Scalar.QComplex := ((999999192397658913645895700842 : Int)/10^30,(-1270906774689303039297256671 : Int)/10^30)
theorem v3341_pa_checked : Scalar.distance (sourceCoefficient 44 64 1 0) v3341_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3341_pb : Scalar.QComplex := ((-548367698102966732123417 : Int)/10^30,(-431477167453127010494329114 : Int)/10^30)
theorem v3341_pb_checked : Scalar.distance (sourceCoefficient 44 64 1 1) v3341_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3341_pg : Scalar.QComplex := ((-93086354171612443349673 : Int)/10^30,(118304173690557752384 : Int)/10^30)
theorem v3341_pg_checked : Scalar.distance (sourceCoefficient 44 64 1 2) v3341_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3341_mb : Scalar.QComplex := ((-920712856422424856751995 : Int)/10^30,(-431476533577832188426008550 : Int)/10^30)
theorem v3341_mb_checked : Scalar.distance (sourceCoefficient 44 64 3 1) v3341_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3341_mg : Scalar.QComplex := ((-93086217420134855946957 : Int)/10^30,(198633460836847967844 : Int)/10^30)
theorem v3341_mg_checked : Scalar.distance (sourceCoefficient 44 64 3 2) v3341_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3341_upper : Scalar.QComplex := ((999995509546532642381631673769 : Int)/10^30,(-2996812768683237947304466921 : Int)/10^30)
theorem v3341_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 64 5) 1) 14) v3341_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3341 : Material (44 : Basis) (64 : Basis) where
  plus := ![v3341_pa,v3341_pb,v3341_pg]
  minus := ![(Primitive.Addresses.material3341 1).one,v3341_mb,v3341_mg]
  upper := v3341_upper
  lower := (Primitive.Addresses.material3341 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3341_pa_checked.trans (by decide +kernel)
    · exact v3341_pb_checked.trans (by decide +kernel)
    · exact v3341_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 64 Primitive.Addresses.material3341
    · exact v3341_mb_checked.trans (by decide +kernel)
    · exact v3341_mg_checked.trans (by decide +kernel)
  upper_error := v3341_upper_checked
  lower_error := reuse_lower_error 44 64 Primitive.Addresses.material3341

def v3342_pa : Scalar.QComplex := ((999999146040641018299190263706 : Int)/10^30,(-1306873363687857411614444808 : Int)/10^30)
theorem v3342_pa_checked : Scalar.distance (sourceCoefficient 44 65 1 0) v3342_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3342_pb : Scalar.QComplex := ((-563886470660711657740884 : Int)/10^30,(-431477145982497066978330812 : Int)/10^30)
theorem v3342_pb_checked : Scalar.distance (sourceCoefficient 44 65 1 1) v3342_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3342_pg : Scalar.QComplex := ((-93086349697984142740120 : Int)/10^30,(121652174829241942413 : Int)/10^30)
theorem v3342_pg_checked : Scalar.distance (sourceCoefficient 44 65 1 2) v3342_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3342_mb : Scalar.QComplex := ((-936231604673634876199399 : Int)/10^30,(-431476498715208461643068067 : Int)/10^30)
theorem v3342_mb_checked : Scalar.distance (sourceCoefficient 44 65 3 1) v3342_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3342_mg : Scalar.QComplex := ((-93086210057334026762979 : Int)/10^30,(201981456868378584042 : Int)/10^30)
theorem v3342_mg_checked : Scalar.distance (sourceCoefficient 44 65 3 2) v3342_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3342_upper : Scalar.QComplex := ((999995401114514042328615092923 : Int)/10^30,(-3032779224105775527047674749 : Int)/10^30)
theorem v3342_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 65 5) 1) 14) v3342_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3342 : Material (44 : Basis) (65 : Basis) where
  plus := ![v3342_pa,v3342_pb,v3342_pg]
  minus := ![(Primitive.Addresses.material3342 1).one,v3342_mb,v3342_mg]
  upper := v3342_upper
  lower := (Primitive.Addresses.material3342 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3342_pa_checked.trans (by decide +kernel)
    · exact v3342_pb_checked.trans (by decide +kernel)
    · exact v3342_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 65 Primitive.Addresses.material3342
    · exact v3342_mb_checked.trans (by decide +kernel)
    · exact v3342_mg_checked.trans (by decide +kernel)
  upper_error := v3342_upper_checked
  lower_error := reuse_lower_error 44 65 Primitive.Addresses.material3342

def v3343_pa : Scalar.QComplex := ((999999122901257686559490244223 : Int)/10^30,(-1324460914985669651373679964 : Int)/10^30)
theorem v3343_pa_checked : Scalar.distance (sourceCoefficient 44 66 1 0) v3343_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3343_pb : Scalar.QComplex := ((-571475102539022956510780 : Int)/10^30,(-431477135212489433001631312 : Int)/10^30)
theorem v3343_pb_checked : Scalar.distance (sourceCoefficient 44 66 1 1) v3343_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3343_pg : Scalar.QComplex := ((-93086347459248748233284 : Int)/10^30,(123289337065473043270 : Int)/10^30)
theorem v3343_pg_checked : Scalar.distance (sourceCoefficient 44 66 1 2) v3343_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3343_mb : Scalar.QComplex := ((-943820224432320184079575 : Int)/10^30,(-431476481396557306142128952 : Int)/10^30)
theorem v3343_mb_checked : Scalar.distance (sourceCoefficient 44 66 3 1) v3343_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3343_mg : Scalar.QComplex := ((-93086206405802191022151 : Int)/10^30,(203618616563091545780 : Int)/10^30)
theorem v3343_mg_checked : Scalar.distance (sourceCoefficient 44 66 3 2) v3343_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3343_upper : Scalar.QComplex := ((999995347620647164148458633232 : Int)/10^30,(-3050366709272519645493295118 : Int)/10^30)
theorem v3343_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 66 5) 1) 14) v3343_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3343 : Material (44 : Basis) (66 : Basis) where
  plus := ![v3343_pa,v3343_pb,v3343_pg]
  minus := ![(Primitive.Addresses.material3343 1).one,v3343_mb,v3343_mg]
  upper := v3343_upper
  lower := (Primitive.Addresses.material3343 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3343_pa_checked.trans (by decide +kernel)
    · exact v3343_pb_checked.trans (by decide +kernel)
    · exact v3343_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 66 Primitive.Addresses.material3343
    · exact v3343_mb_checked.trans (by decide +kernel)
    · exact v3343_mg_checked.trans (by decide +kernel)
  upper_error := v3343_upper_checked
  lower_error := reuse_lower_error 44 66 Primitive.Addresses.material3343

def v3344_pa : Scalar.QComplex := ((999999083371308738797087288087 : Int)/10^30,(-1353978043512614787260402547 : Int)/10^30)
theorem v3344_pa_checked : Scalar.distance (sourceCoefficient 44 67 1 0) v3344_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3344_pb : Scalar.QComplex := ((-584211077845030502940505 : Int)/10^30,(-431477116737271379185468032 : Int)/10^30)
theorem v3344_pb_checked : Scalar.distance (sourceCoefficient 44 67 1 1) v3344_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3344_pg : Scalar.QComplex := ((-93086343626487424100296 : Int)/10^30,(126036980950247300621 : Int)/10^30)
theorem v3344_pg_checked : Scalar.distance (sourceCoefficient 44 67 1 2) v3344_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3344_mb : Scalar.QComplex := ((-956556179052860973745773 : Int)/10^30,(-431476451930773049443982276 : Int)/10^30)
theorem v3344_mb_checked : Scalar.distance (sourceCoefficient 44 67 3 1) v3344_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3344_mg : Scalar.QComplex := ((-93086200201949370727967 : Int)/10^30,(206366256117292009736 : Int)/10^30)
theorem v3344_mg_checked : Scalar.distance (sourceCoefficient 44 67 3 2) v3344_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3344_upper : Scalar.QComplex := ((999995257146871027076544685890 : Int)/10^30,(-3079883725612063411095674921 : Int)/10^30)
theorem v3344_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 44 67 5) 1) 14) v3344_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3344 : Material (44 : Basis) (67 : Basis) where
  plus := ![v3344_pa,v3344_pb,v3344_pg]
  minus := ![(Primitive.Addresses.material3344 1).one,v3344_mb,v3344_mg]
  upper := v3344_upper
  lower := (Primitive.Addresses.material3344 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3344_pa_checked.trans (by decide +kernel)
    · exact v3344_pb_checked.trans (by decide +kernel)
    · exact v3344_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 44 67 Primitive.Addresses.material3344
    · exact v3344_mb_checked.trans (by decide +kernel)
    · exact v3344_mg_checked.trans (by decide +kernel)
  upper_error := v3344_upper_checked
  lower_error := reuse_lower_error 44 67 Primitive.Addresses.material3344

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
