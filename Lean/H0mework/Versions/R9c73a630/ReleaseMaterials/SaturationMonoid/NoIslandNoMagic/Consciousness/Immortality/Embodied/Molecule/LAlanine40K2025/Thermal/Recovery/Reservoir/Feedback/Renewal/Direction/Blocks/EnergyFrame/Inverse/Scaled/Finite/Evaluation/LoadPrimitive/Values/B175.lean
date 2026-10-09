import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B116
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B117

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2801_pa : Scalar.QComplex := ((999999705213767447504250298204 : Int)/10^30,(-767836166252976518981453000 : Int)/10^30)
theorem v2801_pa_checked : Scalar.distance (sourceCoefficient 35 37 1 0) v2801_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2801_pb : Scalar.QComplex := ((-331304045520170244672606 : Int)/10^30,(-431477393768848844880054051 : Int)/10^30)
theorem v2801_pb_checked : Scalar.distance (sourceCoefficient 35 37 1 1) v2801_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2801_pg : Scalar.QComplex := ((-93086402452260598848292 : Int)/10^30,(71475127459108995190 : Int)/10^30)
theorem v2801_pg_checked : Scalar.distance (sourceCoefficient 35 37 1 2) v2801_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2801_mb : Scalar.QComplex := ((-703649479962621586213079 : Int)/10^30,(-431476947209625750075403503 : Int)/10^30)
theorem v2801_mb_checked : Scalar.distance (sourceCoefficient 35 37 3 1) v2801_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2801_mg : Scalar.QComplex := ((-93086306112122830145291 : Int)/10^30,(151804473706018194281 : Int)/10^30)
theorem v2801_mg_checked : Scalar.distance (sourceCoefficient 35 37 3 2) v2801_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2801_upper : Scalar.QComplex := ((999996890616109348894292260585 : Int)/10^30,(-2493743794585568883530751821 : Int)/10^30)
theorem v2801_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 37 5) 1) 14) v2801_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2801 : Material (35 : Basis) (37 : Basis) where
  plus := ![v2801_pa,v2801_pb,v2801_pg]
  minus := ![(Primitive.Addresses.material2801 1).one,v2801_mb,v2801_mg]
  upper := v2801_upper
  lower := (Primitive.Addresses.material2801 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2801_pa_checked.trans (by decide +kernel)
    · exact v2801_pb_checked.trans (by decide +kernel)
    · exact v2801_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 37 Primitive.Addresses.material2801
    · exact v2801_mb_checked.trans (by decide +kernel)
    · exact v2801_mg_checked.trans (by decide +kernel)
  upper_error := v2801_upper_checked
  lower_error := reuse_lower_error 35 37 Primitive.Addresses.material2801

def v2802_pa : Scalar.QComplex := ((999999687050936052588857145048 : Int)/10^30,(-791137175183738701897882726 : Int)/10^30)
theorem v2802_pa_checked : Scalar.distance (sourceCoefficient 35 38 1 0) v2802_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2802_pb : Scalar.QComplex := ((-341357906997566918440304 : Int)/10^30,(-431477385815740939915044111 : Int)/10^30)
theorem v2802_pb_checked : Scalar.distance (sourceCoefficient 35 38 1 1) v2802_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2802_pg : Scalar.QComplex := ((-93086400749007172577244 : Int)/10^30,(73644135183454163884 : Int)/10^30)
theorem v2802_pg_checked : Scalar.distance (sourceCoefficient 35 38 1 2) v2802_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2802_mb : Scalar.QComplex := ((-713703330833332220475924 : Int)/10^30,(-431476930580491160534489702 : Int)/10^30)
theorem v2802_mb_checked : Scalar.distance (sourceCoefficient 35 38 3 1) v2802_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2802_mg : Scalar.QComplex := ((-93086302537114060444993 : Int)/10^30,(153973479152911663466 : Int)/10^30)
theorem v2802_mg_checked : Scalar.distance (sourceCoefficient 35 38 3 2) v2802_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2802_upper : Scalar.QComplex := ((999996832237877441904878844643 : Int)/10^30,(-2517044737464816124427629659 : Int)/10^30)
theorem v2802_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 38 5) 1) 14) v2802_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2802 : Material (35 : Basis) (38 : Basis) where
  plus := ![v2802_pa,v2802_pb,v2802_pg]
  minus := ![(Primitive.Addresses.material2802 1).one,v2802_mb,v2802_mg]
  upper := v2802_upper
  lower := (Primitive.Addresses.material2802 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2802_pa_checked.trans (by decide +kernel)
    · exact v2802_pb_checked.trans (by decide +kernel)
    · exact v2802_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 38 Primitive.Addresses.material2802
    · exact v2802_mb_checked.trans (by decide +kernel)
    · exact v2802_mg_checked.trans (by decide +kernel)
  upper_error := v2802_upper_checked
  lower_error := reuse_lower_error 35 38 Primitive.Addresses.material2802

def v2803_pa : Scalar.QComplex := ((999999676265463453767024286720 : Int)/10^30,(-804654564573156322949656496 : Int)/10^30)
theorem v2803_pa_checked : Scalar.distance (sourceCoefficient 35 39 1 0) v2803_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2803_pb : Scalar.QComplex := ((-347190356576559947792585 : Int)/10^30,(-431477381058820141104622781 : Int)/10^30)
theorem v2803_pb_checked : Scalar.distance (sourceCoefficient 35 39 1 1) v2803_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2803_pg : Scalar.QComplex := ((-93086399733890480842515 : Int)/10^30,(74902420694056869056 : Int)/10^30)
theorem v2803_pg_checked : Scalar.distance (sourceCoefficient 35 39 1 2) v2803_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2803_mb : Scalar.QComplex := ((-719535774135629309841483 : Int)/10^30,(-431476920790430830049857112 : Int)/10^30)
theorem v2803_mb_checked : Scalar.distance (sourceCoefficient 35 39 3 1) v2803_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2803_mg : Scalar.QComplex := ((-93086300436154022110135 : Int)/10^30,(155231763318997180743 : Int)/10^30)
theorem v2803_mg_checked : Scalar.distance (sourceCoefficient 35 39 3 2) v2803_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2803_upper : Scalar.QComplex := ((999996798122633108628889297861 : Int)/10^30,(-2530562088106922858905353478 : Int)/10^30)
theorem v2803_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 39 5) 1) 14) v2803_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2803 : Material (35 : Basis) (39 : Basis) where
  plus := ![v2803_pa,v2803_pb,v2803_pg]
  minus := ![(Primitive.Addresses.material2803 1).one,v2803_mb,v2803_mg]
  upper := v2803_upper
  lower := (Primitive.Addresses.material2803 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2803_pa_checked.trans (by decide +kernel)
    · exact v2803_pb_checked.trans (by decide +kernel)
    · exact v2803_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 39 Primitive.Addresses.material2803
    · exact v2803_mb_checked.trans (by decide +kernel)
    · exact v2803_mg_checked.trans (by decide +kernel)
  upper_error := v2803_upper_checked
  lower_error := reuse_lower_error 35 39 Primitive.Addresses.material2803

def v2804_pa : Scalar.QComplex := ((999999657712789324477213466251 : Int)/10^30,(-827390055651209154075282810 : Int)/10^30)
theorem v2804_pa_checked : Scalar.distance (sourceCoefficient 35 40 1 0) v2804_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2804_pb : Scalar.QComplex := ((-357000209707091207889904 : Int)/10^30,(-431477372820855577863654582 : Int)/10^30)
theorem v2804_pb_checked : Scalar.distance (sourceCoefficient 35 40 1 1) v2804_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2804_pg : Scalar.QComplex := ((-93086397981765207884196 : Int)/10^30,(77018786369048874710 : Int)/10^30)
theorem v2804_pg_checked : Scalar.distance (sourceCoefficient 35 40 1 2) v2804_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2804_mb : Scalar.QComplex := ((-729345616504511523079787 : Int)/10^30,(-431476904087007901915004581 : Int)/10^30)
theorem v2804_mb_checked : Scalar.distance (sourceCoefficient 35 40 3 1) v2804_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2804_mg : Scalar.QComplex := ((-93086296857701141601678 : Int)/10^30,(157348126693964325138 : Int)/10^30)
theorem v2804_mg_checked : Scalar.distance (sourceCoefficient 35 40 3 2) v2804_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2804_upper : Scalar.QComplex := ((999996740330591558287520321808 : Int)/10^30,(-2553297513302899965954899050 : Int)/10^30)
theorem v2804_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 40 5) 1) 14) v2804_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2804 : Material (35 : Basis) (40 : Basis) where
  plus := ![v2804_pa,v2804_pb,v2804_pg]
  minus := ![(Primitive.Addresses.material2804 1).one,v2804_mb,v2804_mg]
  upper := v2804_upper
  lower := (Primitive.Addresses.material2804 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2804_pa_checked.trans (by decide +kernel)
    · exact v2804_pb_checked.trans (by decide +kernel)
    · exact v2804_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 40 Primitive.Addresses.material2804
    · exact v2804_mb_checked.trans (by decide +kernel)
    · exact v2804_mg_checked.trans (by decide +kernel)
  upper_error := v2804_upper_checked
  lower_error := reuse_lower_error 35 40 Primitive.Addresses.material2804

def v2805_pa : Scalar.QComplex := ((999999645623983416810352668877 : Int)/10^30,(-841874044963982819004620366 : Int)/10^30)
theorem v2805_pa_checked : Scalar.distance (sourceCoefficient 35 41 1 0) v2805_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2805_pb : Scalar.QComplex := ((-363249725345311827450875 : Int)/10^30,(-431477367417666063192693420 : Int)/10^30)
theorem v2805_pb_checked : Scalar.distance (sourceCoefficient 35 41 1 1) v2805_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2805_pg : Scalar.QComplex := ((-93086396836274584786627 : Int)/10^30,(78367049207079707206 : Int)/10^30)
theorem v2805_pg_checked : Scalar.distance (sourceCoefficient 35 41 1 2) v2805_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2805_mb : Scalar.QComplex := ((-735595125153042653017891 : Int)/10^30,(-431476893290769871049814974 : Int)/10^30)
theorem v2805_mb_checked : Scalar.distance (sourceCoefficient 35 41 3 1) v2805_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2805_mg : Scalar.QComplex := ((-93086294548720839306073 : Int)/10^30,(158696388041468467629 : Int)/10^30)
theorem v2805_mg_checked : Scalar.distance (sourceCoefficient 35 41 3 2) v2805_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2805_upper : Scalar.QComplex := ((999996703243752078875890294750 : Int)/10^30,(-2567781460179290649682083827 : Int)/10^30)
theorem v2805_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 41 5) 1) 14) v2805_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2805 : Material (35 : Basis) (41 : Basis) where
  plus := ![v2805_pa,v2805_pb,v2805_pg]
  minus := ![(Primitive.Addresses.material2805 1).one,v2805_mb,v2805_mg]
  upper := v2805_upper
  lower := (Primitive.Addresses.material2805 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2805_pa_checked.trans (by decide +kernel)
    · exact v2805_pb_checked.trans (by decide +kernel)
    · exact v2805_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 41 Primitive.Addresses.material2805
    · exact v2805_mb_checked.trans (by decide +kernel)
    · exact v2805_mg_checked.trans (by decide +kernel)
  upper_error := v2805_upper_checked
  lower_error := reuse_lower_error 35 41 Primitive.Addresses.material2805

def v2806_pa : Scalar.QComplex := ((999999635719567964235131580209 : Int)/10^30,(-853557690710649371673431992 : Int)/10^30)
theorem v2806_pa_checked : Scalar.distance (sourceCoefficient 35 42 1 0) v2806_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2806_pb : Scalar.QComplex := ((-368290955692796164587901 : Int)/10^30,(-431477362971187797587054465 : Int)/10^30)
theorem v2806_pb_checked : Scalar.distance (sourceCoefficient 35 42 1 1) v2806_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2806_pg : Scalar.QComplex := ((-93086395895652370474706 : Int)/10^30,(79454638061040187261 : Int)/10^30)
theorem v2806_pg_checked : Scalar.distance (sourceCoefficient 35 42 1 2) v2806_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2806_mb : Scalar.QComplex := ((-740636349786336054907188 : Int)/10^30,(-431476884493938519778676435 : Int)/10^30)
theorem v2806_mb_checked : Scalar.distance (sourceCoefficient 35 42 3 1) v2806_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2806_mg : Scalar.QComplex := ((-93086292669558777446538 : Int)/10^30,(159783975678755305189 : Int)/10^30)
theorem v2806_mg_checked : Scalar.distance (sourceCoefficient 35 42 3 2) v2806_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2806_upper : Scalar.QComplex := ((999996673174438751079964239933 : Int)/10^30,(-2579465071430416770536506330 : Int)/10^30)
theorem v2806_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 42 5) 1) 14) v2806_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2806 : Material (35 : Basis) (42 : Basis) where
  plus := ![v2806_pa,v2806_pb,v2806_pg]
  minus := ![(Primitive.Addresses.material2806 1).one,v2806_mb,v2806_mg]
  upper := v2806_upper
  lower := (Primitive.Addresses.material2806 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2806_pa_checked.trans (by decide +kernel)
    · exact v2806_pb_checked.trans (by decide +kernel)
    · exact v2806_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 42 Primitive.Addresses.material2806
    · exact v2806_mb_checked.trans (by decide +kernel)
    · exact v2806_mg_checked.trans (by decide +kernel)
  upper_error := v2806_upper_checked
  lower_error := reuse_lower_error 35 42 Primitive.Addresses.material2806

def v2807_pa : Scalar.QComplex := ((999999622388601633484376094163 : Int)/10^30,(-869035473466223397925064082 : Int)/10^30)
theorem v2807_pa_checked : Scalar.distance (sourceCoefficient 35 43 1 0) v2807_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2807_pb : Scalar.QComplex := ((-374969270788216038630445 : Int)/10^30,(-431477356959835530591727470 : Int)/10^30)
theorem v2807_pb_checked : Scalar.distance (sourceCoefficient 35 43 1 1) v2807_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2807_pg : Scalar.QComplex := ((-93086394626745465632490 : Int)/10^30,(80895409574746190332 : Int)/10^30)
theorem v2807_pg_checked : Scalar.distance (sourceCoefficient 35 43 1 2) v2807_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2807_mb : Scalar.QComplex := ((-747314657207587739685921 : Int)/10^30,(-431476872719503343883593353 : Int)/10^30)
theorem v2807_mb_checked : Scalar.distance (sourceCoefficient 35 43 3 1) v2807_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2807_mg : Scalar.QComplex := ((-93086290157331418688224 : Int)/10^30,(161224745560986717763 : Int)/10^30)
theorem v2807_mg_checked : Scalar.distance (sourceCoefficient 35 43 3 2) v2807_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2807_upper : Scalar.QComplex := ((999996633130243372599920627278 : Int)/10^30,(-2594942808125613019383629054 : Int)/10^30)
theorem v2807_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 43 5) 1) 14) v2807_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2807 : Material (35 : Basis) (43 : Basis) where
  plus := ![v2807_pa,v2807_pb,v2807_pg]
  minus := ![(Primitive.Addresses.material2807 1).one,v2807_mb,v2807_mg]
  upper := v2807_upper
  lower := (Primitive.Addresses.material2807 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2807_pa_checked.trans (by decide +kernel)
    · exact v2807_pb_checked.trans (by decide +kernel)
    · exact v2807_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 43 Primitive.Addresses.material2807
    · exact v2807_mb_checked.trans (by decide +kernel)
    · exact v2807_mg_checked.trans (by decide +kernel)
  upper_error := v2807_upper_checked
  lower_error := reuse_lower_error 35 43 Primitive.Addresses.material2807

def v2808_pa : Scalar.QComplex := ((999999617282576518126143468735 : Int)/10^30,(-874891250665544989743359698 : Int)/10^30)
theorem v2808_pa_checked : Scalar.distance (sourceCoefficient 35 44 1 0) v2808_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2808_pb : Scalar.QComplex := ((-377495906917509930376246 : Int)/10^30,(-431477354649599556949281636 : Int)/10^30)
theorem v2808_pb_checked : Scalar.distance (sourceCoefficient 35 44 1 1) v2808_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2808_pg : Scalar.QComplex := ((-93086394139890906950119 : Int)/10^30,(81440502957694472715 : Int)/10^30)
theorem v2808_pg_checked : Scalar.distance (sourceCoefficient 35 44 1 2) v2808_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2808_mb : Scalar.QComplex := ((-749841290402469931432352 : Int)/10^30,(-431476868228895046333932028 : Int)/10^30)
theorem v2808_mb_checked : Scalar.distance (sourceCoefficient 35 44 3 1) v2808_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2808_mg : Scalar.QComplex := ((-93086289200086001894313 : Int)/10^30,(161769838320838264649 : Int)/10^30)
theorem v2808_mg_checked : Scalar.distance (sourceCoefficient 35 44 3 2) v2808_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2808_upper : Scalar.QComplex := ((999996617917685647995000138840 : Int)/10^30,(-2600798567790906206594050131 : Int)/10^30)
theorem v2808_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 44 5) 1) 14) v2808_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2808 : Material (35 : Basis) (44 : Basis) where
  plus := ![v2808_pa,v2808_pb,v2808_pg]
  minus := ![(Primitive.Addresses.material2808 1).one,v2808_mb,v2808_mg]
  upper := v2808_upper
  lower := (Primitive.Addresses.material2808 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2808_pa_checked.trans (by decide +kernel)
    · exact v2808_pb_checked.trans (by decide +kernel)
    · exact v2808_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 44 Primitive.Addresses.material2808
    · exact v2808_mb_checked.trans (by decide +kernel)
    · exact v2808_mg_checked.trans (by decide +kernel)
  upper_error := v2808_upper_checked
  lower_error := reuse_lower_error 35 44 Primitive.Addresses.material2808

def v2809_pa : Scalar.QComplex := ((999999614729491603483446337252 : Int)/10^30,(-877804572988582958894561329 : Int)/10^30)
theorem v2809_pa_checked : Scalar.distance (sourceCoefficient 35 45 1 0) v2809_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2809_pb : Scalar.QComplex := ((-378752939959398765967374 : Int)/10^30,(-431477353492879588604508225 : Int)/10^30)
theorem v2809_pb_checked : Scalar.distance (sourceCoefficient 35 45 1 1) v2809_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2809_pg : Scalar.QComplex := ((-93086393896287455122326 : Int)/10^30,(81711693726283428509 : Int)/10^30)
theorem v2809_pg_checked : Scalar.distance (sourceCoefficient 35 45 1 2) v2809_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2809_mb : Scalar.QComplex := ((-751098321978110680332115 : Int)/10^30,(-431476865987412608205373893 : Int)/10^30)
theorem v2809_mb_checked : Scalar.distance (sourceCoefficient 35 45 3 1) v2809_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2809_mg : Scalar.QComplex := ((-93086288722457221457763 : Int)/10^30,(162041028778231695831 : Int)/10^30)
theorem v2809_mg_checked : Scalar.distance (sourceCoefficient 35 45 3 2) v2809_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2809_upper : Scalar.QComplex := ((999996610336474500845432575537 : Int)/10^30,(-2603711881368499849840998331 : Int)/10^30)
theorem v2809_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 45 5) 1) 14) v2809_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2809 : Material (35 : Basis) (45 : Basis) where
  plus := ![v2809_pa,v2809_pb,v2809_pg]
  minus := ![(Primitive.Addresses.material2809 1).one,v2809_mb,v2809_mg]
  upper := v2809_upper
  lower := (Primitive.Addresses.material2809 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2809_pa_checked.trans (by decide +kernel)
    · exact v2809_pb_checked.trans (by decide +kernel)
    · exact v2809_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 45 Primitive.Addresses.material2809
    · exact v2809_mb_checked.trans (by decide +kernel)
    · exact v2809_mg_checked.trans (by decide +kernel)
  upper_error := v2809_upper_checked
  lower_error := reuse_lower_error 35 45 Primitive.Addresses.material2809

def v2810_pa : Scalar.QComplex := ((999999600230989880655791664907 : Int)/10^30,(-894168809802392383173600660 : Int)/10^30)
theorem v2810_pa_checked : Scalar.distance (sourceCoefficient 35 46 1 0) v2810_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2810_pb : Scalar.QComplex := ((-385813739974934381487148 : Int)/10^30,(-431477346904798291389749069 : Int)/10^30)
theorem v2810_pb_checked : Scalar.distance (sourceCoefficient 35 46 1 1) v2810_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2810_pg : Scalar.QComplex := ((-93086392510828293671219 : Int)/10^30,(83234982074972058696 : Int)/10^30)
theorem v2810_pg_checked : Scalar.distance (sourceCoefficient 35 46 1 2) v2810_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2810_mb : Scalar.QComplex := ((-758159113679370312236505 : Int)/10^30,(-431476853306181357254874490 : Int)/10^30)
theorem v2810_mb_checked : Scalar.distance (sourceCoefficient 35 46 3 1) v2810_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2810_mg : Scalar.QComplex := ((-93086286022469337318569 : Int)/10^30,(163564315364141598517 : Int)/10^30)
theorem v2810_mg_checked : Scalar.distance (sourceCoefficient 35 46 3 2) v2810_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2810_upper : Scalar.QComplex := ((999996567594806183164979331385 : Int)/10^30,(-2620076068786602138440986791 : Int)/10^30)
theorem v2810_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 46 5) 1) 14) v2810_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2810 : Material (35 : Basis) (46 : Basis) where
  plus := ![v2810_pa,v2810_pb,v2810_pg]
  minus := ![(Primitive.Addresses.material2810 1).one,v2810_mb,v2810_mg]
  upper := v2810_upper
  lower := (Primitive.Addresses.material2810 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2810_pa_checked.trans (by decide +kernel)
    · exact v2810_pb_checked.trans (by decide +kernel)
    · exact v2810_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 46 Primitive.Addresses.material2810
    · exact v2810_mb_checked.trans (by decide +kernel)
    · exact v2810_mg_checked.trans (by decide +kernel)
  upper_error := v2810_upper_checked
  lower_error := reuse_lower_error 35 46 Primitive.Addresses.material2810

def v2811_pa : Scalar.QComplex := ((999999596701960836443248130360 : Int)/10^30,(-898106850924657578168194590 : Int)/10^30)
theorem v2811_pa_checked : Scalar.distance (sourceCoefficient 35 47 1 0) v2811_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2811_pb : Scalar.QComplex := ((-387512916112665250767332 : Int)/10^30,(-431477345296383425693037778 : Int)/10^30)
theorem v2811_pb_checked : Scalar.distance (sourceCoefficient 35 47 1 1) v2811_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2811_pg : Scalar.QComplex := ((-93086392173077213562946 : Int)/10^30,(83601560254845390820 : Int)/10^30)
theorem v2811_pg_checked : Scalar.distance (sourceCoefficient 35 47 1 2) v2811_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2811_mb : Scalar.QComplex := ((-759858287796430660473877 : Int)/10^30,(-431476850231454611635174258 : Int)/10^30)
theorem v2811_mb_checked : Scalar.distance (sourceCoefficient 35 47 3 1) v2811_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2811_mg : Scalar.QComplex := ((-93086285368377923808113 : Int)/10^30,(163930893116057150434 : Int)/10^30)
theorem v2811_mg_checked : Scalar.distance (sourceCoefficient 35 47 3 2) v2811_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2811_upper : Scalar.QComplex := ((999996557269080674296800553526 : Int)/10^30,(-2624014097952833697330465139 : Int)/10^30)
theorem v2811_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 47 5) 1) 14) v2811_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2811 : Material (35 : Basis) (47 : Basis) where
  plus := ![v2811_pa,v2811_pb,v2811_pg]
  minus := ![(Primitive.Addresses.material2811 1).one,v2811_mb,v2811_mg]
  upper := v2811_upper
  lower := (Primitive.Addresses.material2811 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2811_pa_checked.trans (by decide +kernel)
    · exact v2811_pb_checked.trans (by decide +kernel)
    · exact v2811_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 47 Primitive.Addresses.material2811
    · exact v2811_mb_checked.trans (by decide +kernel)
    · exact v2811_mg_checked.trans (by decide +kernel)
  upper_error := v2811_upper_checked
  lower_error := reuse_lower_error 35 47 Primitive.Addresses.material2811

def v2812_pa : Scalar.QComplex := ((999999571690162078982260793056 : Int)/10^30,(-925537407343818934034284643 : Int)/10^30)
theorem v2812_pa_checked : Scalar.distance (sourceCoefficient 35 48 1 0) v2812_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2812_pb : Scalar.QComplex := ((-399348583939825638978241 : Int)/10^30,(-431477333845403723094351430 : Int)/10^30)
theorem v2812_pb_checked : Scalar.distance (sourceCoefficient 35 48 1 1) v2812_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2812_pg : Scalar.QComplex := ((-93086389773737547074064 : Int)/10^30,(86154972751203644480 : Int)/10^30)
theorem v2812_pg_checked : Scalar.distance (sourceCoefficient 35 48 1 2) v2812_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2812_mb : Scalar.QComplex := ((-771693941334951249529674 : Int)/10^30,(-431476828566830896611018340 : Int)/10^30)
theorem v2812_mb_checked : Scalar.distance (sourceCoefficient 35 48 3 1) v2812_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2812_mg : Scalar.QComplex := ((-93086280765559167775653 : Int)/10^30,(166484302591141165051 : Int)/10^30)
theorem v2812_mg_checked : Scalar.distance (sourceCoefficient 35 48 3 2) v2812_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2812_upper : Scalar.QComplex := ((999996484914667270138872298880 : Int)/10^30,(-2651444570349307883642031263 : Int)/10^30)
theorem v2812_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 48 5) 1) 14) v2812_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2812 : Material (35 : Basis) (48 : Basis) where
  plus := ![v2812_pa,v2812_pb,v2812_pg]
  minus := ![(Primitive.Addresses.material2812 1).one,v2812_mb,v2812_mg]
  upper := v2812_upper
  lower := (Primitive.Addresses.material2812 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2812_pa_checked.trans (by decide +kernel)
    · exact v2812_pb_checked.trans (by decide +kernel)
    · exact v2812_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 48 Primitive.Addresses.material2812
    · exact v2812_mb_checked.trans (by decide +kernel)
    · exact v2812_mg_checked.trans (by decide +kernel)
  upper_error := v2812_upper_checked
  lower_error := reuse_lower_error 35 48 Primitive.Addresses.material2812

def v2813_pa : Scalar.QComplex := ((999999551049968148446774706615 : Int)/10^30,(-947575781743589809796535802 : Int)/10^30)
theorem v2813_pa_checked : Scalar.distance (sourceCoefficient 35 49 1 0) v2813_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2813_pb : Scalar.QComplex := ((-408857646464997318761559 : Int)/10^30,(-431477324331806422581540231 : Int)/10^30)
theorem v2813_pb_checked : Scalar.distance (sourceCoefficient 35 49 1 1) v2813_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2813_pg : Scalar.QComplex := ((-93086387786850672396569 : Int)/10^30,(88206446277098842431 : Int)/10^30)
theorem v2813_pg_checked : Scalar.distance (sourceCoefficient 35 49 1 2) v2813_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2813_mb : Scalar.QComplex := ((-781202992109658371739273 : Int)/10^30,(-431476810847344451500034819 : Int)/10^30)
theorem v2813_mb_checked : Scalar.distance (sourceCoefficient 35 49 3 1) v2813_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2813_mg : Scalar.QComplex := ((-93086277008343774997136 : Int)/10^30,(168535773638585125556 : Int)/10^30)
theorem v2813_mg_checked : Scalar.distance (sourceCoefficient 35 49 3 2) v2813_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2813_upper : Scalar.QComplex := ((999996426238269172450974783338 : Int)/10^30,(-2673482876302406639918740520 : Int)/10^30)
theorem v2813_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 49 5) 1) 14) v2813_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2813 : Material (35 : Basis) (49 : Basis) where
  plus := ![v2813_pa,v2813_pb,v2813_pg]
  minus := ![(Primitive.Addresses.material2813 1).one,v2813_mb,v2813_mg]
  upper := v2813_upper
  lower := (Primitive.Addresses.material2813 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2813_pa_checked.trans (by decide +kernel)
    · exact v2813_pb_checked.trans (by decide +kernel)
    · exact v2813_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 49 Primitive.Addresses.material2813
    · exact v2813_mb_checked.trans (by decide +kernel)
    · exact v2813_mg_checked.trans (by decide +kernel)
  upper_error := v2813_upper_checked
  lower_error := reuse_lower_error 35 49 Primitive.Addresses.material2813

def v2814_pa : Scalar.QComplex := ((999999548606378111805920157601 : Int)/10^30,(-950151061684501975667598333 : Int)/10^30)
theorem v2814_pa_checked : Scalar.distance (sourceCoefficient 35 50 1 0) v2814_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2814_pb : Scalar.QComplex := ((-409968821790352990218979 : Int)/10^30,(-431477323201867772106307081 : Int)/10^30)
theorem v2814_pb_checked : Scalar.distance (sourceCoefficient 35 50 1 1) v2814_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2814_pg : Scalar.QComplex := ((-93086387551232348519362 : Int)/10^30,(88446169884215390164 : Int)/10^30)
theorem v2814_pg_checked : Scalar.distance (sourceCoefficient 35 50 1 2) v2814_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2814_mb : Scalar.QComplex := ((-782314166046186521533210 : Int)/10^30,(-431476808758511961449536039 : Int)/10^30)
theorem v2814_mb_checked : Scalar.distance (sourceCoefficient 35 50 3 1) v2814_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2814_mg : Scalar.QComplex := ((-93086276565854862660289 : Int)/10^30,(168775496953113616799 : Int)/10^30)
theorem v2814_mg_checked : Scalar.distance (sourceCoefficient 35 50 3 2) v2814_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2814_upper : Scalar.QComplex := ((999996419349983224807278386090 : Int)/10^30,(-2676058148190327124947749237 : Int)/10^30)
theorem v2814_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 50 5) 1) 14) v2814_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2814 : Material (35 : Basis) (50 : Basis) where
  plus := ![v2814_pa,v2814_pb,v2814_pg]
  minus := ![(Primitive.Addresses.material2814 1).one,v2814_mb,v2814_mg]
  upper := v2814_upper
  lower := (Primitive.Addresses.material2814 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2814_pa_checked.trans (by decide +kernel)
    · exact v2814_pb_checked.trans (by decide +kernel)
    · exact v2814_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 50 Primitive.Addresses.material2814
    · exact v2814_mb_checked.trans (by decide +kernel)
    · exact v2814_mg_checked.trans (by decide +kernel)
  upper_error := v2814_upper_checked
  lower_error := reuse_lower_error 35 50 Primitive.Addresses.material2814

def v2815_pa : Scalar.QComplex := ((999999537806546740308868652647 : Int)/10^30,(-961450307034427040634992530 : Int)/10^30)
theorem v2815_pa_checked : Scalar.distance (sourceCoefficient 35 51 1 0) v2815_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2815_pb : Scalar.QComplex := ((-414844191799162834499062 : Int)/10^30,(-431477318199076486385306651 : Int)/10^30)
theorem v2815_pb_checked : Scalar.distance (sourceCoefficient 35 51 1 1) v2815_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2815_pg : Scalar.QComplex := ((-93086386508925455249140 : Int)/10^30,(89497976255110431104 : Int)/10^30)
theorem v2815_pg_checked : Scalar.distance (sourceCoefficient 35 51 1 2) v2815_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2815_mb : Scalar.QComplex := ((-787189529922489733894793 : Int)/10^30,(-431476799548497799407533731 : Int)/10^30)
theorem v2815_mb_checked : Scalar.distance (sourceCoefficient 35 51 3 1) v2815_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2815_mg : Scalar.QComplex := ((-93086274615886831006567 : Int)/10^30,(169827302032909170796 : Int)/10^30)
theorem v2815_mg_checked : Scalar.distance (sourceCoefficient 35 51 3 2) v2815_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2815_upper : Scalar.QComplex := ((999996389048695523950574858745 : Int)/10^30,(-2687357358071824349643183954 : Int)/10^30)
theorem v2815_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 51 5) 1) 14) v2815_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2815 : Material (35 : Basis) (51 : Basis) where
  plus := ![v2815_pa,v2815_pb,v2815_pg]
  minus := ![(Primitive.Addresses.material2815 1).one,v2815_mb,v2815_mg]
  upper := v2815_upper
  lower := (Primitive.Addresses.material2815 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2815_pa_checked.trans (by decide +kernel)
    · exact v2815_pb_checked.trans (by decide +kernel)
    · exact v2815_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 51 Primitive.Addresses.material2815
    · exact v2815_mb_checked.trans (by decide +kernel)
    · exact v2815_mg_checked.trans (by decide +kernel)
  upper_error := v2815_upper_checked
  lower_error := reuse_lower_error 35 51 Primitive.Addresses.material2815

def v2816_pa : Scalar.QComplex := ((999999514257538453387248767208 : Int)/10^30,(-985639227682972525218177255 : Int)/10^30)
theorem v2816_pa_checked : Scalar.distance (sourceCoefficient 35 52 1 0) v2816_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2816_pb : Scalar.QComplex := ((-425281166450246066289002 : Int)/10^30,(-431477307242397607243421517 : Int)/10^30)
theorem v2816_pb_checked : Scalar.distance (sourceCoefficient 35 52 1 1) v2816_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2816_pg : Scalar.QComplex := ((-93086384230988686074106 : Int)/10^30,(91749636427926365397 : Int)/10^30)
theorem v2816_pg_checked : Scalar.distance (sourceCoefficient 35 52 1 2) v2816_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2816_mb : Scalar.QComplex := ((-797626491232289907579728 : Int)/10^30,(-431476779585183939941804245 : Int)/10^30)
theorem v2816_mb_checked : Scalar.distance (sourceCoefficient 35 52 3 1) v2816_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2816_mg : Scalar.QComplex := ((-93086270394869591880978 : Int)/10^30,(172078959401572279462 : Int)/10^30)
theorem v2816_mg_checked : Scalar.distance (sourceCoefficient 35 52 3 2) v2816_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2816_upper : Scalar.QComplex := ((999996323751839672860541487510 : Int)/10^30,(-2711546202050362004553662328 : Int)/10^30)
theorem v2816_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 52 5) 1) 14) v2816_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2816 : Material (35 : Basis) (52 : Basis) where
  plus := ![v2816_pa,v2816_pb,v2816_pg]
  minus := ![(Primitive.Addresses.material2816 1).one,v2816_mb,v2816_mg]
  upper := v2816_upper
  lower := (Primitive.Addresses.material2816 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2816_pa_checked.trans (by decide +kernel)
    · exact v2816_pb_checked.trans (by decide +kernel)
    · exact v2816_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 52 Primitive.Addresses.material2816
    · exact v2816_mb_checked.trans (by decide +kernel)
    · exact v2816_mg_checked.trans (by decide +kernel)
  upper_error := v2816_upper_checked
  lower_error := reuse_lower_error 35 52 Primitive.Addresses.material2816

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
