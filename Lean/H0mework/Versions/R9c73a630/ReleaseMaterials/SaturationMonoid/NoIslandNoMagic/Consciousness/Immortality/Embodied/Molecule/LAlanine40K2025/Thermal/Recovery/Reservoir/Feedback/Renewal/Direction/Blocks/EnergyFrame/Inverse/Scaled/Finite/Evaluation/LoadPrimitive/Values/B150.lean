import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B100

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2401_pa : Scalar.QComplex := ((999998699796271384550238927017 : Int)/10^30,(-1612577367663692474851455064 : Int)/10^30)
theorem v2401_pa_checked : Scalar.distance (sourceCoefficient 28 92 1 0) v2401_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2401_pb : Scalar.QComplex := ((-695790748288527509979302 : Int)/10^30,(-431476875200639160377648901 : Int)/10^30)
theorem v2401_pb_checked : Scalar.distance (sourceCoefficient 28 92 1 1) v2401_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2401_pg : Scalar.QComplex := ((-93086299719263872361027 : Int)/10^30,(150109055339197502073 : Int)/10^30)
theorem v2401_pg_checked : Scalar.distance (sourceCoefficient 28 92 1 2) v2401_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2401_mb : Scalar.QComplex := ((-1068135599514912033072349 : Int)/10^30,(-431476114106000534831766528 : Int)/10^30)
theorem v2401_mb_checked : Scalar.distance (sourceCoefficient 28 92 3 1) v2401_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2401_mg : Scalar.QComplex := ((-93086135521626135975006 : Int)/10^30,(230438283653152350823 : Int)/10^30)
theorem v2401_mg_checked : Scalar.distance (sourceCoefficient 28 92 3 2) v2401_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2401_upper : Scalar.QComplex := ((999994427253431425457791084410 : Int)/10^30,(-3338482002594108168288298690 : Int)/10^30)
theorem v2401_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 92 5) 1) 14) v2401_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2401 : Material (28 : Basis) (92 : Basis) where
  plus := ![v2401_pa,v2401_pb,v2401_pg]
  minus := ![(Primitive.Addresses.material2401 1).one,v2401_mb,v2401_mg]
  upper := v2401_upper
  lower := (Primitive.Addresses.material2401 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2401_pa_checked.trans (by decide +kernel)
    · exact v2401_pb_checked.trans (by decide +kernel)
    · exact v2401_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 92 Primitive.Addresses.material2401
    · exact v2401_mb_checked.trans (by decide +kernel)
    · exact v2401_mg_checked.trans (by decide +kernel)
  upper_error := v2401_upper_checked
  lower_error := reuse_lower_error 28 92 Primitive.Addresses.material2401

def v2402_pa : Scalar.QComplex := ((999998637919113240751293266397 : Int)/10^30,(-1650502928883846403520201300 : Int)/10^30)
theorem v2402_pa_checked : Scalar.distance (sourceCoefficient 28 93 1 0) v2402_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2402_pb : Scalar.QComplex := ((-712154762263937987013968 : Int)/10^30,(-431476842475609735666610523 : Int)/10^30)
theorem v2402_pb_checked : Scalar.distance (sourceCoefficient 28 93 1 1) v2402_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2402_pg : Scalar.QComplex := ((-93086293309273173055591 : Int)/10^30,(153639409015198639827 : Int)/10^30)
theorem v2402_pg_checked : Scalar.distance (sourceCoefficient 28 93 1 2) v2402_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2402_mb : Scalar.QComplex := ((-1084499579157025721764016 : Int)/10^30,(-431476067259576242195984819 : Int)/10^30)
theorem v2402_mb_checked : Scalar.distance (sourceCoefficient 28 93 3 1) v2402_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2402_mg : Scalar.QComplex := ((-93086126065101602240241 : Int)/10^30,(233968630483108191632 : Int)/10^30)
theorem v2402_mg_checked : Scalar.distance (sourceCoefficient 28 93 3 2) v2402_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2402_upper : Scalar.QComplex := ((999994299920287354469174184200 : Int)/10^30,(-3376407400534232204648782116 : Int)/10^30)
theorem v2402_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 93 5) 1) 14) v2402_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2402 : Material (28 : Basis) (93 : Basis) where
  plus := ![v2402_pa,v2402_pb,v2402_pg]
  minus := ![(Primitive.Addresses.material2402 1).one,v2402_mb,v2402_mg]
  upper := v2402_upper
  lower := (Primitive.Addresses.material2402 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2402_pa_checked.trans (by decide +kernel)
    · exact v2402_pb_checked.trans (by decide +kernel)
    · exact v2402_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 93 Primitive.Addresses.material2402
    · exact v2402_mb_checked.trans (by decide +kernel)
    · exact v2402_mg_checked.trans (by decide +kernel)
  upper_error := v2402_upper_checked
  lower_error := reuse_lower_error 28 93 Primitive.Addresses.material2402

def v2403_pa : Scalar.QComplex := ((999998562975508897254094150997 : Int)/10^30,(-1695301423690225001101691431 : Int)/10^30)
theorem v2403_pa_checked : Scalar.distance (sourceCoefficient 28 94 1 0) v2403_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2403_pb : Scalar.QComplex := ((-731484289159137873000601 : Int)/10^30,(-431476802754080751916159622 : Int)/10^30)
theorem v2403_pb_checked : Scalar.distance (sourceCoefficient 28 94 1 1) v2403_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2403_pg : Scalar.QComplex := ((-93086285536419946107509 : Int)/10^30,(157809539172100254445 : Int)/10^30)
theorem v2403_pg_checked : Scalar.distance (sourceCoefficient 28 94 1 2) v2403_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2403_mb : Scalar.QComplex := ((-1103829064577068819925937 : Int)/10^30,(-431476010857550907602934645 : Int)/10^30)
theorem v2403_mb_checked : Scalar.distance (sourceCoefficient 28 94 3 1) v2403_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2403_mg : Scalar.QComplex := ((-93086114693616759764780 : Int)/10^30,(238138752379657505929 : Int)/10^30)
theorem v2403_mg_checked : Scalar.distance (sourceCoefficient 28 94 3 2) v2403_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2403_upper : Scalar.QComplex := ((999994147658656682559614862643 : Int)/10^30,(-3421205699272652922793132755 : Int)/10^30)
theorem v2403_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 94 5) 1) 14) v2403_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2403 : Material (28 : Basis) (94 : Basis) where
  plus := ![v2403_pa,v2403_pb,v2403_pg]
  minus := ![(Primitive.Addresses.material2403 1).one,v2403_mb,v2403_mg]
  upper := v2403_upper
  lower := (Primitive.Addresses.material2403 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2403_pa_checked.trans (by decide +kernel)
    · exact v2403_pb_checked.trans (by decide +kernel)
    · exact v2403_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 94 Primitive.Addresses.material2403
    · exact v2403_mb_checked.trans (by decide +kernel)
    · exact v2403_mg_checked.trans (by decide +kernel)
  upper_error := v2403_upper_checked
  lower_error := reuse_lower_error 28 94 Primitive.Addresses.material2403

def v2404_pa : Scalar.QComplex := ((999998486937252462111169169433 : Int)/10^30,(-1739575582065033377420616967 : Int)/10^30)
theorem v2404_pa_checked : Scalar.distance (sourceCoefficient 28 95 1 0) v2404_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2404_pb : Scalar.QComplex := ((-750587575721381024552138 : Int)/10^30,(-431476762363074514931425039 : Int)/10^30)
theorem v2404_pb_checked : Scalar.distance (sourceCoefficient 28 95 1 1) v2404_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2404_pg : Scalar.QComplex := ((-93086277640401988234174 : Int)/10^30,(161930860620122471480 : Int)/10^30)
theorem v2404_pg_checked : Scalar.distance (sourceCoefficient 28 95 1 2) v2404_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2404_mb : Scalar.QComplex := ((-1122932309170666081901562 : Int)/10^30,(-431475953981283786907895749 : Int)/10^30)
theorem v2404_mb_checked : Scalar.distance (sourceCoefficient 28 95 3 1) v2404_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2404_mg : Scalar.QComplex := ((-93086103241086949724199 : Int)/10^30,(242260065479215519974 : Int)/10^30)
theorem v2404_mg_checked : Scalar.distance (sourceCoefficient 28 95 3 2) v2404_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2404_upper : Scalar.QComplex := ((999993995207332662820739530232 : Int)/10^30,(-3465479660471170737496341890 : Int)/10^30)
theorem v2404_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 95 5) 1) 14) v2404_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2404 : Material (28 : Basis) (95 : Basis) where
  plus := ![v2404_pa,v2404_pb,v2404_pg]
  minus := ![(Primitive.Addresses.material2404 1).one,v2404_mb,v2404_mg]
  upper := v2404_upper
  lower := (Primitive.Addresses.material2404 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2404_pa_checked.trans (by decide +kernel)
    · exact v2404_pb_checked.trans (by decide +kernel)
    · exact v2404_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 95 Primitive.Addresses.material2404
    · exact v2404_mb_checked.trans (by decide +kernel)
    · exact v2404_mg_checked.trans (by decide +kernel)
  upper_error := v2404_upper_checked
  lower_error := reuse_lower_error 28 95 Primitive.Addresses.material2404

def v2405_pa : Scalar.QComplex := ((999998449720668598702205116744 : Int)/10^30,(-1760839646145153735279574436 : Int)/10^30)
theorem v2405_pa_checked : Scalar.distance (sourceCoefficient 28 96 1 0) v2405_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2405_pb : Scalar.QComplex := ((-759762532538897270747883 : Int)/10^30,(-431476742563141857904395776 : Int)/10^30)
theorem v2405_pb_checked : Scalar.distance (sourceCoefficient 28 96 1 1) v2405_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2405_pg : Scalar.QComplex := ((-93086273772415945331081 : Int)/10^30,(163910255477073068896 : Int)/10^30)
theorem v2405_pg_checked : Scalar.distance (sourceCoefficient 28 96 1 2) v2405_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2405_mb : Scalar.QComplex := ((-1132107245485476461543818 : Int)/10^30,(-431475926263783993499614306 : Int)/10^30)
theorem v2405_mb_checked : Scalar.distance (sourceCoefficient 28 96 3 1) v2405_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2405_mg : Scalar.QComplex := ((-93086097664973734135724 : Int)/10^30,(244239456261249201932 : Int)/10^30)
theorem v2405_mg_checked : Scalar.distance (sourceCoefficient 28 96 3 2) v2405_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2405_upper : Scalar.QComplex := ((999993921290958687678287641446 : Int)/10^30,(-3486743628648518014317744702 : Int)/10^30)
theorem v2405_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 96 5) 1) 14) v2405_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2405 : Material (28 : Basis) (96 : Basis) where
  plus := ![v2405_pa,v2405_pb,v2405_pg]
  minus := ![(Primitive.Addresses.material2405 1).one,v2405_mb,v2405_mg]
  upper := v2405_upper
  lower := (Primitive.Addresses.material2405 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2405_pa_checked.trans (by decide +kernel)
    · exact v2405_pb_checked.trans (by decide +kernel)
    · exact v2405_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 96 Primitive.Addresses.material2405
    · exact v2405_mb_checked.trans (by decide +kernel)
    · exact v2405_mg_checked.trans (by decide +kernel)
  upper_error := v2405_upper_checked
  lower_error := reuse_lower_error 28 96 Primitive.Addresses.material2405

def v2406_pa : Scalar.QComplex := ((999998318217374013276563416915 : Int)/10^30,(-1834001751247976808312597061 : Int)/10^30)
theorem v2406_pa_checked : Scalar.distance (sourceCoefficient 28 97 1 0) v2406_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2406_pb : Scalar.QComplex := ((-791330303744018274219509 : Int)/10^30,(-431476672451369874748358679 : Int)/10^30)
theorem v2406_pb_checked : Scalar.distance (sourceCoefficient 28 97 1 1) v2406_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2406_pg : Scalar.QComplex := ((-93086260088916030672988 : Int)/10^30,(170720651135221625977 : Int)/10^30)
theorem v2406_pg_checked : Scalar.distance (sourceCoefficient 28 97 1 2) v2406_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2406_mb : Scalar.QComplex := ((-1163674944433172022459582 : Int)/10^30,(-431475828910473325778006884 : Int)/10^30)
theorem v2406_mb_checked : Scalar.distance (sourceCoefficient 28 97 3 1) v2406_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2406_mg : Scalar.QComplex := ((-93086078104414190321945 : Int)/10^30,(251049837575332060636 : Int)/10^30)
theorem v2406_mg_checked : Scalar.distance (sourceCoefficient 28 97 3 2) v2406_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2406_upper : Scalar.QComplex := ((999993663516703767817699835020 : Int)/10^30,(-3559905397822223192521506226 : Int)/10^30)
theorem v2406_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 28 97 5) 1) 14) v2406_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2406 : Material (28 : Basis) (97 : Basis) where
  plus := ![v2406_pa,v2406_pb,v2406_pg]
  minus := ![(Primitive.Addresses.material2406 1).one,v2406_mb,v2406_mg]
  upper := v2406_upper
  lower := (Primitive.Addresses.material2406 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2406_pa_checked.trans (by decide +kernel)
    · exact v2406_pb_checked.trans (by decide +kernel)
    · exact v2406_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 28 97 Primitive.Addresses.material2406
    · exact v2406_mb_checked.trans (by decide +kernel)
    · exact v2406_mg_checked.trans (by decide +kernel)
  upper_error := v2406_upper_checked
  lower_error := reuse_lower_error 28 97 Primitive.Addresses.material2406

def v2407_pa : Scalar.QComplex := ((999999843497631511020801918312 : Int)/10^30,(-559468240818875306337844702 : Int)/10^30)
theorem v2407_pa_checked : Scalar.distance (sourceCoefficient 29 30 1 0) v2407_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2407_pb : Scalar.QComplex := ((-241397969626029747639076 : Int)/10^30,(-431477453471441955034767366 : Int)/10^30)
theorem v2407_pb_checked : Scalar.distance (sourceCoefficient 29 30 1 1) v2407_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2407_pg : Scalar.QComplex := ((-93086415328518225689886 : Int)/10^30,(52078901178452663134 : Int)/10^30)
theorem v2407_pg_checked : Scalar.distance (sourceCoefficient 29 30 1 2) v2407_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2407_mb : Scalar.QComplex := ((-613743489065271004307404 : Int)/10^30,(-431477084497090907525223092 : Int)/10^30)
theorem v2407_mb_checked : Scalar.distance (sourceCoefficient 29 30 3 1) v2407_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2407_mg : Scalar.QComplex := ((-93086335726445369171007 : Int)/10^30,(132408265759093764695 : Int)/10^30)
theorem v2407_mg_checked : Scalar.distance (sourceCoefficient 29 30 3 2) v2407_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2407_upper : Scalar.QComplex := ((999997388523903763564654972866 : Int)/10^30,(-2285376418156420348548919103 : Int)/10^30)
theorem v2407_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 30 5) 1) 14) v2407_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2407 : Material (29 : Basis) (30 : Basis) where
  plus := ![v2407_pa,v2407_pb,v2407_pg]
  minus := ![(Primitive.Addresses.material2407 1).one,v2407_mb,v2407_mg]
  upper := v2407_upper
  lower := (Primitive.Addresses.material2407 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2407_pa_checked.trans (by decide +kernel)
    · exact v2407_pb_checked.trans (by decide +kernel)
    · exact v2407_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 30 Primitive.Addresses.material2407
    · exact v2407_mb_checked.trans (by decide +kernel)
    · exact v2407_mg_checked.trans (by decide +kernel)
  upper_error := v2407_upper_checked
  lower_error := reuse_lower_error 29 30 Primitive.Addresses.material2407

def v2408_pa : Scalar.QComplex := ((999999837228742228823717174553 : Int)/10^30,(-570563308536283473167694969 : Int)/10^30)
theorem v2408_pa_checked : Scalar.distance (sourceCoefficient 29 31 1 0) v2408_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2408_pb : Scalar.QComplex := ((-246185241930249420689793 : Int)/10^30,(-431477450749380682433135763 : Int)/10^30)
theorem v2408_pb_checked : Scalar.distance (sourceCoefficient 29 31 1 1) v2408_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2408_pg : Scalar.QComplex := ((-93086414743116888212696 : Int)/10^30,(53111701420671890382 : Int)/10^30)
theorem v2408_pg_checked : Scalar.distance (sourceCoefficient 29 31 1 2) v2408_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2408_mb : Scalar.QComplex := ((-618530757237954128177922 : Int)/10^30,(-431477077643830260670564916 : Int)/10^30)
theorem v2408_mb_checked : Scalar.distance (sourceCoefficient 29 31 3 1) v2408_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2408_mg : Scalar.QComplex := ((-93086334249784156226466 : Int)/10^30,(133441065111579271717 : Int)/10^30)
theorem v2408_mg_checked : Scalar.distance (sourceCoefficient 29 31 3 2) v2408_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2408_upper : Scalar.QComplex := ((999997363105943474575954857292 : Int)/10^30,(-2296471458529494276627502486 : Int)/10^30)
theorem v2408_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 31 5) 1) 14) v2408_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2408 : Material (29 : Basis) (31 : Basis) where
  plus := ![v2408_pa,v2408_pb,v2408_pg]
  minus := ![(Primitive.Addresses.material2408 1).one,v2408_mb,v2408_mg]
  upper := v2408_upper
  lower := (Primitive.Addresses.material2408 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2408_pa_checked.trans (by decide +kernel)
    · exact v2408_pb_checked.trans (by decide +kernel)
    · exact v2408_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 31 Primitive.Addresses.material2408
    · exact v2408_mb_checked.trans (by decide +kernel)
    · exact v2408_mg_checked.trans (by decide +kernel)
  upper_error := v2408_upper_checked
  lower_error := reuse_lower_error 29 31 Primitive.Addresses.material2408

def v2409_pa : Scalar.QComplex := ((999999834492274962083506655210 : Int)/10^30,(-575339397819257584920632722 : Int)/10^30)
theorem v2409_pa_checked : Scalar.distance (sourceCoefficient 29 32 1 0) v2409_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2409_pb : Scalar.QComplex := ((-248246017086663202931856 : Int)/10^30,(-431477449555811475089502320 : Int)/10^30)
theorem v2409_pb_checked : Scalar.distance (sourceCoefficient 29 32 1 1) v2409_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2409_pg : Scalar.QComplex := ((-93086414487003327355931 : Int)/10^30,(53556290520086115269 : Int)/10^30)
theorem v2409_pg_checked : Scalar.distance (sourceCoefficient 29 32 1 2) v2409_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2409_mb : Scalar.QComplex := ((-620591530597050668033810 : Int)/10^30,(-431477074671905351629834256 : Int)/10^30)
theorem v2409_mb_checked : Scalar.distance (sourceCoefficient 29 32 3 1) v2409_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2409_mg : Scalar.QComplex := ((-93086333610010321487737 : Int)/10^30,(133885653824438188073 : Int)/10^30)
theorem v2409_mg_checked : Scalar.distance (sourceCoefficient 29 32 3 2) v2409_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2409_upper : Scalar.QComplex := ((999997352126383464504100195230 : Int)/10^30,(-2301247535976150188226119009 : Int)/10^30)
theorem v2409_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 32 5) 1) 14) v2409_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2409 : Material (29 : Basis) (32 : Basis) where
  plus := ![v2409_pa,v2409_pb,v2409_pg]
  minus := ![(Primitive.Addresses.material2409 1).one,v2409_mb,v2409_mg]
  upper := v2409_upper
  lower := (Primitive.Addresses.material2409 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2409_pa_checked.trans (by decide +kernel)
    · exact v2409_pb_checked.trans (by decide +kernel)
    · exact v2409_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 32 Primitive.Addresses.material2409
    · exact v2409_mb_checked.trans (by decide +kernel)
    · exact v2409_mg_checked.trans (by decide +kernel)
  upper_error := v2409_upper_checked
  lower_error := reuse_lower_error 29 32 Primitive.Addresses.material2409

def v2410_pa : Scalar.QComplex := ((999999830640596329380827825946 : Int)/10^30,(-581995514294251869949798906 : Int)/10^30)
theorem v2410_pa_checked : Scalar.distance (sourceCoefficient 29 33 1 0) v2410_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2410_pb : Scalar.QComplex := ((-251117981708969214228857 : Int)/10^30,(-431477447870525227366802740 : Int)/10^30)
theorem v2410_pb_checked : Scalar.distance (sourceCoefficient 29 33 1 1) v2410_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2410_pg : Scalar.QComplex := ((-93086414125943029317872 : Int)/10^30,(54175884638231441165 : Int)/10^30)
theorem v2410_pg_checked : Scalar.distance (sourceCoefficient 29 33 1 2) v2410_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2410_mb : Scalar.QComplex := ((-623463492695666865869177 : Int)/10^30,(-431477070508243610851085539 : Int)/10^30)
theorem v2410_mb_checked : Scalar.distance (sourceCoefficient 29 33 3 1) v2410_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2410_mg : Scalar.QComplex := ((-93086332714268339412693 : Int)/10^30,(134505247400301531279 : Int)/10^30)
theorem v2410_mg_checked : Scalar.distance (sourceCoefficient 29 33 3 2) v2410_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2410_upper : Scalar.QComplex := ((999997336786857370753845418390 : Int)/10^30,(-2307903635889992967627894714 : Int)/10^30)
theorem v2410_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 33 5) 1) 14) v2410_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2410 : Material (29 : Basis) (33 : Basis) where
  plus := ![v2410_pa,v2410_pb,v2410_pg]
  minus := ![(Primitive.Addresses.material2410 1).one,v2410_mb,v2410_mg]
  upper := v2410_upper
  lower := (Primitive.Addresses.material2410 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2410_pa_checked.trans (by decide +kernel)
    · exact v2410_pb_checked.trans (by decide +kernel)
    · exact v2410_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 33 Primitive.Addresses.material2410
    · exact v2410_mb_checked.trans (by decide +kernel)
    · exact v2410_mg_checked.trans (by decide +kernel)
  upper_error := v2410_upper_checked
  lower_error := reuse_lower_error 29 33 Primitive.Addresses.material2410

def v2411_pa : Scalar.QComplex := ((999999821100809730216482193759 : Int)/10^30,(-598162476702314349065780839 : Int)/10^30)
theorem v2411_pa_checked : Scalar.distance (sourceCoefficient 29 34 1 0) v2411_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2411_pb : Scalar.QComplex := ((-258093662520185328199033 : Int)/10^30,(-431477443671015715112705504 : Int)/10^30)
theorem v2411_pb_checked : Scalar.distance (sourceCoefficient 29 34 1 1) v2411_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2411_pg : Scalar.QComplex := ((-93086413228932181627984 : Int)/10^30,(55680809445604875697 : Int)/10^30)
theorem v2411_pg_checked : Scalar.distance (sourceCoefficient 29 34 1 2) v2411_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2411_mb : Scalar.QComplex := ((-630439167285530639273247 : Int)/10^30,(-431477060289037295187887590 : Int)/10^30)
theorem v2411_mb_checked : Scalar.distance (sourceCoefficient 29 34 3 1) v2411_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2411_mg : Scalar.QComplex := ((-93086330518575496254903 : Int)/10^30,(136010170873242719877 : Int)/10^30)
theorem v2411_mg_checked : Scalar.distance (sourceCoefficient 29 34 3 2) v2411_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2411_upper : Scalar.QComplex := ((999997299344374519037954625253 : Int)/10^30,(-2324070557754457817266250195 : Int)/10^30)
theorem v2411_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 34 5) 1) 14) v2411_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2411 : Material (29 : Basis) (34 : Basis) where
  plus := ![v2411_pa,v2411_pb,v2411_pg]
  minus := ![(Primitive.Addresses.material2411 1).one,v2411_mb,v2411_mg]
  upper := v2411_upper
  lower := (Primitive.Addresses.material2411 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2411_pa_checked.trans (by decide +kernel)
    · exact v2411_pb_checked.trans (by decide +kernel)
    · exact v2411_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 34 Primitive.Addresses.material2411
    · exact v2411_mb_checked.trans (by decide +kernel)
    · exact v2411_mg_checked.trans (by decide +kernel)
  upper_error := v2411_upper_checked
  lower_error := reuse_lower_error 29 34 Primitive.Addresses.material2411

def v2412_pa : Scalar.QComplex := ((999999789058893716762401681832 : Int)/10^30,(-649524570797999047213405590 : Int)/10^30)
theorem v2412_pa_checked : Scalar.distance (sourceCoefficient 29 35 1 0) v2412_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2412_pb : Scalar.QComplex := ((-280255251212959815977132 : Int)/10^30,(-431477429331562477964529947 : Int)/10^30)
theorem v2412_pb_checked : Scalar.distance (sourceCoefficient 29 35 1 1) v2412_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2412_pg : Scalar.QComplex := ((-93086410190810391948566 : Int)/10^30,(60461923380217610258 : Int)/10^30)
theorem v2412_pg_checked : Scalar.distance (sourceCoefficient 29 35 1 2) v2412_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2412_mb : Scalar.QComplex := ((-652600735352230503433872 : Int)/10^30,(-431477026825136476311847669 : Int)/10^30)
theorem v2412_mb_checked : Scalar.distance (sourceCoefficient 29 35 3 1) v2412_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2412_mg : Scalar.QComplex := ((-93086323354568845614351 : Int)/10^30,(140791280405865956313 : Int)/10^30)
theorem v2412_mg_checked : Scalar.distance (sourceCoefficient 29 35 3 2) v2412_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2412_upper : Scalar.QComplex := ((999997178656191351880167227367 : Int)/10^30,(-2375432520050896555980478333 : Int)/10^30)
theorem v2412_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 35 5) 1) 14) v2412_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2412 : Material (29 : Basis) (35 : Basis) where
  plus := ![v2412_pa,v2412_pb,v2412_pg]
  minus := ![(Primitive.Addresses.material2412 1).one,v2412_mb,v2412_mg]
  upper := v2412_upper
  lower := (Primitive.Addresses.material2412 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2412_pa_checked.trans (by decide +kernel)
    · exact v2412_pb_checked.trans (by decide +kernel)
    · exact v2412_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 35 Primitive.Addresses.material2412
    · exact v2412_mb_checked.trans (by decide +kernel)
    · exact v2412_mg_checked.trans (by decide +kernel)
  upper_error := v2412_upper_checked
  lower_error := reuse_lower_error 29 35 Primitive.Addresses.material2412

def v2413_pa : Scalar.QComplex := ((999999778442039408804965821003 : Int)/10^30,(-665669491635646591188310317 : Int)/10^30)
theorem v2413_pa_checked : Scalar.distance (sourceCoefficient 29 36 1 0) v2413_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2413_pb : Scalar.QComplex := ((-287221421462458367991379 : Int)/10^30,(-431477424510655298456660554 : Int)/10^30)
theorem v2413_pb_checked : Scalar.distance (sourceCoefficient 29 36 1 1) v2413_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2413_pg : Scalar.QComplex := ((-93086409176639566147347 : Int)/10^30,(61964796403595367396 : Int)/10^30)
theorem v2413_pg_checked : Scalar.distance (sourceCoefficient 29 36 1 2) v2413_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2413_mb : Scalar.QComplex := ((-659566898847679731535616 : Int)/10^30,(-431477015992739911192085288 : Int)/10^30)
theorem v2413_mb_checked : Scalar.distance (sourceCoefficient 29 36 3 1) v2413_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2413_mg : Scalar.QComplex := ((-93086321043486665148593 : Int)/10^30,(142294151994471656049 : Int)/10^30)
theorem v2413_mg_checked : Scalar.distance (sourceCoefficient 29 36 3 2) v2413_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2413_upper : Scalar.QComplex := ((999997140174684146477547186774 : Int)/10^30,(-2391577398518853645868454196 : Int)/10^30)
theorem v2413_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 36 5) 1) 14) v2413_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2413 : Material (29 : Basis) (36 : Basis) where
  plus := ![v2413_pa,v2413_pb,v2413_pg]
  minus := ![(Primitive.Addresses.material2413 1).one,v2413_mb,v2413_mg]
  upper := v2413_upper
  lower := (Primitive.Addresses.material2413 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2413_pa_checked.trans (by decide +kernel)
    · exact v2413_pb_checked.trans (by decide +kernel)
    · exact v2413_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 36 Primitive.Addresses.material2413
    · exact v2413_mb_checked.trans (by decide +kernel)
    · exact v2413_mg_checked.trans (by decide +kernel)
  upper_error := v2413_upper_checked
  lower_error := reuse_lower_error 29 36 Primitive.Addresses.material2413

def v2414_pa : Scalar.QComplex := ((999999773829112099761154903029 : Int)/10^30,(-672563546921186590570098699 : Int)/10^30)
theorem v2414_pa_checked : Scalar.distance (sourceCoefficient 29 37 1 0) v2414_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2414_pb : Scalar.QComplex := ((-290196051263949720001101 : Int)/10^30,(-431477422406387640932071873 : Int)/10^30)
theorem v2414_pb_checked : Scalar.distance (sourceCoefficient 29 37 1 1) v2414_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2414_pg : Scalar.QComplex := ((-93086408734953040307424 : Int)/10^30,(62606539388711944330 : Int)/10^30)
theorem v2414_pg_checked : Scalar.distance (sourceCoefficient 29 37 1 2) v2414_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2414_mb : Scalar.QComplex := ((-662541525725692245405694 : Int)/10^30,(-431477011321501490848450159 : Int)/10^30)
theorem v2414_mb_checked : Scalar.distance (sourceCoefficient 29 37 3 1) v2414_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2414_mg : Scalar.QComplex := ((-93086320048005010644262 : Int)/10^30,(142935894359482411543 : Int)/10^30)
theorem v2414_mg_checked : Scalar.distance (sourceCoefficient 29 37 3 2) v2414_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2414_upper : Scalar.QComplex := ((999997123663249708815013146449 : Int)/10^30,(-2398471435575014076146752706 : Int)/10^30)
theorem v2414_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 37 5) 1) 14) v2414_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2414 : Material (29 : Basis) (37 : Basis) where
  plus := ![v2414_pa,v2414_pb,v2414_pg]
  minus := ![(Primitive.Addresses.material2414 1).one,v2414_mb,v2414_mg]
  upper := v2414_upper
  lower := (Primitive.Addresses.material2414 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2414_pa_checked.trans (by decide +kernel)
    · exact v2414_pb_checked.trans (by decide +kernel)
    · exact v2414_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 37 Primitive.Addresses.material2414
    · exact v2414_mb_checked.trans (by decide +kernel)
    · exact v2414_mg_checked.trans (by decide +kernel)
  upper_error := v2414_upper_checked
  lower_error := reuse_lower_error 29 37 Primitive.Addresses.material2414

def v2415_pa : Scalar.QComplex := ((999999757886229514395294533176 : Int)/10^30,(-695864557476619549219553819 : Int)/10^30)
theorem v2415_pa_checked : Scalar.distance (sourceCoefficient 29 38 1 0) v2415_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2415_pb : Scalar.QComplex := ((-300249913208685669692203 : Int)/10^30,(-431477415091851737582104986 : Int)/10^30)
theorem v2415_pb_checked : Scalar.distance (sourceCoefficient 29 38 1 1) v2415_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2415_pg : Scalar.QComplex := ((-93086407203905538213705 : Int)/10^30,(64775547239086114782 : Int)/10^30)
theorem v2415_pg_checked : Scalar.distance (sourceCoefficient 29 38 1 2) v2415_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2415_mb : Scalar.QComplex := ((-672595377614800858758632 : Int)/10^30,(-431476995330938261860292087 : Int)/10^30)
theorem v2415_mb_checked : Scalar.distance (sourceCoefficient 29 38 3 1) v2415_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2415_mg : Scalar.QComplex := ((-93086316645201992243806 : Int)/10^30,(145104900081010792259 : Int)/10^30)
theorem v2415_mg_checked : Scalar.distance (sourceCoefficient 29 38 3 2) v2415_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2415_upper : Scalar.QComplex := ((999997067504960500987784261525 : Int)/10^30,(-2421772383910359926120063369 : Int)/10^30)
theorem v2415_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 38 5) 1) 14) v2415_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2415 : Material (29 : Basis) (38 : Basis) where
  plus := ![v2415_pa,v2415_pb,v2415_pg]
  minus := ![(Primitive.Addresses.material2415 1).one,v2415_mb,v2415_mg]
  upper := v2415_upper
  lower := (Primitive.Addresses.material2415 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2415_pa_checked.trans (by decide +kernel)
    · exact v2415_pb_checked.trans (by decide +kernel)
    · exact v2415_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 38 Primitive.Addresses.material2415
    · exact v2415_mb_checked.trans (by decide +kernel)
    · exact v2415_mg_checked.trans (by decide +kernel)
  upper_error := v2415_upper_checked
  lower_error := reuse_lower_error 29 38 Primitive.Addresses.material2415

def v2416_pa : Scalar.QComplex := ((999999748388594390711879404783 : Int)/10^30,(-709381947832249822404973628 : Int)/10^30)
theorem v2416_pa_checked : Scalar.distance (sourceCoefficient 29 39 1 0) v2416_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2416_pb : Scalar.QComplex := ((-306082363065611390289813 : Int)/10^30,(-431477410705379550217911032 : Int)/10^30)
theorem v2416_pb_checked : Scalar.distance (sourceCoefficient 29 39 1 1) v2416_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2416_pg : Scalar.QComplex := ((-93086406288689007058339 : Int)/10^30,(66033832824639891783 : Int)/10^30)
theorem v2416_pg_checked : Scalar.distance (sourceCoefficient 29 39 1 2) v2416_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2416_mb : Scalar.QComplex := ((-678427821514711003174465 : Int)/10^30,(-431476985911326165043543572 : Int)/10^30)
theorem v2416_mb_checked : Scalar.distance (sourceCoefficient 29 39 3 1) v2416_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2416_mg : Scalar.QComplex := ((-93086314644142012611516 : Int)/10^30,(146363184408256692701 : Int)/10^30)
theorem v2416_mg_checked : Scalar.distance (sourceCoefficient 29 39 3 2) v2416_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2416_upper : Scalar.QComplex := ((999997034677550057172189787087 : Int)/10^30,(-2435289737741368524056990809 : Int)/10^30)
theorem v2416_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 29 39 5) 1) 14) v2416_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2416 : Material (29 : Basis) (39 : Basis) where
  plus := ![v2416_pa,v2416_pb,v2416_pg]
  minus := ![(Primitive.Addresses.material2416 1).one,v2416_mb,v2416_mg]
  upper := v2416_upper
  lower := (Primitive.Addresses.material2416 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2416_pa_checked.trans (by decide +kernel)
    · exact v2416_pb_checked.trans (by decide +kernel)
    · exact v2416_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 29 39 Primitive.Addresses.material2416
    · exact v2416_mb_checked.trans (by decide +kernel)
    · exact v2416_mg_checked.trans (by decide +kernel)
  upper_error := v2416_upper_checked
  lower_error := reuse_lower_error 29 39 Primitive.Addresses.material2416

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
