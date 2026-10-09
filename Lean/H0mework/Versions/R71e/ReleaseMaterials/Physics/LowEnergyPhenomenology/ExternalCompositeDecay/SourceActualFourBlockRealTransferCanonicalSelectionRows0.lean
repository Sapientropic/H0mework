import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferCanonicalSelection
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorCanonical79Data
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

def canonicalInverseSelectorRow0 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (0,0)
  | 1 => some (1,0)
  | 18 => some (2,0)
  | 19 => some (3,0)
  | 22 => some (4,0)
  | 23 => some (5,0)
  | 30 => some (6,0)
  | 31 => some (7,0)
  | 34 => some (8,0)
  | 35 => some (9,0)
  | 36 => some (10,0)
  | 37 => some (11,0)
  | 49 => some (12,0)
  | 51 => some (13,0)
  | 55 => some (14,0)
  | 56 => some (15,0)
  | 61 => some (16,0)
  | 63 => some (17,0)
  | 67 => some (18,0)
  | 71 => some (19,0)
  | 73 => some (20,0)
  | 77 => some (21,0)
  | _ => none

theorem actual_canonical_inverse_row0 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 0 b = scaling 0 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow0 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow1 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (22,0)
  | 1 => some (0,0)
  | 18 => some (6,0)
  | 19 => some (7,0)
  | 22 => some (8,0)
  | 23 => some (9,0)
  | 30 => some (23,0)
  | 31 => some (24,0)
  | 34 => some (25,0)
  | 35 => some (26,0)
  | 36 => some (27,0)
  | 37 => some (10,0)
  | 49 => some (13,0)
  | 51 => some (28,0)
  | 55 => some (15,0)
  | 56 => some (29,0)
  | 61 => some (19,0)
  | 63 => some (30,0)
  | 67 => some (21,0)
  | 71 => some (31,0)
  | 73 => some (17,0)
  | 77 => some (32,0)
  | _ => none

theorem actual_canonical_inverse_row1 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 1 b = scaling 1 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow1 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow2 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 2 => some (180,1)
  | 3 => some (181,1)
  | 16 => some (182,1)
  | 17 => some (183,1)
  | 28 => some (184,1)
  | 29 => some (182,1)
  | 38 => some (185,1)
  | 39 => some (186,1)
  | 62 => some (187,1)
  | 68 => some (188,1)
  | 72 => some (189,1)
  | 78 => some (190,1)
  | _ => none

theorem actual_canonical_inverse_row2 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 2 b = scaling 2 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow2 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow3 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 2 => some (191,1)
  | 3 => some (180,1)
  | 16 => some (184,1)
  | 17 => some (182,1)
  | 28 => some (192,1)
  | 29 => some (184,1)
  | 38 => some (193,1)
  | 39 => some (185,1)
  | 62 => some (189,1)
  | 68 => some (190,1)
  | 72 => some (194,1)
  | 78 => some (195,1)
  | _ => none

theorem actual_canonical_inverse_row3 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 3 b = scaling 3 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow3 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow4 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 4 => some (180,2)
  | 5 => some (191,2)
  | 14 => some (192,2)
  | 15 => some (183,2)
  | 26 => some (183,2)
  | 27 => some (182,2)
  | 40 => some (185,2)
  | 41 => some (193,2)
  | 59 => some (195,2)
  | 65 => some (194,2)
  | 69 => some (190,2)
  | 75 => some (189,2)
  | _ => none

theorem actual_canonical_inverse_row4 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 4 b = scaling 4 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow4 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow5 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 4 => some (181,2)
  | 5 => some (180,2)
  | 14 => some (184,2)
  | 15 => some (192,2)
  | 26 => some (192,2)
  | 27 => some (183,2)
  | 40 => some (186,2)
  | 41 => some (185,2)
  | 59 => some (190,2)
  | 65 => some (189,2)
  | 69 => some (188,2)
  | 75 => some (187,2)
  | _ => none

theorem actual_canonical_inverse_row5 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 5 b = scaling 5 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow5 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow6 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (233,3)
  | 7 => some (234,3)
  | 10 => some (235,3)
  | 11 => some (236,3)
  | 12 => some (237,3)
  | 13 => some (238,3)
  | 24 => some (239,3)
  | 25 => some (240,3)
  | 42 => some (241,3)
  | 43 => some (242,3)
  | 46 => some (243,3)
  | 47 => some (244,3)
  | 48 => some (245,3)
  | 50 => some (246,3)
  | 52 => some (247,3)
  | 53 => some (248,3)
  | 54 => some (249,3)
  | 57 => some (250,3)
  | 58 => some (251,3)
  | 60 => some (252,3)
  | 64 => some (253,3)
  | 66 => some (254,3)
  | 70 => some (255,3)
  | 74 => some (256,3)
  | 76 => some (257,3)
  | _ => none

theorem actual_canonical_inverse_row6 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 6 b = scaling 6 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow6 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow7 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (234,3)
  | 7 => some (258,3)
  | 10 => some (259,3)
  | 11 => some (260,3)
  | 12 => some (261,3)
  | 13 => some (262,3)
  | 24 => some (263,3)
  | 25 => some (264,3)
  | 42 => some (265,3)
  | 43 => some (266,3)
  | 46 => some (267,3)
  | 47 => some (268,3)
  | 48 => some (269,3)
  | 50 => some (270,3)
  | 52 => some (271,3)
  | 53 => some (272,3)
  | 54 => some (273,3)
  | 57 => some (274,3)
  | 58 => some (275,3)
  | 60 => some (276,3)
  | 64 => some (277,3)
  | 66 => some (278,3)
  | 70 => some (279,3)
  | 74 => some (280,3)
  | 76 => some (281,3)
  | _ => none

theorem actual_canonical_inverse_row7 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 7 b = scaling 7 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow7 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow8 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 8 => some (522,4)
  | 44 => some (523,4)
  | _ => none

theorem actual_canonical_inverse_row8 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 8 b = scaling 8 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow8 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow9 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 9 => some (522,5)
  | 45 => some (523,5)
  | _ => none

theorem actual_canonical_inverse_row9 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 9 b = scaling 9 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow9 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow10 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (235,3)
  | 7 => some (259,3)
  | 10 => some (282,3)
  | 11 => some (283,3)
  | 12 => some (284,3)
  | 25 => some (285,3)
  | 42 => some (286,3)
  | 43 => some (287,3)
  | 46 => some (288,3)
  | 47 => some (289,3)
  | 58 => some (290,3)
  | 60 => some (291,3)
  | 64 => some (291,3)
  | 66 => some (290,3)
  | 70 => some (292,3)
  | 74 => some (293,3)
  | 76 => some (294,3)
  | _ => none

theorem actual_canonical_inverse_row10 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 10 b = scaling 10 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow10 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow11 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (236,3)
  | 7 => some (260,3)
  | 10 => some (283,3)
  | 11 => some (295,3)
  | 12 => some (296,3)
  | 25 => some (297,3)
  | 42 => some (298,3)
  | 43 => some (299,3)
  | 46 => some (289,3)
  | 47 => some (300,3)
  | 58 => some (301,3)
  | 60 => some (302,3)
  | 64 => some (302,3)
  | 66 => some (301,3)
  | 70 => some (303,3)
  | 74 => some (304,3)
  | 76 => some (305,3)
  | _ => none

theorem actual_canonical_inverse_row11 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 11 b = scaling 11 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow11 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow12 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (306,3)
  | 7 => some (307,3)
  | 10 => some (285,3)
  | 11 => some (297,3)
  | 12 => some (308,3)
  | 13 => some (309,3)
  | 24 => some (310,3)
  | 25 => some (311,3)
  | 42 => some (312,3)
  | 43 => some (313,3)
  | 46 => some (314,3)
  | 47 => some (315,3)
  | 48 => some (316,3)
  | 50 => some (317,3)
  | 52 => some (318,3)
  | 53 => some (319,3)
  | 54 => some (320,3)
  | 57 => some (321,3)
  | 58 => some (322,3)
  | 60 => some (323,3)
  | 64 => some (324,3)
  | 66 => some (325,3)
  | 70 => some (326,3)
  | 74 => some (327,3)
  | 76 => some (328,3)
  | _ => none

theorem actual_canonical_inverse_row12 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 12 b = scaling 12 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow12 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow13 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (238,3)
  | 7 => some (262,3)
  | 12 => some (329,3)
  | 13 => some (330,3)
  | 24 => some (331,3)
  | 25 => some (332,3)
  | 42 => some (333,3)
  | 43 => some (334,3)
  | 48 => some (335,3)
  | 50 => some (336,3)
  | 52 => some (337,3)
  | 53 => some (338,3)
  | 54 => some (339,3)
  | 57 => some (340,3)
  | 58 => some (341,3)
  | 60 => some (342,3)
  | 64 => some (343,3)
  | 66 => some (344,3)
  | 70 => some (345,3)
  | 74 => some (345,3)
  | _ => none

theorem actual_canonical_inverse_row13 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 13 b = scaling 13 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow13 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow14 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 4 => some (192,2)
  | 5 => some (183,2)
  | 14 => some (196,2)
  | 15 => some (206,2)
  | 26 => some (198,2)
  | 27 => some (207,2)
  | 40 => some (212,2)
  | 41 => some (201,2)
  | 59 => some (203,2)
  | 65 => some (202,2)
  | 69 => some (214,2)
  | 75 => some (213,2)
  | _ => none

theorem actual_canonical_inverse_row14 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 14 b = scaling 14 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow14 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow15 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 4 => some (184,2)
  | 5 => some (192,2)
  | 14 => some (197,2)
  | 15 => some (196,2)
  | 26 => some (199,2)
  | 27 => some (198,2)
  | 40 => some (208,2)
  | 41 => some (212,2)
  | 59 => some (214,2)
  | 65 => some (213,2)
  | 69 => some (210,2)
  | 75 => some (209,2)
  | _ => none

theorem actual_canonical_inverse_row15 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 15 b = scaling 15 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow15 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow16 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 2 => some (182,1)
  | 3 => some (183,1)
  | 16 => some (196,1)
  | 17 => some (197,1)
  | 28 => some (198,1)
  | 29 => some (199,1)
  | 38 => some (200,1)
  | 39 => some (201,1)
  | 62 => some (202,1)
  | 68 => some (203,1)
  | 72 => some (204,1)
  | 78 => some (205,1)
  | _ => none

theorem actual_canonical_inverse_row16 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 16 b = scaling 16 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow16 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow17 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 2 => some (184,1)
  | 3 => some (182,1)
  | 16 => some (206,1)
  | 17 => some (196,1)
  | 28 => some (207,1)
  | 29 => some (198,1)
  | 38 => some (208,1)
  | 39 => some (200,1)
  | 62 => some (204,1)
  | 68 => some (205,1)
  | 72 => some (209,1)
  | 78 => some (210,1)
  | _ => none

theorem actual_canonical_inverse_row17 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 17 b = scaling 17 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow17 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow18 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (23,0)
  | 1 => some (6,0)
  | 18 => some (33,0)
  | 19 => some (34,0)
  | 22 => some (35,0)
  | 23 => some (36,0)
  | 30 => some (37,0)
  | 31 => some (38,0)
  | 34 => some (39,0)
  | 35 => some (40,0)
  | 36 => some (41,0)
  | 37 => some (42,0)
  | 49 => some (43,0)
  | 51 => some (44,0)
  | 55 => some (45,0)
  | 56 => some (46,0)
  | 61 => some (47,0)
  | 63 => some (48,0)
  | 67 => some (49,0)
  | 71 => some (50,0)
  | 73 => some (51,0)
  | 77 => some (52,0)
  | _ => none

theorem actual_canonical_inverse_row18 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 18 b = scaling 18 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow18 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow19 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (24,0)
  | 1 => some (7,0)
  | 18 => some (34,0)
  | 19 => some (53,0)
  | 22 => some (54,0)
  | 23 => some (55,0)
  | 30 => some (38,0)
  | 31 => some (56,0)
  | 34 => some (57,0)
  | 35 => some (58,0)
  | 36 => some (59,0)
  | 37 => some (60,0)
  | 49 => some (61,0)
  | 51 => some (62,0)
  | 55 => some (63,0)
  | 56 => some (64,0)
  | 61 => some (65,0)
  | 63 => some (66,0)
  | 67 => some (67,0)
  | 71 => some (68,0)
  | 73 => some (69,0)
  | 77 => some (70,0)
  | _ => none

theorem actual_canonical_inverse_row19 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 19 b = scaling 19 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow19 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow20 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 20 => some (525,6)
  | _ => none

theorem actual_canonical_inverse_row20 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 20 b = scaling 20 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow20 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow21 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 21 => some (525,7)
  | _ => none

theorem actual_canonical_inverse_row21 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 21 b = scaling 21 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow21 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow22 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (25,0)
  | 1 => some (8,0)
  | 18 => some (35,0)
  | 19 => some (54,0)
  | 22 => some (71,0)
  | 23 => some (72,0)
  | 30 => some (39,0)
  | 31 => some (57,0)
  | 34 => some (73,0)
  | 35 => some (74,0)
  | 36 => some (75,0)
  | 37 => some (76,0)
  | 61 => some (77,0)
  | 63 => some (78,0)
  | 67 => some (79,0)
  | 71 => some (80,0)
  | 73 => some (81,0)
  | 77 => some (82,0)
  | _ => none

theorem actual_canonical_inverse_row22 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 22 b = scaling 22 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow22 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow23 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (26,0)
  | 1 => some (9,0)
  | 18 => some (36,0)
  | 19 => some (55,0)
  | 22 => some (72,0)
  | 23 => some (83,0)
  | 30 => some (40,0)
  | 31 => some (58,0)
  | 34 => some (74,0)
  | 35 => some (84,0)
  | 36 => some (85,0)
  | 37 => some (86,0)
  | 61 => some (87,0)
  | 63 => some (88,0)
  | 67 => some (89,0)
  | 71 => some (90,0)
  | 73 => some (91,0)
  | 77 => some (92,0)
  | _ => none

theorem actual_canonical_inverse_row23 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 23 b = scaling 23 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow23 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow24 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (239,3)
  | 7 => some (263,3)
  | 12 => some (346,3)
  | 13 => some (331,3)
  | 24 => some (330,3)
  | 25 => some (347,3)
  | 42 => some (348,3)
  | 43 => some (349,3)
  | 48 => some (335,3)
  | 50 => some (338,3)
  | 52 => some (350,3)
  | 53 => some (336,3)
  | 54 => some (339,3)
  | 57 => some (340,3)
  | 58 => some (341,3)
  | 60 => some (342,3)
  | 64 => some (343,3)
  | 66 => some (344,3)
  | 70 => some (345,3)
  | 74 => some (345,3)
  | _ => none

theorem actual_canonical_inverse_row24 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 24 b = scaling 24 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow24 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow25 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 6 => some (351,3)
  | 7 => some (352,3)
  | 10 => some (284,3)
  | 11 => some (296,3)
  | 12 => some (311,3)
  | 13 => some (353,3)
  | 24 => some (354,3)
  | 25 => some (355,3)
  | 42 => some (356,3)
  | 43 => some (357,3)
  | 46 => some (358,3)
  | 47 => some (359,3)
  | 48 => some (360,3)
  | 50 => some (361,3)
  | 52 => some (362,3)
  | 53 => some (363,3)
  | 54 => some (364,3)
  | 57 => some (365,3)
  | 58 => some (366,3)
  | 60 => some (367,3)
  | 64 => some (368,3)
  | 66 => some (369,3)
  | 70 => some (370,3)
  | 74 => some (371,3)
  | 76 => some (372,3)
  | _ => none

theorem actual_canonical_inverse_row25 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 25 b = scaling 25 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow25 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow26 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 4 => some (184,2)
  | 5 => some (192,2)
  | 14 => some (211,2)
  | 15 => some (199,2)
  | 26 => some (196,2)
  | 27 => some (206,2)
  | 40 => some (208,2)
  | 41 => some (212,2)
  | 59 => some (214,2)
  | 65 => some (213,2)
  | 69 => some (210,2)
  | 75 => some (209,2)
  | _ => none

theorem actual_canonical_inverse_row26 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 26 b = scaling 26 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow26 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow27 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 4 => some (182,2)
  | 5 => some (184,2)
  | 14 => some (207,2)
  | 15 => some (211,2)
  | 26 => some (197,2)
  | 27 => some (196,2)
  | 40 => some (200,2)
  | 41 => some (208,2)
  | 59 => some (210,2)
  | 65 => some (209,2)
  | 69 => some (205,2)
  | 75 => some (204,2)
  | _ => none

theorem actual_canonical_inverse_row27 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 27 b = scaling 27 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow27 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow28 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 2 => some (183,1)
  | 3 => some (192,1)
  | 16 => some (211,1)
  | 17 => some (207,1)
  | 28 => some (196,1)
  | 29 => some (197,1)
  | 38 => some (201,1)
  | 39 => some (212,1)
  | 62 => some (213,1)
  | 68 => some (214,1)
  | 72 => some (202,1)
  | 78 => some (203,1)
  | _ => none

theorem actual_canonical_inverse_row28 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 28 b = scaling 28 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow28 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow29 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 2 => some (182,1)
  | 3 => some (183,1)
  | 16 => some (199,1)
  | 17 => some (211,1)
  | 28 => some (206,1)
  | 29 => some (196,1)
  | 38 => some (200,1)
  | 39 => some (201,1)
  | 62 => some (202,1)
  | 68 => some (203,1)
  | 72 => some (204,1)
  | 78 => some (205,1)
  | _ => none

theorem actual_canonical_inverse_row29 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 29 b = scaling 29 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow29 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow30 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (6,0)
  | 1 => some (2,0)
  | 18 => some (93,0)
  | 19 => some (94,0)
  | 22 => some (95,0)
  | 23 => some (96,0)
  | 30 => some (33,0)
  | 31 => some (34,0)
  | 34 => some (35,0)
  | 35 => some (36,0)
  | 36 => some (42,0)
  | 37 => some (97,0)
  | 49 => some (62,0)
  | 51 => some (43,0)
  | 55 => some (64,0)
  | 56 => some (45,0)
  | 61 => some (98,0)
  | 63 => some (51,0)
  | 67 => some (99,0)
  | 71 => some (47,0)
  | 73 => some (100,0)
  | 77 => some (49,0)
  | _ => none

theorem actual_canonical_inverse_row30 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 30 b = scaling 30 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow30 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow31 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (7,0)
  | 1 => some (3,0)
  | 18 => some (94,0)
  | 19 => some (101,0)
  | 22 => some (102,0)
  | 23 => some (103,0)
  | 30 => some (34,0)
  | 31 => some (53,0)
  | 34 => some (54,0)
  | 35 => some (55,0)
  | 36 => some (60,0)
  | 37 => some (104,0)
  | 49 => some (44,0)
  | 51 => some (61,0)
  | 55 => some (46,0)
  | 56 => some (63,0)
  | 61 => some (105,0)
  | 63 => some (69,0)
  | 67 => some (106,0)
  | 71 => some (65,0)
  | 73 => some (107,0)
  | 77 => some (67,0)
  | _ => none

theorem actual_canonical_inverse_row31 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 31 b = scaling 31 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow31 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow32 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 32 => some (525,8)
  | _ => none

theorem actual_canonical_inverse_row32 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 32 b = scaling 32 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow32 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow33 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 33 => some (525,9)
  | _ => none

theorem actual_canonical_inverse_row33 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 33 b = scaling 33 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow33 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow34 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (8,0)
  | 1 => some (4,0)
  | 18 => some (95,0)
  | 19 => some (102,0)
  | 22 => some (108,0)
  | 23 => some (109,0)
  | 30 => some (35,0)
  | 31 => some (54,0)
  | 34 => some (71,0)
  | 35 => some (72,0)
  | 36 => some (76,0)
  | 37 => some (110,0)
  | 61 => some (111,0)
  | 63 => some (81,0)
  | 67 => some (112,0)
  | 71 => some (77,0)
  | 73 => some (113,0)
  | 77 => some (79,0)
  | _ => none

theorem actual_canonical_inverse_row34 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 34 b = scaling 34 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow34 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow35 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (9,0)
  | 1 => some (5,0)
  | 18 => some (96,0)
  | 19 => some (103,0)
  | 22 => some (109,0)
  | 23 => some (114,0)
  | 30 => some (36,0)
  | 31 => some (55,0)
  | 34 => some (72,0)
  | 35 => some (83,0)
  | 36 => some (86,0)
  | 37 => some (115,0)
  | 61 => some (116,0)
  | 63 => some (91,0)
  | 67 => some (117,0)
  | 71 => some (87,0)
  | 73 => some (118,0)
  | 77 => some (89,0)
  | _ => none

theorem actual_canonical_inverse_row35 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 35 b = scaling 35 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow35 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow36 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (10,0)
  | 1 => some (11,0)
  | 18 => some (97,0)
  | 19 => some (104,0)
  | 22 => some (110,0)
  | 23 => some (115,0)
  | 30 => some (42,0)
  | 31 => some (60,0)
  | 34 => some (76,0)
  | 35 => some (86,0)
  | 36 => some (119,0)
  | 37 => some (120,0)
  | 49 => some (121,0)
  | 51 => some (122,0)
  | 55 => some (123,0)
  | 56 => some (124,0)
  | 61 => some (125,0)
  | 63 => some (126,0)
  | 67 => some (127,0)
  | 71 => some (128,0)
  | 73 => some (129,0)
  | 77 => some (130,0)
  | _ => none

theorem actual_canonical_inverse_row36 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 36 b = scaling 36 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow36 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow37 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 0 => some (27,0)
  | 1 => some (10,0)
  | 18 => some (42,0)
  | 19 => some (60,0)
  | 22 => some (76,0)
  | 23 => some (86,0)
  | 30 => some (41,0)
  | 31 => some (59,0)
  | 34 => some (75,0)
  | 35 => some (85,0)
  | 36 => some (131,0)
  | 37 => some (119,0)
  | 49 => some (122,0)
  | 51 => some (132,0)
  | 55 => some (124,0)
  | 56 => some (133,0)
  | 61 => some (128,0)
  | 63 => some (134,0)
  | 67 => some (130,0)
  | 71 => some (135,0)
  | 73 => some (126,0)
  | 77 => some (136,0)
  | _ => none

theorem actual_canonical_inverse_row37 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 37 b = scaling 37 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow37 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow38 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 2 => some (185,1)
  | 3 => some (186,1)
  | 16 => some (200,1)
  | 17 => some (201,1)
  | 28 => some (208,1)
  | 29 => some (200,1)
  | 38 => some (215,1)
  | 39 => some (216,1)
  | 62 => some (217,1)
  | 68 => some (218,1)
  | 72 => some (219,1)
  | 78 => some (220,1)
  | _ => none

theorem actual_canonical_inverse_row38 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 38 b = scaling 38 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow38 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

def canonicalInverseSelectorRow39 (b : Fin 79) : Option (Fin 526 × Fin 10) :=
  match b.val with
  | 2 => some (193,1)
  | 3 => some (185,1)
  | 16 => some (208,1)
  | 17 => some (200,1)
  | 28 => some (212,1)
  | 29 => some (208,1)
  | 38 => some (221,1)
  | 39 => some (215,1)
  | 62 => some (219,1)
  | 68 => some (220,1)
  | 72 => some (222,1)
  | 78 => some (223,1)
  | _ => none

theorem actual_canonical_inverse_row39 (x : ℂ) (b : Fin 79) :
    axialInverse x 0 39 b = scaling 39 *
      selectedCanonicalInverse x (canonicalInverseSelectorRow39 b) * scaling b / (lapse : ℂ) := by
  fin_cases b <;> rfl

end LowEnergy.ActualFourBlockRealTransfer
