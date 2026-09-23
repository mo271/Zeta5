import Apery.Table2.I00
import Apery.Table2.I01
import Apery.Table2.I02
import Apery.Table2.I03
import Apery.Table2.I04
import Apery.Table2.I05
import Apery.Table2.I06
import Apery.Table2.I07
import Apery.Table2.I08
import Apery.Table2.I09
import Apery.Table2.I10
import Apery.Table2.I11
import Apery.Table2.I12
import Apery.Table2.I13
import Apery.Table2.I14
import Apery.Table2.I15
import Apery.Table2.I16
import Apery.Table2.I17

namespace Apery

lemma J_0_2 : ∀ t : ℝ, (0 : ℝ) < t → t ≤ (21522393 / 400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7174131 / 200000000000 : ℝ) with h | h
  · exact I_0 t h1 h
  · exact I_1 t h h2

lemma J_3_5 : ∀ t : ℝ, (7174131 / 100000000000 : ℝ) < t → t ≤ (78667711 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (14825913 / 200000000000 : ℝ) with h | h
  · exact I_3 t h1 h
  · exact I_4 t h h2

lemma J_2_5 : ∀ t : ℝ, (21522393 / 400000000000 : ℝ) < t → t ≤ (78667711 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7174131 / 100000000000 : ℝ) with h | h
  · exact I_2 t h1 h
  · exact J_3_5 t h h2

lemma J_0_5 : ∀ t : ℝ, (0 : ℝ) < t → t ≤ (78667711 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (21522393 / 400000000000 : ℝ) with h | h
  · exact J_0_2 t h1 h
  · exact J_2_5 t h h2

lemma J_5_7 : ∀ t : ℝ, (78667711 / 1000000000000 : ℝ) < t → t ≤ (19269871 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (85815639 / 1000000000000 : ℝ) with h | h
  · exact I_5 t h1 h
  · exact I_6 t h h2

lemma J_8_10 : ∀ t : ℝ, (55761057 / 500000000000 : ℝ) < t → t ≤ (82548843 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (33336783 / 250000000000 : ℝ) with h | h
  · exact I_8 t h1 h
  · exact I_9 t h h2

lemma J_7_10 : ∀ t : ℝ, (19269871 / 200000000000 : ℝ) < t → t ≤ (82548843 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (55761057 / 500000000000 : ℝ) with h | h
  · exact I_7 t h1 h
  · exact J_8_10 t h h2

lemma J_5_10 : ∀ t : ℝ, (78667711 / 1000000000000 : ℝ) < t → t ≤ (82548843 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19269871 / 200000000000 : ℝ) with h | h
  · exact J_5_7 t h1 h
  · exact J_7_10 t h h2

lemma J_0_10 : ∀ t : ℝ, (0 : ℝ) < t → t ≤ (82548843 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (78667711 / 1000000000000 : ℝ) with h | h
  · exact J_0_5 t h1 h
  · exact J_5_10 t h h2

lemma J_10_12 : ∀ t : ℝ, (82548843 / 500000000000 : ℝ) < t → t ≤ (496117379 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (53051547 / 250000000000 : ℝ) with h | h
  · exact I_10 t h1 h
  · exact I_11 t h h2

lemma J_13_15 : ∀ t : ℝ, (283911191 / 1000000000000 : ℝ) < t → t ≤ (396324613 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (170058951 / 500000000000 : ℝ) with h | h
  · exact I_13 t h1 h
  · exact I_14 t h h2

lemma J_12_15 : ∀ t : ℝ, (496117379 / 2000000000000 : ℝ) < t → t ≤ (396324613 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (283911191 / 1000000000000 : ℝ) with h | h
  · exact I_12 t h1 h
  · exact J_13_15 t h h2

lemma J_10_15 : ∀ t : ℝ, (82548843 / 500000000000 : ℝ) < t → t ≤ (396324613 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (496117379 / 2000000000000 : ℝ) with h | h
  · exact J_10_12 t h1 h
  · exact J_12_15 t h h2

lemma J_16_18 : ∀ t : ℝ, (974522519 / 2000000000000 : ℝ) < t → t ≤ (729961631 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (289098953 / 500000000000 : ℝ) with h | h
  · exact I_16 t h1 h
  · exact I_17 t h h2

lemma J_15_18 : ∀ t : ℝ, (396324613 / 1000000000000 : ℝ) < t → t ≤ (729961631 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (974522519 / 2000000000000 : ℝ) with h | h
  · exact I_15 t h1 h
  · exact J_16_18 t h h2

lemma J_19_21 : ∀ t : ℝ, (1611686987 / 2000000000000 : ℝ) < t → t ≤ (4047462733 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (220431339 / 250000000000 : ℝ) with h | h
  · exact I_19 t h1 h
  · exact I_20 t h h2

lemma J_18_21 : ∀ t : ℝ, (729961631 / 1000000000000 : ℝ) < t → t ≤ (4047462733 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1611686987 / 2000000000000 : ℝ) with h | h
  · exact I_18 t h1 h
  · exact J_19_21 t h h2

lemma J_15_21 : ∀ t : ℝ, (396324613 / 1000000000000 : ℝ) < t → t ≤ (4047462733 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (729961631 / 1000000000000 : ℝ) with h | h
  · exact J_15_18 t h1 h
  · exact J_18_21 t h h2

lemma J_10_21 : ∀ t : ℝ, (82548843 / 500000000000 : ℝ) < t → t ≤ (4047462733 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (396324613 / 1000000000000 : ℝ) with h | h
  · exact J_10_15 t h1 h
  · exact J_15_21 t h h2

lemma J_0_21 : ∀ t : ℝ, (0 : ℝ) < t → t ≤ (4047462733 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (82548843 / 500000000000 : ℝ) with h | h
  · exact J_0_10 t h1 h
  · exact J_10_21 t h h2

lemma J_21_23 : ∀ t : ℝ, (4047462733 / 4000000000000 : ℝ) < t → t ≤ (5088585351 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2284012021 / 2000000000000 : ℝ) with h | h
  · exact I_21 t h1 h
  · exact I_22 t h h2

lemma J_24_26 : ∀ t : ℝ, (280457333 / 200000000000 : ℝ) < t → t ≤ (3714534929 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (6519108259 / 4000000000000 : ℝ) with h | h
  · exact I_24 t h1 h
  · exact I_25 t h h2

lemma J_23_26 : ∀ t : ℝ, (5088585351 / 4000000000000 : ℝ) < t → t ≤ (3714534929 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (280457333 / 200000000000 : ℝ) with h | h
  · exact I_23 t h1 h
  · exact J_24_26 t h h2

lemma J_21_26 : ∀ t : ℝ, (4047462733 / 4000000000000 : ℝ) < t → t ≤ (3714534929 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5088585351 / 4000000000000 : ℝ) with h | h
  · exact J_21_23 t h1 h
  · exact J_23_26 t h h2

lemma J_26_28 : ∀ t : ℝ, (3714534929 / 2000000000000 : ℝ) < t → t ≤ (289031033 / 125000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (8339031457 / 4000000000000 : ℝ) with h | h
  · exact I_26 t h1 h
  · exact I_27 t h h2

lemma J_29_31 : ∀ t : ℝ, (124379927 / 40000000000 : ℝ) < t → t ≤ (1953374043 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7016246261 / 2000000000000 : ℝ) with h | h
  · exact I_29 t h1 h
  · exact I_30 t h h2

lemma J_28_31 : ∀ t : ℝ, (289031033 / 125000000000 : ℝ) < t → t ≤ (1953374043 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (124379927 / 40000000000 : ℝ) with h | h
  · exact I_28 t h1 h
  · exact J_29_31 t h h2

lemma J_26_31 : ∀ t : ℝ, (3714534929 / 2000000000000 : ℝ) < t → t ≤ (1953374043 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (289031033 / 125000000000 : ℝ) with h | h
  · exact J_26_28 t h1 h
  · exact J_28_31 t h h2

lemma J_21_31 : ∀ t : ℝ, (4047462733 / 4000000000000 : ℝ) < t → t ≤ (1953374043 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3714534929 / 2000000000000 : ℝ) with h | h
  · exact J_21_26 t h1 h
  · exact J_26_31 t h h2

lemma J_31_33 : ∀ t : ℝ, (1953374043 / 500000000000 : ℝ) < t → t ≤ (59205079 / 10000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (59205077 / 10000000000 : ℝ) with h | h
  · exact I_31 t h1 h
  · exact I_32 t h h2

lemma J_34_36 : ∀ t : ℝ, (8992695531 / 1000000000000 : ℝ) < t → t ≤ (40732008867 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19572466643 / 2000000000000 : ℝ) with h | h
  · exact I_34 t h1 h
  · exact I_35 t h h2

lemma J_33_36 : ∀ t : ℝ, (59205079 / 10000000000 : ℝ) < t → t ≤ (40732008867 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (8992695531 / 1000000000000 : ℝ) with h | h
  · exact I_33 t h1 h
  · exact J_34_36 t h h2

lemma J_31_36 : ∀ t : ℝ, (1953374043 / 500000000000 : ℝ) < t → t ≤ (40732008867 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (59205079 / 10000000000 : ℝ) with h | h
  · exact J_31_33 t h1 h
  · exact J_33_36 t h h2

lemma J_37_39 : ∀ t : ℝ, (1322471389 / 125000000000 : ℝ) < t → t ≤ (12166846693 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4549323561 / 400000000000 : ℝ) with h | h
  · exact I_37 t h1 h
  · exact I_38 t h h2

lemma J_36_39 : ∀ t : ℝ, (40732008867 / 4000000000000 : ℝ) < t → t ≤ (12166846693 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1322471389 / 125000000000 : ℝ) with h | h
  · exact I_36 t h1 h
  · exact J_37_39 t h h2

lemma J_40_42 : ∀ t : ℝ, (3068199571 / 200000000000 : ℝ) < t → t ≤ (133117165709 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (255845148549 / 16000000000000 : ℝ) with h | h
  · exact I_40 t h1 h
  · exact I_41 t h h2

lemma J_39_42 : ∀ t : ℝ, (12166846693 / 1000000000000 : ℝ) < t → t ≤ (133117165709 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3068199571 / 200000000000 : ℝ) with h | h
  · exact I_39 t h1 h
  · exact J_40_42 t h h2

lemma J_36_42 : ∀ t : ℝ, (40732008867 / 4000000000000 : ℝ) < t → t ≤ (133117165709 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (12166846693 / 1000000000000 : ℝ) with h | h
  · exact J_36_39 t h1 h
  · exact J_39_42 t h h2

lemma J_31_42 : ∀ t : ℝ, (1953374043 / 500000000000 : ℝ) < t → t ≤ (133117165709 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (40732008867 / 4000000000000 : ℝ) with h | h
  · exact J_31_36 t h1 h
  · exact J_36_42 t h h2

lemma J_21_42 : ∀ t : ℝ, (4047462733 / 4000000000000 : ℝ) < t → t ≤ (133117165709 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1953374043 / 500000000000 : ℝ) with h | h
  · exact J_21_31 t h1 h
  · exact J_31_42 t h h2

lemma J_0_42 : ∀ t : ℝ, (0 : ℝ) < t → t ≤ (133117165709 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4047462733 / 4000000000000 : ℝ) with h | h
  · exact J_0_21 t h1 h
  · exact J_21_42 t h h2

lemma J_42_44 : ∀ t : ℝ, (133117165709 / 8000000000000 : ℝ) < t → t ≤ (276623514287 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (108571569141 / 6400000000000 : ℝ) with h | h
  · exact I_42 t h1 h
  · exact I_43 t h h2

lemma J_45_47 : ∀ t : ℝ, (563636211443 / 32000000000000 : ℝ) < t → t ≤ (584414577181 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (71753174289 / 4000000000000 : ℝ) with h | h
  · exact I_45 t h1 h
  · exact I_46 t h h2

lemma J_44_47 : ∀ t : ℝ, (276623514287 / 16000000000000 : ℝ) < t → t ≤ (584414577181 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (563636211443 / 32000000000000 : ℝ) with h | h
  · exact I_44 t h1 h
  · exact J_45_47 t h h2

lemma J_42_47 : ∀ t : ℝ, (133117165709 / 8000000000000 : ℝ) < t → t ≤ (584414577181 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (276623514287 / 16000000000000 : ℝ) with h | h
  · exact J_42_44 t h1 h
  · exact J_44_47 t h h2

lemma J_47_49 : ∀ t : ℝ, (584414577181 / 32000000000000 : ℝ) < t → t ≤ (605192942919 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11896075201 / 640000000000 : ℝ) with h | h
  · exact I_47 t h1 h
  · exact I_48 t h h2

lemma J_50_52 : ∀ t : ℝ, (153895531447 / 8000000000000 : ℝ) < t → t ≤ (41071178579 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (318180245763 / 16000000000000 : ℝ) with h | h
  · exact I_50 t h1 h
  · exact I_51 t h h2

lemma J_49_52 : ∀ t : ℝ, (605192942919 / 32000000000000 : ℝ) < t → t ≤ (41071178579 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (153895531447 / 8000000000000 : ℝ) with h | h
  · exact I_49 t h1 h
  · exact J_50_52 t h h2

lemma J_47_52 : ∀ t : ℝ, (584414577181 / 32000000000000 : ℝ) < t → t ≤ (41071178579 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (605192942919 / 32000000000000 : ℝ) with h | h
  · exact J_47_49 t h1 h
  · exact J_49_52 t h h2

lemma J_42_52 : ∀ t : ℝ, (133117165709 / 8000000000000 : ℝ) < t → t ≤ (41071178579 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (584414577181 / 32000000000000 : ℝ) with h | h
  · exact J_42_47 t h1 h
  · exact J_47_52 t h h2

lemma J_52_54 : ∀ t : ℝ, (41071178579 / 2000000000000 : ℝ) < t → t ≤ (92531540027 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (34934779437 / 1600000000000 : ℝ) with h | h
  · exact I_52 t h1 h
  · exact I_53 t h h2

lemma J_55_57 : ∀ t : ℝ, (6432545181 / 250000000000 : ℝ) < t → t ≤ (435951987867 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (213931144553 / 8000000000000 : ℝ) with h | h
  · exact I_55 t h1 h
  · exact I_56 t h h2

lemma J_54_57 : ∀ t : ℝ, (92531540027 / 4000000000000 : ℝ) < t → t ≤ (435951987867 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (6432545181 / 250000000000 : ℝ) with h | h
  · exact I_54 t h1 h
  · exact J_55_57 t h h2

lemma J_52_57 : ∀ t : ℝ, (41071178579 / 2000000000000 : ℝ) < t → t ≤ (435951987867 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (92531540027 / 4000000000000 : ℝ) with h | h
  · exact J_52_54 t h1 h
  · exact J_54_57 t h h2

lemma J_58_60 : ∀ t : ℝ, (111010421657 / 4000000000000 : ℝ) < t → t ≤ (912352469539 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (452131385389 / 16000000000000 : ℝ) with h | h
  · exact I_58 t h1 h
  · exact I_59 t h h2

lemma J_57_60 : ∀ t : ℝ, (435951987867 / 16000000000000 : ℝ) < t → t ≤ (912352469539 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (111010421657 / 4000000000000 : ℝ) with h | h
  · exact I_57 t h1 h
  · exact J_58_60 t h h2

lemma J_61_63 : ∀ t : ℝ, (9204421683 / 320000000000 : ℝ) < t → t ≤ (468310782911 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (928531867061 / 32000000000000 : ℝ) with h | h
  · exact I_61 t h1 h
  · exact I_62 t h h2

lemma J_60_63 : ∀ t : ℝ, (912352469539 / 32000000000000 : ℝ) < t → t ≤ (468310782911 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9204421683 / 320000000000 : ℝ) with h | h
  · exact I_60 t h1 h
  · exact J_61_63 t h h2

lemma J_57_63 : ∀ t : ℝ, (435951987867 / 16000000000000 : ℝ) < t → t ≤ (468310782911 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (912352469539 / 32000000000000 : ℝ) with h | h
  · exact J_57_60 t h1 h
  · exact J_60_63 t h h2

lemma J_52_63 : ∀ t : ℝ, (41071178579 / 2000000000000 : ℝ) < t → t ≤ (468310782911 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (435951987867 / 16000000000000 : ℝ) with h | h
  · exact J_52_57 t h1 h
  · exact J_57_63 t h h2

lemma J_42_63 : ∀ t : ℝ, (133117165709 / 8000000000000 : ℝ) < t → t ≤ (468310782911 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (41071178579 / 2000000000000 : ℝ) with h | h
  · exact J_42_52 t h1 h
  · exact J_52_63 t h h2

lemma J_63_65 : ∀ t : ℝ, (468310782911 / 16000000000000 : ℝ) < t → t ≤ (59550060209 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (944711264583 / 32000000000000 : ℝ) with h | h
  · exact I_63 t h1 h
  · exact I_64 t h h2

lemma J_66_68 : ∀ t : ℝ, (192178132421 / 6400000000000 : ℝ) < t → t ≤ (977070059627 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (484490180433 / 16000000000000 : ℝ) with h | h
  · exact I_66 t h1 h
  · exact I_67 t h h2

lemma J_65_68 : ∀ t : ℝ, (59550060209 / 2000000000000 : ℝ) < t → t ≤ (977070059627 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (192178132421 / 6400000000000 : ℝ) with h | h
  · exact I_65 t h1 h
  · exact J_66_68 t h h2

lemma J_63_68 : ∀ t : ℝ, (468310782911 / 16000000000000 : ℝ) < t → t ≤ (977070059627 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (59550060209 / 2000000000000 : ℝ) with h | h
  · exact J_63_65 t h1 h
  · exact J_65_68 t h h2

lemma J_69_71 : ∀ t : ℝ, (246289939597 / 8000000000000 : ℝ) < t → t ≤ (127189819179 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (100133915591 / 3200000000000 : ℝ) with h | h
  · exact I_69 t h1 h
  · exact I_70 t h h2

lemma J_68_71 : ∀ t : ℝ, (977070059627 / 32000000000000 : ℝ) < t → t ≤ (127189819179 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (246289939597 / 8000000000000 : ℝ) with h | h
  · exact I_68 t h1 h
  · exact J_69_71 t h h2

lemma J_72_74 : ∀ t : ℝ, (516848975477 / 16000000000000 : ℝ) < t → t ≤ (6763975897 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (262469337119 / 8000000000000 : ℝ) with h | h
  · exact I_72 t h1 h
  · exact I_73 t h h2

lemma J_71_74 : ∀ t : ℝ, (127189819179 / 4000000000000 : ℝ) < t → t ≤ (6763975897 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (516848975477 / 16000000000000 : ℝ) with h | h
  · exact I_71 t h1 h
  · exact J_72_74 t h h2

lemma J_68_74 : ∀ t : ℝ, (977070059627 / 32000000000000 : ℝ) < t → t ≤ (6763975897 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (127189819179 / 4000000000000 : ℝ) with h | h
  · exact J_68_71 t h1 h
  · exact J_71_74 t h h2

lemma J_63_74 : ∀ t : ℝ, (468310782911 / 16000000000000 : ℝ) < t → t ≤ (6763975897 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (977070059627 / 32000000000000 : ℝ) with h | h
  · exact J_63_68 t h1 h
  · exact J_68_74 t h h2

lemma J_74_76 : ∀ t : ℝ, (6763975897 / 200000000000 : ℝ) < t → t ≤ (143369216701 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (278648734641 / 8000000000000 : ℝ) with h | h
  · exact I_74 t h1 h
  · exact I_75 t h h2

lemma J_77_79 : ∀ t : ℝ, (75729457731 / 2000000000000 : ℝ) < t → t ≤ (694494763253 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20954789123 / 500000000000 : ℝ) with h | h
  · exact I_77 t h1 h
  · exact I_78 t h h2

lemma J_76_79 : ∀ t : ℝ, (143369216701 / 4000000000000 : ℝ) < t → t ≤ (694494763253 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (75729457731 / 2000000000000 : ℝ) with h | h
  · exact I_76 t h1 h
  · exact J_77_79 t h h2

lemma J_74_79 : ∀ t : ℝ, (6763975897 / 200000000000 : ℝ) < t → t ≤ (694494763253 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (143369216701 / 4000000000000 : ℝ) with h | h
  · exact J_74_76 t h1 h
  · exact J_76_79 t h h2

lemma J_80_82 : ∀ t : ℝ, (1412931037823 / 32000000000000 : ℝ) < t → t ≤ (2897686609597 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (71843627457 / 1600000000000 : ℝ) with h | h
  · exact I_80 t h1 h
  · exact I_81 t h h2

lemma J_79_82 : ∀ t : ℝ, (694494763253 / 16000000000000 : ℝ) < t → t ≤ (2897686609597 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1412931037823 / 32000000000000 : ℝ) with h | h
  · exact I_79 t h1 h
  · exact J_80_82 t h h2

lemma J_83_85 : ∀ t : ℝ, (1460814060457 / 32000000000000 : ℝ) < t → t ≤ (742377785887 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2945569632231 / 64000000000000 : ℝ) with h | h
  · exact I_83 t h1 h
  · exact I_84 t h h2

lemma J_82_85 : ∀ t : ℝ, (2897686609597 / 64000000000000 : ℝ) < t → t ≤ (742377785887 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1460814060457 / 32000000000000 : ℝ) with h | h
  · exact I_82 t h1 h
  · exact J_83_85 t h h2

lemma J_79_85 : ∀ t : ℝ, (694494763253 / 16000000000000 : ℝ) < t → t ≤ (742377785887 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2897686609597 / 64000000000000 : ℝ) with h | h
  · exact J_79_82 t h1 h
  · exact J_82_85 t h h2

lemma J_74_85 : ∀ t : ℝ, (6763975897 / 200000000000 : ℝ) < t → t ≤ (742377785887 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (694494763253 / 16000000000000 : ℝ) with h | h
  · exact J_74_79 t h1 h
  · exact J_79_85 t h h2

lemma J_63_85 : ∀ t : ℝ, (468310782911 / 16000000000000 : ℝ) < t → t ≤ (742377785887 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (6763975897 / 200000000000 : ℝ) with h | h
  · exact J_63_74 t h1 h
  · exact J_74_85 t h h2

lemma J_42_85 : ∀ t : ℝ, (133117165709 / 8000000000000 : ℝ) < t → t ≤ (742377785887 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (468310782911 / 16000000000000 : ℝ) with h | h
  · exact J_42_63 t h1 h
  · exact J_63_85 t h h2

lemma J_0_85 : ∀ t : ℝ, (0 : ℝ) < t → t ≤ (742377785887 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (133117165709 / 8000000000000 : ℝ) with h | h
  · exact J_0_42 t h1 h
  · exact J_42_85 t h h2

lemma J_85_87 : ∀ t : ℝ, (742377785887 / 16000000000000 : ℝ) < t → t ≤ (1508697083091 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (598690530973 / 12800000000000 : ℝ) with h | h
  · exact I_85 t h1 h
  · exact I_86 t h h2

lemma J_88_90 : ∀ t : ℝ, (3041335677499 / 64000000000000 : ℝ) < t → t ≤ (3089218700133 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (191579824301 / 4000000000000 : ℝ) with h | h
  · exact I_88 t h1 h
  · exact I_89 t h h2

lemma J_87_90 : ∀ t : ℝ, (1508697083091 / 32000000000000 : ℝ) < t → t ≤ (3089218700133 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3041335677499 / 64000000000000 : ℝ) with h | h
  · exact I_87 t h1 h
  · exact J_88_90 t h h2

lemma J_85_90 : ∀ t : ℝ, (742377785887 / 16000000000000 : ℝ) < t → t ≤ (3089218700133 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1508697083091 / 32000000000000 : ℝ) with h | h
  · exact J_85_87 t h1 h
  · exact J_87_90 t h h2

lemma J_90_92 : ∀ t : ℝ, (3089218700133 / 64000000000000 : ℝ) < t → t ≤ (3137101722767 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (62263204229 / 1280000000000 : ℝ) with h | h
  · exact I_90 t h1 h
  · exact I_91 t h h2

lemma J_93_95 : ∀ t : ℝ, (790260808521 / 16000000000000 : ℝ) < t → t ≤ (1604463128359 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3184984745401 / 64000000000000 : ℝ) with h | h
  · exact I_93 t h1 h
  · exact I_94 t h h2

lemma J_92_95 : ∀ t : ℝ, (3137101722767 / 64000000000000 : ℝ) < t → t ≤ (1604463128359 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (790260808521 / 16000000000000 : ℝ) with h | h
  · exact I_92 t h1 h
  · exact J_93_95 t h h2

lemma J_90_95 : ∀ t : ℝ, (3089218700133 / 64000000000000 : ℝ) < t → t ≤ (1604463128359 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3137101722767 / 64000000000000 : ℝ) with h | h
  · exact J_90_92 t h1 h
  · exact J_92_95 t h h2

lemma J_85_95 : ∀ t : ℝ, (742377785887 / 16000000000000 : ℝ) < t → t ≤ (1604463128359 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3089218700133 / 64000000000000 : ℝ) with h | h
  · exact J_85_90 t h1 h
  · exact J_90_95 t h h2

lemma J_95_97 : ∀ t : ℝ, (1604463128359 / 32000000000000 : ℝ) < t → t ≤ (407101159919 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (646573553607 / 12800000000000 : ℝ) with h | h
  · exact I_95 t h1 h
  · exact I_96 t h h2

lemma J_98_100 : ∀ t : ℝ, (1652346150993 / 32000000000000 : ℝ) < t → t ≤ (1700229173627 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (167628766231 / 3200000000000 : ℝ) with h | h
  · exact I_98 t h1 h
  · exact I_99 t h h2

lemma J_97_100 : ∀ t : ℝ, (407101159919 / 8000000000000 : ℝ) < t → t ≤ (1700229173627 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1652346150993 / 32000000000000 : ℝ) with h | h
  · exact I_97 t h1 h
  · exact J_98_100 t h h2

lemma J_95_100 : ∀ t : ℝ, (1604463128359 / 32000000000000 : ℝ) < t → t ≤ (1700229173627 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (407101159919 / 8000000000000 : ℝ) with h | h
  · exact J_95_97 t h1 h
  · exact J_97_100 t h h2

lemma J_101_103 : ∀ t : ℝ, (107760667809 / 2000000000000 : ℝ) < t → t ≤ (454984182553 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (886026853789 / 16000000000000 : ℝ) with h | h
  · exact I_101 t h1 h
  · exact I_102 t h h2

lemma J_100_103 : ∀ t : ℝ, (1700229173627 / 32000000000000 : ℝ) < t → t ≤ (454984182553 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (107760667809 / 2000000000000 : ℝ) with h | h
  · exact I_100 t h1 h
  · exact J_101_103 t h h2

lemma J_104_106 : ∀ t : ℝ, (47892569387 / 800000000000 : ℝ) < t → t ≤ (65851089563 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (502867205187 / 8000000000000 : ℝ) with h | h
  · exact I_104 t h1 h
  · exact I_105 t h h2

lemma J_103_106 : ∀ t : ℝ, (454984182553 / 8000000000000 : ℝ) < t → t ≤ (65851089563 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (47892569387 / 800000000000 : ℝ) with h | h
  · exact I_103 t h1 h
  · exact J_104_106 t h h2

lemma J_100_106 : ∀ t : ℝ, (1700229173627 / 32000000000000 : ℝ) < t → t ≤ (65851089563 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (454984182553 / 8000000000000 : ℝ) with h | h
  · exact J_100_103 t h1 h
  · exact J_103_106 t h h2

lemma J_95_106 : ∀ t : ℝ, (1604463128359 / 32000000000000 : ℝ) < t → t ≤ (65851089563 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1700229173627 / 32000000000000 : ℝ) with h | h
  · exact J_95_100 t h1 h
  · exact J_100_106 t h h2

lemma J_85_106 : ∀ t : ℝ, (742377785887 / 16000000000000 : ℝ) < t → t ≤ (65851089563 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1604463128359 / 32000000000000 : ℝ) with h | h
  · exact J_85_95 t h1 h
  · exact J_95_106 t h h2

lemma J_106_108 : ∀ t : ℝ, (65851089563 / 1000000000000 : ℝ) < t → t ≤ (1087247381329 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2140864814337 / 32000000000000 : ℝ) with h | h
  · exact I_106 t h1 h
  · exact I_107 t h h2

lemma J_109_111 : ∀ t : ℝ, (2208124710979 / 32000000000000 : ℝ) < t → t ≤ (22417546593 / 320000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4449879370279 / 64000000000000 : ℝ) with h | h
  · exact I_109 t h1 h
  · exact I_110 t h h2

lemma J_108_111 : ∀ t : ℝ, (1087247381329 / 16000000000000 : ℝ) < t → t ≤ (22417546593 / 320000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2208124710979 / 32000000000000 : ℝ) with h | h
  · exact I_108 t h1 h
  · exact J_109_111 t h h2

lemma J_106_111 : ∀ t : ℝ, (65851089563 / 1000000000000 : ℝ) < t → t ≤ (22417546593 / 320000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1087247381329 / 16000000000000 : ℝ) with h | h
  · exact J_106_108 t h1 h
  · exact J_108_111 t h h2

lemma J_112_114 : ∀ t : ℝ, (4517139266921 / 64000000000000 : ℝ) < t → t ≤ (4584399163563 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2275384607621 / 32000000000000 : ℝ) with h | h
  · exact I_112 t h1 h
  · exact I_113 t h h2

lemma J_111_114 : ∀ t : ℝ, (22417546593 / 320000000000 : ℝ) < t → t ≤ (4584399163563 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4517139266921 / 64000000000000 : ℝ) with h | h
  · exact I_111 t h1 h
  · exact J_112_114 t h h2

lemma J_115_117 : ∀ t : ℝ, (1154507277971 / 16000000000000 : ℝ) < t → t ≤ (2342644504263 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (930331812041 / 12800000000000 : ℝ) with h | h
  · exact I_115 t h1 h
  · exact I_116 t h h2

lemma J_114_117 : ∀ t : ℝ, (4584399163563 / 64000000000000 : ℝ) < t → t ≤ (2342644504263 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1154507277971 / 16000000000000 : ℝ) with h | h
  · exact I_114 t h1 h
  · exact J_115_117 t h h2

lemma J_111_117 : ∀ t : ℝ, (22417546593 / 320000000000 : ℝ) < t → t ≤ (2342644504263 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4584399163563 / 64000000000000 : ℝ) with h | h
  · exact J_111_114 t h1 h
  · exact J_114_117 t h h2

lemma J_106_117 : ∀ t : ℝ, (65851089563 / 1000000000000 : ℝ) < t → t ≤ (2342644504263 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (22417546593 / 320000000000 : ℝ) with h | h
  · exact J_106_111 t h1 h
  · exact J_111_117 t h h2

lemma J_117_119 : ∀ t : ℝ, (2342644504263 / 32000000000000 : ℝ) < t → t ≤ (4718918956847 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9404207965373 / 128000000000000 : ℝ) with h | h
  · exact I_117 t h1 h
  · exact I_118 t h h2

lemma J_120_122 : ∀ t : ℝ, (1894293572403 / 25600000000000 : ℝ) < t → t ≤ (9538727758657 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (297034306573 / 4000000000000 : ℝ) with h | h
  · exact I_120 t h1 h
  · exact I_121 t h h2

lemma J_119_122 : ∀ t : ℝ, (4718918956847 / 64000000000000 : ℝ) < t → t ≤ (9538727758657 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1894293572403 / 25600000000000 : ℝ) with h | h
  · exact I_119 t h1 h
  · exact J_120_122 t h h2

lemma J_117_122 : ∀ t : ℝ, (2342644504263 / 32000000000000 : ℝ) < t → t ≤ (9538727758657 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4718918956847 / 64000000000000 : ℝ) with h | h
  · exact J_117_119 t h1 h
  · exact J_119_122 t h h2

lemma J_123_125 : ∀ t : ℝ, (4786178853489 / 64000000000000 : ℝ) < t → t ≤ (481980880181 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9605987655299 / 128000000000000 : ℝ) with h | h
  · exact I_123 t h1 h
  · exact I_124 t h h2

lemma J_122_125 : ∀ t : ℝ, (9538727758657 / 128000000000000 : ℝ) < t → t ≤ (481980880181 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4786178853489 / 64000000000000 : ℝ) with h | h
  · exact I_122 t h1 h
  · exact J_123_125 t h h2

lemma J_126_128 : ∀ t : ℝ, (9673247551941 / 128000000000000 : ℝ) < t → t ≤ (1221767174613 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4853438750131 / 64000000000000 : ℝ) with h | h
  · exact I_126 t h1 h
  · exact I_127 t h h2

lemma J_125_128 : ∀ t : ℝ, (481980880181 / 6400000000000 : ℝ) < t → t ≤ (1221767174613 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9673247551941 / 128000000000000 : ℝ) with h | h
  · exact I_125 t h1 h
  · exact J_126_128 t h h2

lemma J_122_128 : ∀ t : ℝ, (9538727758657 / 128000000000000 : ℝ) < t → t ≤ (1221767174613 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (481980880181 / 6400000000000 : ℝ) with h | h
  · exact J_122_125 t h1 h
  · exact J_125_128 t h h2

lemma J_117_128 : ∀ t : ℝ, (2342644504263 / 32000000000000 : ℝ) < t → t ≤ (1221767174613 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9538727758657 / 128000000000000 : ℝ) with h | h
  · exact J_117_122 t h1 h
  · exact J_122_128 t h h2

lemma J_106_128 : ∀ t : ℝ, (65851089563 / 1000000000000 : ℝ) < t → t ≤ (1221767174613 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2342644504263 / 32000000000000 : ℝ) with h | h
  · exact J_106_117 t h1 h
  · exact J_117_128 t h h2

lemma J_85_128 : ∀ t : ℝ, (742377785887 / 16000000000000 : ℝ) < t → t ≤ (1221767174613 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (65851089563 / 1000000000000 : ℝ) with h | h
  · exact J_85_106 t h1 h
  · exact J_106_128 t h h2

lemma J_128_130 : ∀ t : ℝ, (1221767174613 / 16000000000000 : ℝ) < t → t ≤ (2477164297547 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4920698646773 / 64000000000000 : ℝ) with h | h
  · exact I_128 t h1 h
  · exact I_129 t h h2

lemma J_131_133 : ∀ t : ℝ, (997591708683 / 12800000000000 : ℝ) < t → t ≤ (5055218440057 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (627698561467 / 8000000000000 : ℝ) with h | h
  · exact I_131 t h1 h
  · exact I_132 t h h2

lemma J_130_133 : ∀ t : ℝ, (2477164297547 / 32000000000000 : ℝ) < t → t ≤ (5055218440057 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (997591708683 / 12800000000000 : ℝ) with h | h
  · exact I_130 t h1 h
  · exact J_131_133 t h h2

lemma J_128_133 : ∀ t : ℝ, (1221767174613 / 16000000000000 : ℝ) < t → t ≤ (5055218440057 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2477164297547 / 32000000000000 : ℝ) with h | h
  · exact J_128_130 t h1 h
  · exact J_130_133 t h h2

lemma J_133_135 : ∀ t : ℝ, (5055218440057 / 64000000000000 : ℝ) < t → t ≤ (5122478336699 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2544424194189 / 32000000000000 : ℝ) with h | h
  · exact I_133 t h1 h
  · exact I_134 t h h2

lemma J_136_138 : ∀ t : ℝ, (257805414251 / 3200000000000 : ℝ) < t → t ≤ (165332127447 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2611684090831 / 32000000000000 : ℝ) with h | h
  · exact I_136 t h1 h
  · exact I_137 t h h2

lemma J_135_138 : ∀ t : ℝ, (5122478336699 / 64000000000000 : ℝ) < t → t ≤ (165332127447 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (257805414251 / 3200000000000 : ℝ) with h | h
  · exact I_135 t h1 h
  · exact J_136_138 t h h2

lemma J_133_138 : ∀ t : ℝ, (5055218440057 / 64000000000000 : ℝ) < t → t ≤ (165332127447 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5122478336699 / 64000000000000 : ℝ) with h | h
  · exact J_133_135 t h1 h
  · exact J_135_138 t h h2

lemma J_128_138 : ∀ t : ℝ, (1221767174613 / 16000000000000 : ℝ) < t → t ≤ (165332127447 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5055218440057 / 64000000000000 : ℝ) with h | h
  · exact J_128_133 t h1 h
  · exact J_133_138 t h h2

lemma J_138_140 : ∀ t : ℝ, (165332127447 / 2000000000000 : ℝ) < t → t ≤ (1356286967897 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2678943987473 / 32000000000000 : ℝ) with h | h
  · exact I_138 t h1 h
  · exact I_139 t h h2

lemma J_141_143 : ∀ t : ℝ, (694958458109 / 8000000000000 : ℝ) < t → t ≤ (72858840643 / 800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1423546864539 / 16000000000000 : ℝ) with h | h
  · exact I_141 t h1 h
  · exact I_142 t h h2

lemma J_140_143 : ∀ t : ℝ, (1356286967897 / 16000000000000 : ℝ) < t → t ≤ (72858840643 / 800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (694958458109 / 8000000000000 : ℝ) with h | h
  · exact I_140 t h1 h
  · exact J_141_143 t h h2

lemma J_138_143 : ∀ t : ℝ, (165332127447 / 2000000000000 : ℝ) < t → t ≤ (72858840643 / 800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1356286967897 / 16000000000000 : ℝ) with h | h
  · exact J_138_140 t h1 h
  · exact J_140_143 t h h2

lemma J_144_146 : ∀ t : ℝ, (762218354751 / 8000000000000 : ℝ) < t → t ≤ (1614118950931 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (24870259471 / 250000000000 : ℝ) with h | h
  · exact I_144 t h1 h
  · exact I_145 t h h2

lemma J_143_146 : ∀ t : ℝ, (72858840643 / 800000000000 : ℝ) < t → t ≤ (1614118950931 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (762218354751 / 8000000000000 : ℝ) with h | h
  · exact I_143 t h1 h
  · exact J_144_146 t h h2

lemma J_147_149 : ∀ t : ℝ, (818270647859 / 8000000000000 : ℝ) < t → t ≤ (3340349625797 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (331792728101 / 3200000000000 : ℝ) with h | h
  · exact I_147 t h1 h
  · exact I_148 t h h2

lemma J_146_149 : ∀ t : ℝ, (1614118950931 / 16000000000000 : ℝ) < t → t ≤ (3340349625797 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (818270647859 / 8000000000000 : ℝ) with h | h
  · exact I_146 t h1 h
  · exact J_147_149 t h h2

lemma J_143_149 : ∀ t : ℝ, (72858840643 / 800000000000 : ℝ) < t → t ≤ (3340349625797 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1614118950931 / 16000000000000 : ℝ) with h | h
  · exact J_143_146 t h1 h
  · exact J_146_149 t h h2

lemma J_138_149 : ∀ t : ℝ, (165332127447 / 2000000000000 : ℝ) < t → t ≤ (3340349625797 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (72858840643 / 800000000000 : ℝ) with h | h
  · exact J_138_143 t h1 h
  · exact J_143_149 t h h2

lemma J_128_149 : ∀ t : ℝ, (1221767174613 / 16000000000000 : ℝ) < t → t ≤ (3340349625797 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (165332127447 / 2000000000000 : ℝ) with h | h
  · exact J_128_138 t h1 h
  · exact J_138_149 t h h2

lemma J_149_151 : ∀ t : ℝ, (3340349625797 / 32000000000000 : ℝ) < t → t ≤ (3385194315371 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (420346496323 / 4000000000000 : ℝ) with h | h
  · exact I_149 t h1 h
  · exact I_150 t h h2

lemma J_152_154 : ∀ t : ℝ, (1703808330079 / 16000000000000 : ℝ) < t → t ≤ (863115337433 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (686007800989 / 6400000000000 : ℝ) with h | h
  · exact I_152 t h1 h
  · exact I_153 t h h2

lemma J_151_154 : ∀ t : ℝ, (3385194315371 / 32000000000000 : ℝ) < t → t ≤ (863115337433 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1703808330079 / 16000000000000 : ℝ) with h | h
  · exact I_151 t h1 h
  · exact J_152_154 t h h2

lemma J_149_154 : ∀ t : ℝ, (3340349625797 / 32000000000000 : ℝ) < t → t ≤ (863115337433 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3385194315371 / 32000000000000 : ℝ) with h | h
  · exact J_149_151 t h1 h
  · exact J_151_154 t h h2

lemma J_155_157 : ∀ t : ℝ, (6927345044251 / 64000000000000 : ℝ) < t → t ≤ (278887589353 / 2560000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3474883694519 / 32000000000000 : ℝ) with h | h
  · exact I_155 t h1 h
  · exact I_156 t h h2

lemma J_154_157 : ∀ t : ℝ, (863115337433 / 8000000000000 : ℝ) < t → t ≤ (278887589353 / 2560000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (6927345044251 / 64000000000000 : ℝ) with h | h
  · exact I_154 t h1 h
  · exact J_155_157 t h h2

lemma J_158_160 : ∀ t : ℝ, (1748653019653 / 16000000000000 : ℝ) < t → t ≤ (3519728384093 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7017034423399 / 64000000000000 : ℝ) with h | h
  · exact I_158 t h1 h
  · exact I_159 t h h2

lemma J_157_160 : ∀ t : ℝ, (278887589353 / 2560000000000 : ℝ) < t → t ≤ (3519728384093 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1748653019653 / 16000000000000 : ℝ) with h | h
  · exact I_157 t h1 h
  · exact J_158_160 t h h2

lemma J_154_160 : ∀ t : ℝ, (863115337433 / 8000000000000 : ℝ) < t → t ≤ (3519728384093 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (278887589353 / 2560000000000 : ℝ) with h | h
  · exact J_154_157 t h1 h
  · exact J_157_160 t h h2

lemma J_149_160 : ∀ t : ℝ, (3340349625797 / 32000000000000 : ℝ) < t → t ≤ (3519728384093 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (863115337433 / 8000000000000 : ℝ) with h | h
  · exact J_149_154 t h1 h
  · exact J_154_160 t h h2

lemma J_160_162 : ∀ t : ℝ, (3519728384093 / 32000000000000 : ℝ) < t → t ≤ (44276884111 / 400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7061879112973 / 64000000000000 : ℝ) with h | h
  · exact I_160 t h1 h
  · exact I_161 t h h2

lemma J_163_165 : ∀ t : ℝ, (7106723802547 / 64000000000000 : ℝ) < t → t ≤ (7151568492121 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3564573073667 / 32000000000000 : ℝ) with h | h
  · exact I_163 t h1 h
  · exact I_164 t h h2

lemma J_162_165 : ∀ t : ℝ, (44276884111 / 400000000000 : ℝ) < t → t ≤ (7151568492121 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7106723802547 / 64000000000000 : ℝ) with h | h
  · exact I_162 t h1 h
  · exact J_163_165 t h h2

lemma J_160_165 : ∀ t : ℝ, (3519728384093 / 32000000000000 : ℝ) < t → t ≤ (7151568492121 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (44276884111 / 400000000000 : ℝ) with h | h
  · exact J_160_162 t h1 h
  · exact J_162_165 t h h2

lemma J_166_168 : ∀ t : ℝ, (1793497709227 / 16000000000000 : ℝ) < t → t ≤ (3609417763241 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1439282636339 / 12800000000000 : ℝ) with h | h
  · exact I_166 t h1 h
  · exact I_167 t h h2

lemma J_165_168 : ∀ t : ℝ, (7151568492121 / 64000000000000 : ℝ) < t → t ≤ (3609417763241 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1793497709227 / 16000000000000 : ℝ) with h | h
  · exact I_165 t h1 h
  · exact J_166_168 t h h2

lemma J_169_171 : ∀ t : ℝ, (7241257871269 / 64000000000000 : ℝ) < t → t ≤ (7286102560843 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (907960027007 / 8000000000000 : ℝ) with h | h
  · exact I_169 t h1 h
  · exact I_170 t h h2

lemma J_168_171 : ∀ t : ℝ, (3609417763241 / 32000000000000 : ℝ) < t → t ≤ (7286102560843 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7241257871269 / 64000000000000 : ℝ) with h | h
  · exact I_168 t h1 h
  · exact J_169_171 t h h2

lemma J_165_171 : ∀ t : ℝ, (7151568492121 / 64000000000000 : ℝ) < t → t ≤ (7286102560843 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3609417763241 / 32000000000000 : ℝ) with h | h
  · exact J_165_168 t h1 h
  · exact J_168_171 t h h2

lemma J_160_171 : ∀ t : ℝ, (3519728384093 / 32000000000000 : ℝ) < t → t ≤ (7286102560843 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7151568492121 / 64000000000000 : ℝ) with h | h
  · exact J_160_165 t h1 h
  · exact J_165_171 t h h2

lemma J_149_171 : ∀ t : ℝ, (3340349625797 / 32000000000000 : ℝ) < t → t ≤ (7286102560843 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3519728384093 / 32000000000000 : ℝ) with h | h
  · exact J_149_160 t h1 h
  · exact J_160_171 t h h2

lemma J_128_171 : ∀ t : ℝ, (1221767174613 / 16000000000000 : ℝ) < t → t ≤ (7286102560843 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3340349625797 / 32000000000000 : ℝ) with h | h
  · exact J_128_149 t h1 h
  · exact J_149_171 t h h2

lemma J_85_171 : ∀ t : ℝ, (742377785887 / 16000000000000 : ℝ) < t → t ≤ (7286102560843 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1221767174613 / 16000000000000 : ℝ) with h | h
  · exact J_85_128 t h1 h
  · exact J_128_171 t h h2

lemma J_0_171 : ∀ t : ℝ, (0 : ℝ) < t → t ≤ (7286102560843 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (742377785887 / 16000000000000 : ℝ) with h | h
  · exact J_0_85 t h1 h
  · exact J_85_171 t h h2

lemma J_171_173 : ∀ t : ℝ, (7286102560843 / 64000000000000 : ℝ) < t → t ≤ (7330947250417 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (730852490563 / 6400000000000 : ℝ) with h | h
  · exact I_171 t h1 h
  · exact I_172 t h h2

lemma J_174_176 : ∀ t : ℝ, (1838342398801 / 16000000000000 : ℝ) < t → t ≤ (465191185897 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3699107142389 / 32000000000000 : ℝ) with h | h
  · exact I_174 t h1 h
  · exact I_175 t h h2

lemma J_173_176 : ∀ t : ℝ, (7330947250417 / 64000000000000 : ℝ) < t → t ≤ (465191185897 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1838342398801 / 16000000000000 : ℝ) with h | h
  · exact I_173 t h1 h
  · exact J_174_176 t h h2

lemma J_171_176 : ∀ t : ℝ, (7286102560843 / 64000000000000 : ℝ) < t → t ≤ (465191185897 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7330947250417 / 64000000000000 : ℝ) with h | h
  · exact J_171_173 t h1 h
  · exact J_173_176 t h h2

lemma J_176_178 : ∀ t : ℝ, (465191185897 / 4000000000000 : ℝ) < t → t ≤ (15065496707 / 128000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3743951831963 / 32000000000000 : ℝ) with h | h
  · exact I_176 t h1 h
  · exact I_177 t h h2

lemma J_179_181 : ∀ t : ℝ, (3788796521537 / 32000000000000 : ℝ) < t → t ≤ (3833641211111 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (952804716581 / 8000000000000 : ℝ) with h | h
  · exact I_179 t h1 h
  · exact I_180 t h h2

lemma J_178_181 : ∀ t : ℝ, (15065496707 / 128000000000 : ℝ) < t → t ≤ (3833641211111 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3788796521537 / 32000000000000 : ℝ) with h | h
  · exact I_178 t h1 h
  · exact J_179_181 t h h2

lemma J_176_181 : ∀ t : ℝ, (465191185897 / 4000000000000 : ℝ) < t → t ≤ (3833641211111 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (15065496707 / 128000000000 : ℝ) with h | h
  · exact J_176_178 t h1 h
  · exact J_178_181 t h h2

lemma J_171_181 : ∀ t : ℝ, (7286102560843 / 64000000000000 : ℝ) < t → t ≤ (3833641211111 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (465191185897 / 4000000000000 : ℝ) with h | h
  · exact J_171_176 t h1 h
  · exact J_176_181 t h h2

lemma J_181_183 : ∀ t : ℝ, (3833641211111 / 32000000000000 : ℝ) < t → t ≤ (121903382671 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1928031777949 / 16000000000000 : ℝ) with h | h
  · exact I_181 t h1 h
  · exact I_182 t h h2

lemma J_184_186 : ∀ t : ℝ, (1972876467523 / 16000000000000 : ℝ) < t → t ≤ (2017721157097 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (199529881231 / 1600000000000 : ℝ) with h | h
  · exact I_184 t h1 h
  · exact I_185 t h h2

lemma J_183_186 : ∀ t : ℝ, (121903382671 / 1000000000000 : ℝ) < t → t ≤ (2017721157097 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1972876467523 / 16000000000000 : ℝ) with h | h
  · exact I_183 t h1 h
  · exact J_184_186 t h h2

lemma J_181_186 : ∀ t : ℝ, (3833641211111 / 32000000000000 : ℝ) < t → t ≤ (2017721157097 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (121903382671 / 1000000000000 : ℝ) with h | h
  · exact J_181_183 t h1 h
  · exact J_183_186 t h h2

lemma J_187_189 : ∀ t : ℝ, (510035875471 / 4000000000000 : ℝ) < t → t ≤ (266229110129 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1042494095729 / 8000000000000 : ℝ) with h | h
  · exact I_187 t h1 h
  · exact I_188 t h h2

lemma J_186_189 : ∀ t : ℝ, (2017721157097 / 16000000000000 : ℝ) < t → t ≤ (266229110129 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (510035875471 / 4000000000000 : ℝ) with h | h
  · exact I_186 t h1 h
  · exact J_187_189 t h h2

lemma J_190_192 : ∀ t : ℝ, (110976113009 / 800000000000 : ℝ) < t → t ≤ (4675203313927 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (72162863729 / 500000000000 : ℝ) with h | h
  · exact I_190 t h1 h
  · exact I_191 t h h2

lemma J_189_192 : ∀ t : ℝ, (266229110129 / 2000000000000 : ℝ) < t → t ≤ (4675203313927 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (110976113009 / 800000000000 : ℝ) with h | h
  · exact I_189 t h1 h
  · exact J_190_192 t h h2

lemma J_186_192 : ∀ t : ℝ, (2017721157097 / 16000000000000 : ℝ) < t → t ≤ (4675203313927 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (266229110129 / 2000000000000 : ℝ) with h | h
  · exact J_186_189 t h1 h
  · exact J_189_192 t h h2

lemma J_181_192 : ∀ t : ℝ, (3833641211111 / 32000000000000 : ℝ) < t → t ≤ (4675203313927 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2017721157097 / 16000000000000 : ℝ) with h | h
  · exact J_181_186 t h1 h
  · exact J_186_192 t h h2

lemma J_171_192 : ∀ t : ℝ, (7286102560843 / 64000000000000 : ℝ) < t → t ≤ (4675203313927 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3833641211111 / 32000000000000 : ℝ) with h | h
  · exact J_171_181 t h1 h
  · exact J_181_192 t h h2

lemma J_192_194 : ∀ t : ℝ, (4675203313927 / 32000000000000 : ℝ) < t → t ≤ (4788763384469 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2365991674599 / 16000000000000 : ℝ) with h | h
  · exact I_192 t h1 h
  · exact I_193 t h h2

lemma J_195_197 : ∀ t : ℝ, (9634306804209 / 64000000000000 : ℝ) < t → t ≤ (9747866874751 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (242277170987 / 1600000000000 : ℝ) with h | h
  · exact I_195 t h1 h
  · exact I_196 t h h2

lemma J_194_197 : ∀ t : ℝ, (4788763384469 / 32000000000000 : ℝ) < t → t ≤ (9747866874751 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9634306804209 / 64000000000000 : ℝ) with h | h
  · exact I_194 t h1 h
  · exact J_195_197 t h h2

lemma J_192_197 : ∀ t : ℝ, (4675203313927 / 32000000000000 : ℝ) < t → t ≤ (9747866874751 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4788763384469 / 32000000000000 : ℝ) with h | h
  · exact J_192_194 t h1 h
  · exact J_194_197 t h h2

lemma J_197_199 : ∀ t : ℝ, (9747866874751 / 64000000000000 : ℝ) < t → t ≤ (9861426945293 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4902323455011 / 32000000000000 : ℝ) with h | h
  · exact I_197 t h1 h
  · exact I_198 t h h2

lemma J_200_202 : ∀ t : ℝ, (2479551745141 / 16000000000000 : ℝ) < t → t ≤ (1994997403167 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19893193996399 / 128000000000000 : ℝ) with h | h
  · exact I_200 t h1 h
  · exact I_201 t h h2

lemma J_199_202 : ∀ t : ℝ, (9861426945293 / 64000000000000 : ℝ) < t → t ≤ (1994997403167 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2479551745141 / 16000000000000 : ℝ) with h | h
  · exact I_199 t h1 h
  · exact J_200_202 t h h2

lemma J_197_202 : ∀ t : ℝ, (9747866874751 / 64000000000000 : ℝ) < t → t ≤ (1994997403167 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9861426945293 / 64000000000000 : ℝ) with h | h
  · exact J_197_199 t h1 h
  · exact J_199_202 t h h2

lemma J_192_202 : ∀ t : ℝ, (4675203313927 / 32000000000000 : ℝ) < t → t ≤ (1994997403167 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9747866874751 / 64000000000000 : ℝ) with h | h
  · exact J_192_197 t h1 h
  · exact J_197_202 t h h2

lemma J_202_204 : ∀ t : ℝ, (1994997403167 / 12800000000000 : ℝ) < t → t ≤ (5015883525553 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20006754066941 / 128000000000000 : ℝ) with h | h
  · exact I_202 t h1 h
  · exact I_203 t h h2

lemma J_205_207 : ∀ t : ℝ, (20120314137483 / 128000000000000 : ℝ) < t → t ≤ (809354968321 / 5120000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10088547086377 / 64000000000000 : ℝ) with h | h
  · exact I_205 t h1 h
  · exact I_206 t h h2

lemma J_204_207 : ∀ t : ℝ, (5015883525553 / 32000000000000 : ℝ) < t → t ≤ (809354968321 / 5120000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20120314137483 / 128000000000000 : ℝ) with h | h
  · exact I_204 t h1 h
  · exact J_205_207 t h h2

lemma J_202_207 : ∀ t : ℝ, (1994997403167 / 12800000000000 : ℝ) < t → t ≤ (809354968321 / 5120000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5015883525553 / 32000000000000 : ℝ) with h | h
  · exact J_202_204 t h1 h
  · exact J_204_207 t h h2

lemma J_208_210 : ∀ t : ℝ, (634082945103 / 4000000000000 : ℝ) < t → t ≤ (10202107156919 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20347434278567 / 128000000000000 : ℝ) with h | h
  · exact I_208 t h1 h
  · exact I_209 t h h2

lemma J_207_210 : ∀ t : ℝ, (809354968321 / 5120000000000 : ℝ) < t → t ≤ (10202107156919 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (634082945103 / 4000000000000 : ℝ) with h | h
  · exact I_207 t h1 h
  · exact J_208_210 t h h2

lemma J_211_213 : ∀ t : ℝ, (20460994349109 / 128000000000000 : ℝ) < t → t ≤ (20574554419651 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1025888719219 / 6400000000000 : ℝ) with h | h
  · exact I_211 t h1 h
  · exact I_212 t h h2

lemma J_210_213 : ∀ t : ℝ, (10202107156919 / 64000000000000 : ℝ) < t → t ≤ (20574554419651 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20460994349109 / 128000000000000 : ℝ) with h | h
  · exact I_210 t h1 h
  · exact J_211_213 t h h2

lemma J_207_213 : ∀ t : ℝ, (809354968321 / 5120000000000 : ℝ) < t → t ≤ (20574554419651 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10202107156919 / 64000000000000 : ℝ) with h | h
  · exact J_207_210 t h1 h
  · exact J_210_213 t h h2

lemma J_202_213 : ∀ t : ℝ, (1994997403167 / 12800000000000 : ℝ) < t → t ≤ (20574554419651 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (809354968321 / 5120000000000 : ℝ) with h | h
  · exact J_202_207 t h1 h
  · exact J_207_213 t h h2

lemma J_192_213 : ∀ t : ℝ, (4675203313927 / 32000000000000 : ℝ) < t → t ≤ (20574554419651 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1994997403167 / 12800000000000 : ℝ) with h | h
  · exact J_192_202 t h1 h
  · exact J_202_213 t h h2

lemma J_171_213 : ∀ t : ℝ, (7286102560843 / 64000000000000 : ℝ) < t → t ≤ (20574554419651 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4675203313927 / 32000000000000 : ℝ) with h | h
  · exact J_171_192 t h1 h
  · exact J_192_213 t h h2

lemma J_213_215 : ∀ t : ℝ, (20574554419651 / 128000000000000 : ℝ) < t → t ≤ (20688114490193 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10315667227461 / 64000000000000 : ℝ) with h | h
  · exact I_213 t h1 h
  · exact I_214 t h h2

lemma J_216_218 : ∀ t : ℝ, (2593111815683 / 16000000000000 : ℝ) < t → t ≤ (10429227298003 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4160334912147 / 25600000000000 : ℝ) with h | h
  · exact I_216 t h1 h
  · exact I_217 t h h2

lemma J_215_218 : ∀ t : ℝ, (20688114490193 / 128000000000000 : ℝ) < t → t ≤ (10429227298003 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2593111815683 / 16000000000000 : ℝ) with h | h
  · exact I_215 t h1 h
  · exact J_216_218 t h h2

lemma J_213_218 : ∀ t : ℝ, (20574554419651 / 128000000000000 : ℝ) < t → t ≤ (10429227298003 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20688114490193 / 128000000000000 : ℝ) with h | h
  · exact J_213_215 t h1 h
  · exact J_215_218 t h h2

lemma J_218_220 : ∀ t : ℝ, (10429227298003 / 64000000000000 : ℝ) < t → t ≤ (5243003666637 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20915234631277 / 128000000000000 : ℝ) with h | h
  · exact I_218 t h1 h
  · exact I_219 t h h2

lemma J_221_223 : ∀ t : ℝ, (21028794701819 / 128000000000000 : ℝ) < t → t ≤ (21142354772361 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2108557473709 / 12800000000000 : ℝ) with h | h
  · exact I_221 t h1 h
  · exact I_222 t h h2

lemma J_220_223 : ∀ t : ℝ, (5243003666637 / 32000000000000 : ℝ) < t → t ≤ (21142354772361 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (21028794701819 / 128000000000000 : ℝ) with h | h
  · exact I_220 t h1 h
  · exact J_221_223 t h h2

lemma J_218_223 : ∀ t : ℝ, (10429227298003 / 64000000000000 : ℝ) < t → t ≤ (21142354772361 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5243003666637 / 32000000000000 : ℝ) with h | h
  · exact J_218_220 t h1 h
  · exact J_220_223 t h h2

lemma J_213_223 : ∀ t : ℝ, (20574554419651 / 128000000000000 : ℝ) < t → t ≤ (21142354772361 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10429227298003 / 64000000000000 : ℝ) with h | h
  · exact J_213_218 t h1 h
  · exact J_218_223 t h h2

lemma J_223_225 : ∀ t : ℝ, (21142354772361 / 128000000000000 : ℝ) < t → t ≤ (10656347439087 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1324945925477 / 8000000000000 : ℝ) with h | h
  · exact I_223 t h1 h
  · exact I_224 t h h2

lemma J_226_228 : ∀ t : ℝ, (5356563737179 / 32000000000000 : ℝ) < t → t ≤ (108266875449 / 640000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10769907509629 / 64000000000000 : ℝ) with h | h
  · exact I_226 t h1 h
  · exact I_227 t h h2

lemma J_225_228 : ∀ t : ℝ, (10656347439087 / 64000000000000 : ℝ) < t → t ≤ (108266875449 / 640000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5356563737179 / 32000000000000 : ℝ) with h | h
  · exact I_225 t h1 h
  · exact J_226_228 t h h2

lemma J_223_228 : ∀ t : ℝ, (21142354772361 / 128000000000000 : ℝ) < t → t ≤ (108266875449 / 640000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10656347439087 / 64000000000000 : ℝ) with h | h
  · exact J_223_225 t h1 h
  · exact J_225_228 t h h2

lemma J_229_231 : ∀ t : ℝ, (10883467580171 / 64000000000000 : ℝ) < t → t ≤ (10997027650713 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5470123807721 / 32000000000000 : ℝ) with h | h
  · exact I_229 t h1 h
  · exact I_230 t h h2

lemma J_228_231 : ∀ t : ℝ, (108266875449 / 640000000000 : ℝ) < t → t ≤ (10997027650713 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10883467580171 / 64000000000000 : ℝ) with h | h
  · exact I_228 t h1 h
  · exact J_229_231 t h h2

lemma J_232_234 : ∀ t : ℝ, (345431490187 / 2000000000000 : ℝ) < t → t ≤ (2820231956767 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5583683878263 / 32000000000000 : ℝ) with h | h
  · exact I_232 t h1 h
  · exact I_233 t h h2

lemma J_231_234 : ∀ t : ℝ, (10997027650713 / 64000000000000 : ℝ) < t → t ≤ (2820231956767 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (345431490187 / 2000000000000 : ℝ) with h | h
  · exact I_231 t h1 h
  · exact J_232_234 t h h2

lemma J_228_234 : ∀ t : ℝ, (108266875449 / 640000000000 : ℝ) < t → t ≤ (2820231956767 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10997027650713 / 64000000000000 : ℝ) with h | h
  · exact J_228_231 t h1 h
  · exact J_231_234 t h h2

lemma J_223_234 : ∀ t : ℝ, (21142354772361 / 128000000000000 : ℝ) < t → t ≤ (2820231956767 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (108266875449 / 640000000000 : ℝ) with h | h
  · exact J_223_228 t h1 h
  · exact J_228_234 t h h2

lemma J_213_234 : ∀ t : ℝ, (20574554419651 / 128000000000000 : ℝ) < t → t ≤ (2820231956767 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (21142354772361 / 128000000000000 : ℝ) with h | h
  · exact J_213_223 t h1 h
  · exact J_223_234 t h h2

lemma J_234_236 : ∀ t : ℝ, (2820231956767 / 16000000000000 : ℝ) < t → t ≤ (1438505996019 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1139448789761 / 6400000000000 : ℝ) with h | h
  · exact I_234 t h1 h
  · exact I_235 t h h2

lemma J_237_239 : ∀ t : ℝ, (2933792027309 / 16000000000000 : ℝ) < t → t ≤ (3047352097851 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (149528603129 / 800000000000 : ℝ) with h | h
  · exact I_237 t h1 h
  · exact I_238 t h h2

lemma J_236_239 : ∀ t : ℝ, (1438505996019 / 8000000000000 : ℝ) < t → t ≤ (3047352097851 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2933792027309 / 16000000000000 : ℝ) with h | h
  · exact I_236 t h1 h
  · exact J_237_239 t h h2

lemma J_234_239 : ∀ t : ℝ, (2820231956767 / 16000000000000 : ℝ) < t → t ≤ (3047352097851 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1438505996019 / 8000000000000 : ℝ) with h | h
  · exact J_234_236 t h1 h
  · exact J_236_239 t h h2

lemma J_240_242 : ∀ t : ℝ, (1552066066561 / 8000000000000 : ℝ) < t → t ≤ (3251812320751 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (201105762729 / 1000000000000 : ℝ) with h | h
  · exact I_240 t h1 h
  · exact I_241 t h h2

lemma J_239_242 : ∀ t : ℝ, (3047352097851 / 16000000000000 : ℝ) < t → t ≤ (3251812320751 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1552066066561 / 8000000000000 : ℝ) with h | h
  · exact I_239 t h1 h
  · exact J_240_242 t h h2

lemma J_243_245 : ∀ t : ℝ, (1642966218919 / 8000000000000 : ℝ) < t → t ≤ (6674225226937 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (132802102197 / 640000000000 : ℝ) with h | h
  · exact I_243 t h1 h
  · exact I_244 t h h2

lemma J_242_245 : ∀ t : ℝ, (3251812320751 / 16000000000000 : ℝ) < t → t ≤ (6674225226937 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1642966218919 / 8000000000000 : ℝ) with h | h
  · exact I_242 t h1 h
  · exact J_243_245 t h h2

lemma J_239_245 : ∀ t : ℝ, (3047352097851 / 16000000000000 : ℝ) < t → t ≤ (6674225226937 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3251812320751 / 16000000000000 : ℝ) with h | h
  · exact J_239_242 t h1 h
  · exact J_242_245 t h h2

lemma J_234_245 : ∀ t : ℝ, (2820231956767 / 16000000000000 : ℝ) < t → t ≤ (6674225226937 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3047352097851 / 16000000000000 : ℝ) with h | h
  · exact J_234_239 t h1 h
  · exact J_239_245 t h h2

lemma J_245_247 : ∀ t : ℝ, (6674225226937 / 32000000000000 : ℝ) < t → t ≤ (6742465461111 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (838543168003 / 4000000000000 : ℝ) with h | h
  · exact I_245 t h1 h
  · exact I_246 t h h2

lemma J_248_250 : ∀ t : ℝ, (3388292789099 / 16000000000000 : ℝ) < t → t ≤ (1711206453093 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1362141139057 / 6400000000000 : ℝ) with h | h
  · exact I_248 t h1 h
  · exact I_249 t h h2

lemma J_247_250 : ∀ t : ℝ, (6742465461111 / 32000000000000 : ℝ) < t → t ≤ (1711206453093 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3388292789099 / 16000000000000 : ℝ) with h | h
  · exact I_247 t h1 h
  · exact J_248_250 t h h2

lemma J_245_250 : ∀ t : ℝ, (6674225226937 / 32000000000000 : ℝ) < t → t ≤ (1711206453093 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (6742465461111 / 32000000000000 : ℝ) with h | h
  · exact J_245_247 t h1 h
  · exact J_247_250 t h h2

lemma J_251_253 : ∀ t : ℝ, (13723771741831 / 64000000000000 : ℝ) < t → t ≤ (2758402395201 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (6878945929459 / 32000000000000 : ℝ) with h | h
  · exact I_251 t h1 h
  · exact I_252 t h h2

lemma J_250_253 : ∀ t : ℝ, (1711206453093 / 8000000000000 : ℝ) < t → t ≤ (2758402395201 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (13723771741831 / 64000000000000 : ℝ) with h | h
  · exact I_250 t h1 h
  · exact J_251_253 t h h2

lemma J_254_256 : ∀ t : ℝ, (3456533023273 / 16000000000000 : ℝ) < t → t ≤ (6947186163633 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (13860252210179 / 64000000000000 : ℝ) with h | h
  · exact I_254 t h1 h
  · exact I_255 t h h2

lemma J_253_256 : ∀ t : ℝ, (2758402395201 / 12800000000000 : ℝ) < t → t ≤ (6947186163633 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3456533023273 / 16000000000000 : ℝ) with h | h
  · exact I_253 t h1 h
  · exact J_254_256 t h h2

lemma J_250_256 : ∀ t : ℝ, (1711206453093 / 8000000000000 : ℝ) < t → t ≤ (6947186163633 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2758402395201 / 12800000000000 : ℝ) with h | h
  · exact J_250_253 t h1 h
  · exact J_253_256 t h h2

lemma J_245_256 : ∀ t : ℝ, (6674225226937 / 32000000000000 : ℝ) < t → t ≤ (6947186163633 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1711206453093 / 8000000000000 : ℝ) with h | h
  · exact J_245_250 t h1 h
  · exact J_250_256 t h h2

lemma J_234_256 : ∀ t : ℝ, (2820231956767 / 16000000000000 : ℝ) < t → t ≤ (6947186163633 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (6674225226937 / 32000000000000 : ℝ) with h | h
  · exact J_234_245 t h1 h
  · exact J_245_256 t h h2

lemma J_213_256 : ∀ t : ℝ, (20574554419651 / 128000000000000 : ℝ) < t → t ≤ (6947186163633 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2820231956767 / 16000000000000 : ℝ) with h | h
  · exact J_213_234 t h1 h
  · exact J_234_256 t h h2

lemma J_171_256 : ∀ t : ℝ, (7286102560843 / 64000000000000 : ℝ) < t → t ≤ (6947186163633 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20574554419651 / 128000000000000 : ℝ) with h | h
  · exact J_171_213 t h1 h
  · exact J_213_256 t h h2

lemma J_256_258 : ∀ t : ℝ, (6947186163633 / 32000000000000 : ℝ) < t → t ≤ (87266328509 / 400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (13928492444353 / 64000000000000 : ℝ) with h | h
  · exact I_256 t h1 h
  · exact I_257 t h h2

lemma J_259_261 : ∀ t : ℝ, (13996732678527 / 64000000000000 : ℝ) < t → t ≤ (14064972912701 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7015426397807 / 32000000000000 : ℝ) with h | h
  · exact I_259 t h1 h
  · exact I_260 t h h2

lemma J_258_261 : ∀ t : ℝ, (87266328509 / 400000000000 : ℝ) < t → t ≤ (14064972912701 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (13996732678527 / 64000000000000 : ℝ) with h | h
  · exact I_258 t h1 h
  · exact J_259_261 t h h2

lemma J_256_261 : ∀ t : ℝ, (6947186163633 / 32000000000000 : ℝ) < t → t ≤ (14064972912701 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (87266328509 / 400000000000 : ℝ) with h | h
  · exact J_256_258 t h1 h
  · exact J_258_261 t h h2

lemma J_261_263 : ∀ t : ℝ, (14064972912701 / 64000000000000 : ℝ) < t → t ≤ (4522628207 / 20480000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3524773257447 / 16000000000000 : ℝ) with h | h
  · exact I_261 t h1 h
  · exact I_262 t h h2

lemma J_264_266 : ∀ t : ℝ, (7083666631981 / 32000000000000 : ℝ) < t → t ≤ (1779446687267 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (14201453381049 / 64000000000000 : ℝ) with h | h
  · exact I_264 t h1 h
  · exact I_265 t h h2

lemma J_263_266 : ∀ t : ℝ, (4522628207 / 20480000000 : ℝ) < t → t ≤ (1779446687267 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7083666631981 / 32000000000000 : ℝ) with h | h
  · exact I_263 t h1 h
  · exact J_264_266 t h h2

lemma J_261_266 : ∀ t : ℝ, (14064972912701 / 64000000000000 : ℝ) < t → t ≤ (1779446687267 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4522628207 / 20480000000 : ℝ) with h | h
  · exact J_261_263 t h1 h
  · exact J_263_266 t h h2

lemma J_256_266 : ∀ t : ℝ, (6947186163633 / 32000000000000 : ℝ) < t → t ≤ (1779446687267 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (14064972912701 / 64000000000000 : ℝ) with h | h
  · exact J_256_261 t h1 h
  · exact J_261_266 t h h2

lemma J_266_268 : ∀ t : ℝ, (1779446687267 / 8000000000000 : ℝ) < t → t ≤ (1430381373231 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (14269693615223 / 64000000000000 : ℝ) with h | h
  · exact I_266 t h1 h
  · exact I_267 t h h2

lemma J_269_271 : ∀ t : ℝ, (14337933849397 / 64000000000000 : ℝ) < t → t ≤ (14406174083571 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3593013491621 / 16000000000000 : ℝ) with h | h
  · exact I_269 t h1 h
  · exact I_270 t h h2

lemma J_268_271 : ∀ t : ℝ, (1430381373231 / 6400000000000 : ℝ) < t → t ≤ (14406174083571 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (14337933849397 / 64000000000000 : ℝ) with h | h
  · exact I_268 t h1 h
  · exact J_269_271 t h h2

lemma J_266_271 : ∀ t : ℝ, (1779446687267 / 8000000000000 : ℝ) < t → t ≤ (14406174083571 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1430381373231 / 6400000000000 : ℝ) with h | h
  · exact J_266_268 t h1 h
  · exact J_268_271 t h h2

lemma J_272_274 : ∀ t : ℝ, (7220147100329 / 32000000000000 : ℝ) < t → t ≤ (906783402177 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2894882863549 / 12800000000000 : ℝ) with h | h
  · exact I_272 t h1 h
  · exact I_273 t h h2

lemma J_271_274 : ∀ t : ℝ, (14406174083571 / 64000000000000 : ℝ) < t → t ≤ (906783402177 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7220147100329 / 32000000000000 : ℝ) with h | h
  · exact I_271 t h1 h
  · exact J_272_274 t h h2

lemma J_275_277 : ∀ t : ℝ, (14542654551919 / 64000000000000 : ℝ) < t → t ≤ (732250745159 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7288387334503 / 32000000000000 : ℝ) with h | h
  · exact I_275 t h1 h
  · exact I_276 t h h2

lemma J_274_277 : ∀ t : ℝ, (906783402177 / 4000000000000 : ℝ) < t → t ≤ (732250745159 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (14542654551919 / 64000000000000 : ℝ) with h | h
  · exact I_274 t h1 h
  · exact J_275_277 t h h2

lemma J_271_277 : ∀ t : ℝ, (14406174083571 / 64000000000000 : ℝ) < t → t ≤ (732250745159 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (906783402177 / 4000000000000 : ℝ) with h | h
  · exact J_271_274 t h1 h
  · exact J_274_277 t h h2

lemma J_266_277 : ∀ t : ℝ, (1779446687267 / 8000000000000 : ℝ) < t → t ≤ (732250745159 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (14406174083571 / 64000000000000 : ℝ) with h | h
  · exact J_266_271 t h1 h
  · exact J_271_277 t h h2

lemma J_256_277 : ∀ t : ℝ, (6947186163633 / 32000000000000 : ℝ) < t → t ≤ (732250745159 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1779446687267 / 8000000000000 : ℝ) with h | h
  · exact J_256_266 t h1 h
  · exact J_266_277 t h h2

lemma J_277_279 : ∀ t : ℝ, (732250745159 / 3200000000000 : ℝ) < t → t ≤ (1847686921441 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7356627568677 / 32000000000000 : ℝ) with h | h
  · exact I_277 t h1 h
  · exact I_278 t h h2

lemma J_280_282 : ∀ t : ℝ, (7424867802851 / 32000000000000 : ℝ) < t → t ≤ (299724321481 / 1280000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3729493959969 / 16000000000000 : ℝ) with h | h
  · exact I_280 t h1 h
  · exact I_281 t h h2

lemma J_279_282 : ∀ t : ℝ, (1847686921441 / 8000000000000 : ℝ) < t → t ≤ (299724321481 / 1280000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7424867802851 / 32000000000000 : ℝ) with h | h
  · exact I_279 t h1 h
  · exact J_280_282 t h h2

lemma J_277_282 : ∀ t : ℝ, (732250745159 / 3200000000000 : ℝ) < t → t ≤ (299724321481 / 1280000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1847686921441 / 8000000000000 : ℝ) with h | h
  · exact J_277_279 t h1 h
  · exact J_279_282 t h h2

lemma J_283_285 : ∀ t : ℝ, (29403234977 / 125000000000 : ℝ) < t → t ≤ (3797734194143 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7561348271199 / 32000000000000 : ℝ) with h | h
  · exact I_283 t h1 h
  · exact I_284 t h h2

lemma J_282_285 : ∀ t : ℝ, (299724321481 / 1280000000000 : ℝ) < t → t ≤ (3797734194143 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (29403234977 / 125000000000 : ℝ) with h | h
  · exact I_282 t h1 h
  · exact J_283_285 t h h2

lemma J_286_288 : ∀ t : ℝ, (383185431123 / 1600000000000 : ℝ) < t → t ≤ (975023636351 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3865974428317 / 16000000000000 : ℝ) with h | h
  · exact I_286 t h1 h
  · exact I_287 t h h2

lemma J_285_288 : ∀ t : ℝ, (3797734194143 / 16000000000000 : ℝ) < t → t ≤ (975023636351 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (383185431123 / 1600000000000 : ℝ) with h | h
  · exact I_285 t h1 h
  · exact J_286_288 t h h2

lemma J_282_288 : ∀ t : ℝ, (299724321481 / 1280000000000 : ℝ) < t → t ≤ (975023636351 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3797734194143 / 16000000000000 : ℝ) with h | h
  · exact J_282_285 t h1 h
  · exact J_285_288 t h h2

lemma J_277_288 : ∀ t : ℝ, (732250745159 / 3200000000000 : ℝ) < t → t ≤ (975023636351 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (299724321481 / 1280000000000 : ℝ) with h | h
  · exact J_277_282 t h1 h
  · exact J_282_288 t h h2

lemma J_288_290 : ∀ t : ℝ, (975023636351 / 4000000000000 : ℝ) < t → t ≤ (1984167389789 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3934214662491 / 16000000000000 : ℝ) with h | h
  · exact I_288 t h1 h
  · exact I_289 t h h2

lemma J_291_293 : ∀ t : ℝ, (504571876719 / 2000000000000 : ℝ) < t → t ≤ (41730554821 / 160000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2052407623963 / 8000000000000 : ℝ) with h | h
  · exact I_291 t h1 h
  · exact I_292 t h h2

lemma J_290_293 : ∀ t : ℝ, (1984167389789 / 8000000000000 : ℝ) < t → t ≤ (41730554821 / 160000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (504571876719 / 2000000000000 : ℝ) with h | h
  · exact I_290 t h1 h
  · exact J_291_293 t h h2

lemma J_288_293 : ∀ t : ℝ, (975023636351 / 4000000000000 : ℝ) < t → t ≤ (41730554821 / 160000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1984167389789 / 8000000000000 : ℝ) with h | h
  · exact J_288_290 t h1 h
  · exact J_290_293 t h h2

lemma J_294_296 : ∀ t : ℝ, (269345996903 / 1000000000000 : ℝ) < t → t ≤ (4387279507701 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (8696815458149 / 32000000000000 : ℝ) with h | h
  · exact I_294 t h1 h
  · exact I_295 t h h2

lemma J_293_296 : ∀ t : ℝ, (41730554821 / 160000000000 : ℝ) < t → t ≤ (4387279507701 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (269345996903 / 1000000000000 : ℝ) with h | h
  · exact I_293 t h1 h
  · exact J_294_296 t h h2

lemma J_297_299 : ∀ t : ℝ, (1770460514531 / 6400000000000 : ℝ) < t → t ≤ (2232511532477 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (17782348702563 / 64000000000000 : ℝ) with h | h
  · exact I_297 t h1 h
  · exact I_298 t h h2

lemma J_296_299 : ∀ t : ℝ, (4387279507701 / 16000000000000 : ℝ) < t → t ≤ (2232511532477 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1770460514531 / 6400000000000 : ℝ) with h | h
  · exact I_296 t h1 h
  · exact J_297_299 t h h2

lemma J_293_299 : ∀ t : ℝ, (41730554821 / 160000000000 : ℝ) < t → t ≤ (2232511532477 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4387279507701 / 16000000000000 : ℝ) with h | h
  · exact J_293_296 t h1 h
  · exact J_296_299 t h h2

lemma J_288_299 : ∀ t : ℝ, (975023636351 / 4000000000000 : ℝ) < t → t ≤ (2232511532477 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (41730554821 / 160000000000 : ℝ) with h | h
  · exact J_288_293 t h1 h
  · exact J_293_299 t h h2

lemma J_277_299 : ∀ t : ℝ, (732250745159 / 3200000000000 : ℝ) < t → t ≤ (2232511532477 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (975023636351 / 4000000000000 : ℝ) with h | h
  · exact J_277_288 t h1 h
  · exact J_288_299 t h h2

lemma J_256_299 : ∀ t : ℝ, (6947186163633 / 32000000000000 : ℝ) < t → t ≤ (2232511532477 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (732250745159 / 3200000000000 : ℝ) with h | h
  · exact J_256_277 t h1 h
  · exact J_277_299 t h h2

lemma J_299_301 : ∀ t : ℝ, (2232511532477 / 8000000000000 : ℝ) < t → t ≤ (9007789687161 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (17937835817069 / 64000000000000 : ℝ) with h | h
  · exact I_299 t h1 h
  · exact I_300 t h h2

lemma J_302_304 : ∀ t : ℝ, (723732917263 / 2560000000000 : ℝ) < t → t ≤ (36419876534909 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4542766622207 / 16000000000000 : ℝ) with h | h
  · exact I_302 t h1 h
  · exact I_303 t h h2

lemma J_301_304 : ∀ t : ℝ, (9007789687161 / 32000000000000 : ℝ) < t → t ≤ (36419876534909 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (723732917263 / 2560000000000 : ℝ) with h | h
  · exact I_301 t h1 h
  · exact J_302_304 t h h2

lemma J_299_304 : ∀ t : ℝ, (2232511532477 / 8000000000000 : ℝ) < t → t ≤ (36419876534909 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9007789687161 / 32000000000000 : ℝ) with h | h
  · exact J_299_301 t h1 h
  · exact J_301_304 t h h2

lemma J_304_306 : ∀ t : ℝ, (36419876534909 / 128000000000000 : ℝ) < t → t ≤ (7315072729883 / 25600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (18248810046081 / 64000000000000 : ℝ) with h | h
  · exact I_304 t h1 h
  · exact I_305 t h h2

lemma J_307_309 : ∀ t : ℝ, (9163276801667 / 32000000000000 : ℝ) < t → t ≤ (18404297160587 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (36730850763921 / 128000000000000 : ℝ) with h | h
  · exact I_307 t h1 h
  · exact I_308 t h h2

lemma J_306_309 : ∀ t : ℝ, (7315072729883 / 25600000000000 : ℝ) < t → t ≤ (18404297160587 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9163276801667 / 32000000000000 : ℝ) with h | h
  · exact I_306 t h1 h
  · exact J_307_309 t h h2

lemma J_304_309 : ∀ t : ℝ, (36419876534909 / 128000000000000 : ℝ) < t → t ≤ (18404297160587 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7315072729883 / 25600000000000 : ℝ) with h | h
  · exact J_304_306 t h1 h
  · exact J_306_309 t h h2

lemma J_299_309 : ∀ t : ℝ, (2232511532477 / 8000000000000 : ℝ) < t → t ≤ (18404297160587 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (36419876534909 / 128000000000000 : ℝ) with h | h
  · exact J_299_304 t h1 h
  · exact J_304_309 t h h2

lemma J_309_311 : ∀ t : ℝ, (18404297160587 / 64000000000000 : ℝ) < t → t ≤ (231025508973 / 800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (36886337878427 / 128000000000000 : ℝ) with h | h
  · exact I_309 t h1 h
  · exact I_310 t h h2

lemma J_312_314 : ∀ t : ℝ, (37041824992933 / 128000000000000 : ℝ) < t → t ≤ (37197312107439 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (18559784275093 / 64000000000000 : ℝ) with h | h
  · exact I_312 t h1 h
  · exact I_313 t h h2

lemma J_311_314 : ∀ t : ℝ, (231025508973 / 800000000000 : ℝ) < t → t ≤ (37197312107439 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (37041824992933 / 128000000000000 : ℝ) with h | h
  · exact I_311 t h1 h
  · exact J_312_314 t h h2

lemma J_309_314 : ∀ t : ℝ, (18404297160587 / 64000000000000 : ℝ) < t → t ≤ (37197312107439 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (231025508973 / 800000000000 : ℝ) with h | h
  · exact J_309_311 t h1 h
  · exact J_311_314 t h h2

lemma J_315_317 : ∀ t : ℝ, (9318763916173 / 32000000000000 : ℝ) < t → t ≤ (18715271389599 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7470559844389 / 25600000000000 : ℝ) with h | h
  · exact I_315 t h1 h
  · exact I_316 t h h2

lemma J_314_317 : ∀ t : ℝ, (37197312107439 / 128000000000000 : ℝ) < t → t ≤ (18715271389599 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9318763916173 / 32000000000000 : ℝ) with h | h
  · exact I_314 t h1 h
  · exact J_315_317 t h h2

lemma J_318_320 : ∀ t : ℝ, (37508286336451 / 128000000000000 : ℝ) < t → t ≤ (37663773450957 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4698253736713 / 16000000000000 : ℝ) with h | h
  · exact I_318 t h1 h
  · exact I_319 t h h2

lemma J_317_320 : ∀ t : ℝ, (18715271389599 / 64000000000000 : ℝ) < t → t ≤ (37663773450957 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (37508286336451 / 128000000000000 : ℝ) with h | h
  · exact I_317 t h1 h
  · exact J_318_320 t h h2

lemma J_314_320 : ∀ t : ℝ, (37197312107439 / 128000000000000 : ℝ) < t → t ≤ (37663773450957 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (18715271389599 / 64000000000000 : ℝ) with h | h
  · exact J_314_317 t h1 h
  · exact J_317_320 t h h2

lemma J_309_320 : ∀ t : ℝ, (18404297160587 / 64000000000000 : ℝ) < t → t ≤ (37663773450957 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (37197312107439 / 128000000000000 : ℝ) with h | h
  · exact J_309_314 t h1 h
  · exact J_314_320 t h h2

lemma J_299_320 : ∀ t : ℝ, (2232511532477 / 8000000000000 : ℝ) < t → t ≤ (37663773450957 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (18404297160587 / 64000000000000 : ℝ) with h | h
  · exact J_299_309 t h1 h
  · exact J_309_320 t h h2

lemma J_320_322 : ∀ t : ℝ, (37663773450957 / 128000000000000 : ℝ) < t → t ≤ (37819260565463 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3774151700821 / 12800000000000 : ℝ) with h | h
  · exact I_320 t h1 h
  · exact I_321 t h h2

lemma J_323_325 : ∀ t : ℝ, (9474251030679 / 32000000000000 : ℝ) < t → t ≤ (19026245618611 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (37974747679969 / 128000000000000 : ℝ) with h | h
  · exact I_323 t h1 h
  · exact I_324 t h h2

lemma J_322_325 : ∀ t : ℝ, (37819260565463 / 128000000000000 : ℝ) < t → t ≤ (19026245618611 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9474251030679 / 32000000000000 : ℝ) with h | h
  · exact I_322 t h1 h
  · exact J_323_325 t h h2

lemma J_320_325 : ∀ t : ℝ, (37663773450957 / 128000000000000 : ℝ) < t → t ≤ (19026245618611 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (37819260565463 / 128000000000000 : ℝ) with h | h
  · exact J_320_322 t h1 h
  · exact J_322_325 t h h2

lemma J_326_328 : ∀ t : ℝ, (1525209391779 / 5120000000000 : ℝ) < t → t ≤ (38285721908981 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2387998646983 / 8000000000000 : ℝ) with h | h
  · exact I_326 t h1 h
  · exact I_327 t h h2

lemma J_325_328 : ∀ t : ℝ, (19026245618611 / 64000000000000 : ℝ) < t → t ≤ (38285721908981 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1525209391779 / 5120000000000 : ℝ) with h | h
  · exact I_325 t h1 h
  · exact J_326_328 t h h2

lemma J_329_331 : ∀ t : ℝ, (19181732733117 / 64000000000000 : ℝ) < t → t ≤ (1925947629037 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (38441209023487 / 128000000000000 : ℝ) with h | h
  · exact I_329 t h1 h
  · exact I_330 t h h2

lemma J_328_331 : ∀ t : ℝ, (38285721908981 / 128000000000000 : ℝ) < t → t ≤ (1925947629037 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19181732733117 / 64000000000000 : ℝ) with h | h
  · exact I_328 t h1 h
  · exact J_329_331 t h h2

lemma J_325_331 : ∀ t : ℝ, (19026245618611 / 64000000000000 : ℝ) < t → t ≤ (1925947629037 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (38285721908981 / 128000000000000 : ℝ) with h | h
  · exact J_325_328 t h1 h
  · exact J_328_331 t h h2

lemma J_320_331 : ∀ t : ℝ, (37663773450957 / 128000000000000 : ℝ) < t → t ≤ (1925947629037 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19026245618611 / 64000000000000 : ℝ) with h | h
  · exact J_320_325 t h1 h
  · exact J_325_331 t h h2

lemma J_331_333 : ∀ t : ℝ, (1925947629037 / 6400000000000 : ℝ) < t → t ≤ (4853740851219 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19337219847623 / 64000000000000 : ℝ) with h | h
  · exact I_331 t h1 h
  · exact I_332 t h h2

lemma J_334_336 : ∀ t : ℝ, (19492706962129 / 64000000000000 : ℝ) < t → t ≤ (3929638815327 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9785225259691 / 32000000000000 : ℝ) with h | h
  · exact I_334 t h1 h
  · exact I_335 t h h2

lemma J_333_336 : ∀ t : ℝ, (4853740851219 / 16000000000000 : ℝ) < t → t ≤ (3929638815327 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19492706962129 / 64000000000000 : ℝ) with h | h
  · exact I_333 t h1 h
  · exact J_334_336 t h h2

lemma J_331_336 : ∀ t : ℝ, (1925947629037 / 6400000000000 : ℝ) < t → t ≤ (3929638815327 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4853740851219 / 16000000000000 : ℝ) with h | h
  · exact J_331_333 t h1 h
  · exact J_333_336 t h h2

lemma J_337_339 : ∀ t : ℝ, (616435551059 / 2000000000000 : ℝ) < t → t ≤ (9940712374197 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19803681191141 / 64000000000000 : ℝ) with h | h
  · exact I_337 t h1 h
  · exact I_338 t h h2

lemma J_336_339 : ∀ t : ℝ, (3929638815327 / 12800000000000 : ℝ) < t → t ≤ (9940712374197 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (616435551059 / 2000000000000 : ℝ) with h | h
  · exact I_336 t h1 h
  · exact J_337_339 t h h2

lemma J_340_342 : ∀ t : ℝ, (200369118629 / 640000000000 : ℝ) < t → t ≤ (2543485761489 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10096199488703 / 32000000000000 : ℝ) with h | h
  · exact I_340 t h1 h
  · exact I_341 t h h2

lemma J_339_342 : ∀ t : ℝ, (9940712374197 / 32000000000000 : ℝ) < t → t ≤ (2543485761489 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (200369118629 / 640000000000 : ℝ) with h | h
  · exact I_339 t h1 h
  · exact J_340_342 t h h2

lemma J_336_342 : ∀ t : ℝ, (3929638815327 / 12800000000000 : ℝ) < t → t ≤ (2543485761489 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9940712374197 / 32000000000000 : ℝ) with h | h
  · exact J_336_339 t h1 h
  · exact J_339_342 t h h2

lemma J_331_342 : ∀ t : ℝ, (1925947629037 / 6400000000000 : ℝ) < t → t ≤ (2543485761489 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3929638815327 / 12800000000000 : ℝ) with h | h
  · exact J_331_336 t h1 h
  · exact J_336_342 t h h2

lemma J_320_342 : ∀ t : ℝ, (37663773450957 / 128000000000000 : ℝ) < t → t ≤ (2543485761489 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1925947629037 / 6400000000000 : ℝ) with h | h
  · exact J_320_331 t h1 h
  · exact J_331_342 t h h2

lemma J_299_342 : ∀ t : ℝ, (2232511532477 / 8000000000000 : ℝ) < t → t ≤ (2543485761489 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (37663773450957 / 128000000000000 : ℝ) with h | h
  · exact J_299_320 t h1 h
  · exact J_320_342 t h h2

lemma J_256_342 : ∀ t : ℝ, (6947186163633 / 32000000000000 : ℝ) < t → t ≤ (2543485761489 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2232511532477 / 8000000000000 : ℝ) with h | h
  · exact J_256_299 t h1 h
  · exact J_299_342 t h h2

lemma J_171_342 : ∀ t : ℝ, (7286102560843 / 64000000000000 : ℝ) < t → t ≤ (2543485761489 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (6947186163633 / 32000000000000 : ℝ) with h | h
  · exact J_171_256 t h1 h
  · exact J_256_342 t h h2

lemma J_0_342 : ∀ t : ℝ, (0 : ℝ) < t → t ≤ (2543485761489 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7286102560843 / 64000000000000 : ℝ) with h | h
  · exact J_0_171 t h1 h
  · exact J_171_342 t h h2

lemma J_342_344 : ∀ t : ℝ, (2543485761489 / 8000000000000 : ℝ) < t → t ≤ (5164715080231 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10251686603209 / 32000000000000 : ℝ) with h | h
  · exact I_342 t h1 h
  · exact I_343 t h h2

lemma J_345_347 : ∀ t : ℝ, (1310614659371 / 4000000000000 : ℝ) < t → t ≤ (539794575199 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5320202194737 / 16000000000000 : ℝ) with h | h
  · exact I_345 t h1 h
  · exact I_346 t h h2

lemma J_344_347 : ∀ t : ℝ, (5164715080231 / 16000000000000 : ℝ) < t → t ≤ (539794575199 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1310614659371 / 4000000000000 : ℝ) with h | h
  · exact I_344 t h1 h
  · exact J_345_347 t h h2

lemma J_342_347 : ∀ t : ℝ, (2543485761489 / 8000000000000 : ℝ) < t → t ≤ (539794575199 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5164715080231 / 16000000000000 : ℝ) with h | h
  · exact J_342_344 t h1 h
  · exact J_344_347 t h h2

lemma J_347_349 : ∀ t : ℝ, (539794575199 / 1600000000000 : ℝ) < t → t ≤ (86772388539 / 250000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5475689309243 / 16000000000000 : ℝ) with h | h
  · exact I_347 t h1 h
  · exact I_348 t h h2

lemma J_350_352 : ∀ t : ℝ, (11190582883251 / 32000000000000 : ℝ) < t → t ≤ (11358017183769 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1127430003351 / 3200000000000 : ℝ) with h | h
  · exact I_350 t h1 h
  · exact I_351 t h h2

lemma J_349_352 : ∀ t : ℝ, (86772388539 / 250000000000 : ℝ) < t → t ≤ (11358017183769 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11190582883251 / 32000000000000 : ℝ) with h | h
  · exact I_349 t h1 h
  · exact J_350_352 t h h2

lemma J_347_352 : ∀ t : ℝ, (539794575199 / 1600000000000 : ℝ) < t → t ≤ (11358017183769 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (86772388539 / 250000000000 : ℝ) with h | h
  · exact J_347_349 t h1 h
  · exact J_349_352 t h h2

lemma J_342_352 : ∀ t : ℝ, (2543485761489 / 8000000000000 : ℝ) < t → t ≤ (11358017183769 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (539794575199 / 1600000000000 : ℝ) with h | h
  · exact J_342_347 t h1 h
  · exact J_347_352 t h h2

lemma J_352_354 : ∀ t : ℝ, (11358017183769 / 32000000000000 : ℝ) < t → t ≤ (2860433583507 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (22799751517797 / 64000000000000 : ℝ) with h | h
  · exact I_352 t h1 h
  · exact I_353 t h h2

lemma J_355_357 : ∀ t : ℝ, (4593437163663 / 12800000000000 : ℝ) < t → t ≤ (23134620118833 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11525451484287 / 32000000000000 : ℝ) with h | h
  · exact I_355 t h1 h
  · exact I_356 t h h2

lemma J_354_357 : ∀ t : ℝ, (2860433583507 / 8000000000000 : ℝ) < t → t ≤ (23134620118833 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4593437163663 / 12800000000000 : ℝ) with h | h
  · exact I_354 t h1 h
  · exact J_355_357 t h h2

lemma J_352_357 : ∀ t : ℝ, (11358017183769 / 32000000000000 : ℝ) < t → t ≤ (23134620118833 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2860433583507 / 8000000000000 : ℝ) with h | h
  · exact J_352_354 t h1 h
  · exact J_354_357 t h h2

lemma J_358_360 : ∀ t : ℝ, (5804584317273 / 16000000000000 : ℝ) < t → t ≤ (23302054419351 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (46520391688443 / 128000000000000 : ℝ) with h | h
  · exact I_358 t h1 h
  · exact I_359 t h h2

lemma J_357_360 : ∀ t : ℝ, (23134620118833 / 64000000000000 : ℝ) < t → t ≤ (23302054419351 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5804584317273 / 16000000000000 : ℝ) with h | h
  · exact I_357 t h1 h
  · exact J_358_360 t h h2

lemma J_361_363 : ∀ t : ℝ, (46687825988961 / 128000000000000 : ℝ) < t → t ≤ (46855260289479 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2338577156961 / 6400000000000 : ℝ) with h | h
  · exact I_361 t h1 h
  · exact I_362 t h h2

lemma J_360_363 : ∀ t : ℝ, (23302054419351 / 64000000000000 : ℝ) < t → t ≤ (46855260289479 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (46687825988961 / 128000000000000 : ℝ) with h | h
  · exact I_360 t h1 h
  · exact J_361_363 t h h2

lemma J_357_363 : ∀ t : ℝ, (23134620118833 / 64000000000000 : ℝ) < t → t ≤ (46855260289479 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23302054419351 / 64000000000000 : ℝ) with h | h
  · exact J_357_360 t h1 h
  · exact J_360_363 t h h2

lemma J_352_363 : ∀ t : ℝ, (11358017183769 / 32000000000000 : ℝ) < t → t ≤ (46855260289479 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23134620118833 / 64000000000000 : ℝ) with h | h
  · exact J_352_357 t h1 h
  · exact J_357_363 t h h2

lemma J_342_363 : ∀ t : ℝ, (2543485761489 / 8000000000000 : ℝ) < t → t ≤ (46855260289479 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11358017183769 / 32000000000000 : ℝ) with h | h
  · exact J_342_352 t h1 h
  · exact J_352_363 t h h2

lemma J_363_365 : ∀ t : ℝ, (46855260289479 / 128000000000000 : ℝ) < t → t ≤ (47022694589997 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23469488719869 / 64000000000000 : ℝ) with h | h
  · exact I_363 t h1 h
  · exact I_364 t h h2

lemma J_366_368 : ∀ t : ℝ, (1472075366883 / 4000000000000 : ℝ) < t → t ≤ (23636923020387 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9438025778103 / 25600000000000 : ℝ) with h | h
  · exact I_366 t h1 h
  · exact I_367 t h h2

lemma J_365_368 : ∀ t : ℝ, (47022694589997 / 128000000000000 : ℝ) < t → t ≤ (23636923020387 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1472075366883 / 4000000000000 : ℝ) with h | h
  · exact I_365 t h1 h
  · exact J_366_368 t h h2

lemma J_363_368 : ∀ t : ℝ, (46855260289479 / 128000000000000 : ℝ) < t → t ≤ (23636923020387 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (47022694589997 / 128000000000000 : ℝ) with h | h
  · exact J_363_365 t h1 h
  · exact J_365_368 t h h2

lemma J_368_370 : ∀ t : ℝ, (23636923020387 / 64000000000000 : ℝ) < t → t ≤ (11860320085323 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (47357563191033 / 128000000000000 : ℝ) with h | h
  · exact I_368 t h1 h
  · exact I_369 t h h2

lemma J_371_373 : ∀ t : ℝ, (47524997491551 / 128000000000000 : ℝ) < t → t ≤ (47692431792069 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4760871464181 / 12800000000000 : ℝ) with h | h
  · exact I_371 t h1 h
  · exact I_372 t h h2

lemma J_370_373 : ∀ t : ℝ, (11860320085323 / 32000000000000 : ℝ) < t → t ≤ (47692431792069 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (47524997491551 / 128000000000000 : ℝ) with h | h
  · exact I_370 t h1 h
  · exact J_371_373 t h h2

lemma J_368_373 : ∀ t : ℝ, (23636923020387 / 64000000000000 : ℝ) < t → t ≤ (47692431792069 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11860320085323 / 32000000000000 : ℝ) with h | h
  · exact J_368_370 t h1 h
  · exact J_370_373 t h h2

lemma J_363_373 : ∀ t : ℝ, (46855260289479 / 128000000000000 : ℝ) < t → t ≤ (47692431792069 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23636923020387 / 64000000000000 : ℝ) with h | h
  · exact J_363_368 t h1 h
  · exact J_368_373 t h h2

lemma J_373_375 : ∀ t : ℝ, (47692431792069 / 128000000000000 : ℝ) < t → t ≤ (47859866092587 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5972018617791 / 16000000000000 : ℝ) with h | h
  · exact I_373 t h1 h
  · exact I_374 t h h2

lemma J_376_378 : ∀ t : ℝ, (23971791621423 / 64000000000000 : ℝ) < t → t ≤ (12027754385841 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9605460078621 / 25600000000000 : ℝ) with h | h
  · exact I_376 t h1 h
  · exact I_377 t h h2

lemma J_375_378 : ∀ t : ℝ, (47859866092587 / 128000000000000 : ℝ) < t → t ≤ (12027754385841 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23971791621423 / 64000000000000 : ℝ) with h | h
  · exact I_375 t h1 h
  · exact J_376_378 t h h2

lemma J_373_378 : ∀ t : ℝ, (47692431792069 / 128000000000000 : ℝ) < t → t ≤ (12027754385841 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (47859866092587 / 128000000000000 : ℝ) with h | h
  · exact J_373_375 t h1 h
  · exact J_375_378 t h h2

lemma J_379_381 : ∀ t : ℝ, (48194734693623 / 128000000000000 : ℝ) < t → t ≤ (48362168994141 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (24139225921941 / 64000000000000 : ℝ) with h | h
  · exact I_379 t h1 h
  · exact I_380 t h h2

lemma J_378_381 : ∀ t : ℝ, (12027754385841 / 32000000000000 : ℝ) < t → t ≤ (48362168994141 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (48194734693623 / 128000000000000 : ℝ) with h | h
  · exact I_378 t h1 h
  · exact J_379_381 t h h2

lemma J_382_384 : ∀ t : ℝ, (121114715361 / 320000000000 : ℝ) < t → t ≤ (24306660222459 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (48529603294659 / 128000000000000 : ℝ) with h | h
  · exact I_382 t h1 h
  · exact I_383 t h h2

lemma J_381_384 : ∀ t : ℝ, (48362168994141 / 128000000000000 : ℝ) < t → t ≤ (24306660222459 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (121114715361 / 320000000000 : ℝ) with h | h
  · exact I_381 t h1 h
  · exact J_382_384 t h h2

lemma J_378_384 : ∀ t : ℝ, (12027754385841 / 32000000000000 : ℝ) < t → t ≤ (24306660222459 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (48362168994141 / 128000000000000 : ℝ) with h | h
  · exact J_378_381 t h1 h
  · exact J_381_384 t h h2

lemma J_373_384 : ∀ t : ℝ, (47692431792069 / 128000000000000 : ℝ) < t → t ≤ (24306660222459 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (12027754385841 / 32000000000000 : ℝ) with h | h
  · exact J_373_378 t h1 h
  · exact J_378_384 t h h2

lemma J_363_384 : ∀ t : ℝ, (46855260289479 / 128000000000000 : ℝ) < t → t ≤ (24306660222459 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (47692431792069 / 128000000000000 : ℝ) with h | h
  · exact J_363_373 t h1 h
  · exact J_373_384 t h h2

lemma J_342_384 : ∀ t : ℝ, (2543485761489 / 8000000000000 : ℝ) < t → t ≤ (24306660222459 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (46855260289479 / 128000000000000 : ℝ) with h | h
  · exact J_342_363 t h1 h
  · exact J_363_384 t h h2

lemma J_384_386 : ∀ t : ℝ, (24306660222459 / 64000000000000 : ℝ) < t → t ≤ (12195188686359 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (48697037595177 / 128000000000000 : ℝ) with h | h
  · exact I_384 t h1 h
  · exact I_385 t h h2

lemma J_387_389 : ∀ t : ℝ, (9772894379139 / 25600000000000 : ℝ) < t → t ≤ (6139452918309 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (24474094522977 / 64000000000000 : ℝ) with h | h
  · exact I_387 t h1 h
  · exact I_388 t h h2

lemma J_386_389 : ∀ t : ℝ, (12195188686359 / 32000000000000 : ℝ) < t → t ≤ (6139452918309 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9772894379139 / 25600000000000 : ℝ) with h | h
  · exact I_386 t h1 h
  · exact J_387_389 t h h2

lemma J_384_389 : ∀ t : ℝ, (24306660222459 / 64000000000000 : ℝ) < t → t ≤ (6139452918309 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (12195188686359 / 32000000000000 : ℝ) with h | h
  · exact J_384_386 t h1 h
  · exact J_386_389 t h h2

lemma J_389_391 : ∀ t : ℝ, (6139452918309 / 16000000000000 : ℝ) < t → t ≤ (12362622986877 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4928305764699 / 12800000000000 : ℝ) with h | h
  · exact I_389 t h1 h
  · exact I_390 t h h2

lemma J_392_394 : ∀ t : ℝ, (24808963124013 / 64000000000000 : ℝ) < t → t ≤ (24976397424531 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (777896258571 / 2000000000000 : ℝ) with h | h
  · exact I_392 t h1 h
  · exact I_393 t h h2

lemma J_391_394 : ∀ t : ℝ, (12362622986877 / 32000000000000 : ℝ) < t → t ≤ (24976397424531 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (24808963124013 / 64000000000000 : ℝ) with h | h
  · exact I_391 t h1 h
  · exact J_392_394 t h h2

lemma J_389_394 : ∀ t : ℝ, (6139452918309 / 16000000000000 : ℝ) < t → t ≤ (24976397424531 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (12362622986877 / 32000000000000 : ℝ) with h | h
  · exact J_389_391 t h1 h
  · exact J_391_394 t h h2

lemma J_384_394 : ∀ t : ℝ, (24306660222459 / 64000000000000 : ℝ) < t → t ≤ (24976397424531 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (6139452918309 / 16000000000000 : ℝ) with h | h
  · exact J_384_389 t h1 h
  · exact J_389_394 t h h2

lemma J_394_396 : ∀ t : ℝ, (24976397424531 / 64000000000000 : ℝ) < t → t ≤ (25143831725049 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2506011457479 / 6400000000000 : ℝ) with h | h
  · exact I_394 t h1 h
  · exact I_395 t h h2

lemma J_397_399 : ∀ t : ℝ, (6306887218827 / 16000000000000 : ℝ) < t → t ≤ (3195302184543 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (12697491587913 / 32000000000000 : ℝ) with h | h
  · exact I_397 t h1 h
  · exact I_398 t h h2

lemma J_396_399 : ∀ t : ℝ, (25143831725049 / 64000000000000 : ℝ) < t → t ≤ (3195302184543 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (6306887218827 / 16000000000000 : ℝ) with h | h
  · exact I_396 t h1 h
  · exact J_397_399 t h h2

lemma J_394_399 : ∀ t : ℝ, (24976397424531 / 64000000000000 : ℝ) < t → t ≤ (3195302184543 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (25143831725049 / 64000000000000 : ℝ) with h | h
  · exact J_394_396 t h1 h
  · exact J_396_399 t h h2

lemma J_400_402 : ∀ t : ℝ, (12864925888431 / 32000000000000 : ℝ) < t → t ≤ (13032360188949 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1294864303869 / 3200000000000 : ℝ) with h | h
  · exact I_400 t h1 h
  · exact I_401 t h h2

lemma J_399_402 : ∀ t : ℝ, (3195302184543 / 8000000000000 : ℝ) < t → t ≤ (13032360188949 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (12864925888431 / 32000000000000 : ℝ) with h | h
  · exact I_399 t h1 h
  · exact J_400_402 t h h2

lemma J_403_405 : ∀ t : ℝ, (1639509667401 / 4000000000000 : ℝ) < t → t ≤ (3362736485061 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (6641755819863 / 16000000000000 : ℝ) with h | h
  · exact I_403 t h1 h
  · exact I_404 t h h2

lemma J_402_405 : ∀ t : ℝ, (13032360188949 / 32000000000000 : ℝ) < t → t ≤ (3362736485061 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1639509667401 / 4000000000000 : ℝ) with h | h
  · exact I_402 t h1 h
  · exact J_403_405 t h h2

lemma J_399_405 : ∀ t : ℝ, (3195302184543 / 8000000000000 : ℝ) < t → t ≤ (3362736485061 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (13032360188949 / 32000000000000 : ℝ) with h | h
  · exact J_399_402 t h1 h
  · exact J_402_405 t h h2

lemma J_394_405 : ∀ t : ℝ, (24976397424531 / 64000000000000 : ℝ) < t → t ≤ (3362736485061 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3195302184543 / 8000000000000 : ℝ) with h | h
  · exact J_394_399 t h1 h
  · exact J_399_405 t h h2

lemma J_384_405 : ∀ t : ℝ, (24306660222459 / 64000000000000 : ℝ) < t → t ≤ (3362736485061 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (24976397424531 / 64000000000000 : ℝ) with h | h
  · exact J_384_394 t h1 h
  · exact J_394_405 t h h2

lemma J_405_407 : ∀ t : ℝ, (3362736485061 / 8000000000000 : ℝ) < t → t ≤ (86161340883 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (6809190120381 / 16000000000000 : ℝ) with h | h
  · exact I_405 t h1 h
  · exact I_406 t h h2

lemma J_408_410 : ∀ t : ℝ, (54181913021 / 125000000000 : ℝ) < t → t ≤ (219376251837 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (436103903921 / 1000000000000 : ℝ) with h | h
  · exact I_408 t h1 h
  · exact I_409 t h h2

lemma J_407_410 : ∀ t : ℝ, (86161340883 / 200000000000 : ℝ) < t → t ≤ (219376251837 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (54181913021 / 125000000000 : ℝ) with h | h
  · exact I_407 t h1 h
  · exact J_408_410 t h h2

lemma J_405_410 : ∀ t : ℝ, (3362736485061 / 8000000000000 : ℝ) < t → t ≤ (219376251837 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (86161340883 / 200000000000 : ℝ) with h | h
  · exact J_405_407 t h1 h
  · exact J_407_410 t h h2

lemma J_411_413 : ∀ t : ℝ, (880153607101 / 2000000000000 : ℝ) < t → t ≤ (885450806607 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (441401103427 / 1000000000000 : ℝ) with h | h
  · exact I_411 t h1 h
  · exact I_412 t h h2

lemma J_410_413 : ∀ t : ℝ, (219376251837 / 500000000000 : ℝ) < t → t ≤ (885450806607 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (880153607101 / 2000000000000 : ℝ) with h | h
  · exact I_410 t h1 h
  · exact J_411_413 t h h2

lemma J_414_416 : ∀ t : ℝ, (22202485159 / 50000000000 : ℝ) < t → t ≤ (446698302933 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (890748006113 / 2000000000000 : ℝ) with h | h
  · exact I_414 t h1 h
  · exact I_415 t h h2

lemma J_413_416 : ∀ t : ℝ, (885450806607 / 2000000000000 : ℝ) < t → t ≤ (446698302933 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (22202485159 / 50000000000 : ℝ) with h | h
  · exact I_413 t h1 h
  · exact J_414_416 t h h2

lemma J_410_416 : ∀ t : ℝ, (219376251837 / 500000000000 : ℝ) < t → t ≤ (446698302933 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (885450806607 / 2000000000000 : ℝ) with h | h
  · exact J_410_413 t h1 h
  · exact J_413_416 t h h2

lemma J_405_416 : ∀ t : ℝ, (3362736485061 / 8000000000000 : ℝ) < t → t ≤ (446698302933 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (219376251837 / 500000000000 : ℝ) with h | h
  · exact J_405_410 t h1 h
  · exact J_410_416 t h h2

lemma J_416_418 : ∀ t : ℝ, (446698302933 / 1000000000000 : ℝ) < t → t ≤ (1794739010991 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (896045205619 / 2000000000000 : ℝ) with h | h
  · exact I_416 t h1 h
  · exact I_417 t h h2

lemma J_419_421 : ∀ t : ℝ, (224673451343 / 500000000000 : ℝ) < t → t ≤ (7210739241 / 16000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1800036210497 / 4000000000000 : ℝ) with h | h
  · exact I_419 t h1 h
  · exact I_420 t h h2

lemma J_418_421 : ∀ t : ℝ, (1794739010991 / 4000000000000 : ℝ) < t → t ≤ (7210739241 / 16000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (224673451343 / 500000000000 : ℝ) with h | h
  · exact I_418 t h1 h
  · exact J_419_421 t h h2

lemma J_416_421 : ∀ t : ℝ, (446698302933 / 1000000000000 : ℝ) < t → t ≤ (7210739241 / 16000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1794739010991 / 4000000000000 : ℝ) with h | h
  · exact J_416_418 t h1 h
  · exact J_418_421 t h h2

lemma J_422_424 : ∀ t : ℝ, (1805333410003 / 4000000000000 : ℝ) < t → t ≤ (1810630609509 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (451995502439 / 1000000000000 : ℝ) with h | h
  · exact I_422 t h1 h
  · exact I_423 t h h2

lemma J_421_424 : ∀ t : ℝ, (7210739241 / 16000000000 : ℝ) < t → t ≤ (1810630609509 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1805333410003 / 4000000000000 : ℝ) with h | h
  · exact I_421 t h1 h
  · exact J_422_424 t h h2

lemma J_425_427 : ∀ t : ℝ, (906639604631 / 2000000000000 : ℝ) < t → t ≤ (28415256387 / 62500000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (363185561803 / 800000000000 : ℝ) with h | h
  · exact I_425 t h1 h
  · exact I_426 t h h2

lemma J_424_427 : ∀ t : ℝ, (1810630609509 / 4000000000000 : ℝ) < t → t ≤ (28415256387 / 62500000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (906639604631 / 2000000000000 : ℝ) with h | h
  · exact I_424 t h1 h
  · exact J_425_427 t h h2

lemma J_421_427 : ∀ t : ℝ, (7210739241 / 16000000000 : ℝ) < t → t ≤ (28415256387 / 62500000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1810630609509 / 4000000000000 : ℝ) with h | h
  · exact J_421_424 t h1 h
  · exact J_424_427 t h h2

lemma J_416_427 : ∀ t : ℝ, (446698302933 / 1000000000000 : ℝ) < t → t ≤ (28415256387 / 62500000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7210739241 / 16000000000 : ℝ) with h | h
  · exact J_416_421 t h1 h
  · exact J_421_427 t h h2

lemma J_405_427 : ∀ t : ℝ, (3362736485061 / 8000000000000 : ℝ) < t → t ≤ (28415256387 / 62500000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (446698302933 / 1000000000000 : ℝ) with h | h
  · exact J_405_416 t h1 h
  · exact J_416_427 t h h2

lemma J_384_427 : ∀ t : ℝ, (24306660222459 / 64000000000000 : ℝ) < t → t ≤ (28415256387 / 62500000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3362736485061 / 8000000000000 : ℝ) with h | h
  · exact J_384_405 t h1 h
  · exact J_405_427 t h h2

lemma J_342_427 : ∀ t : ℝ, (2543485761489 / 8000000000000 : ℝ) < t → t ≤ (28415256387 / 62500000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (24306660222459 / 64000000000000 : ℝ) with h | h
  · exact J_342_384 t h1 h
  · exact J_384_427 t h h2

lemma J_427_429 : ∀ t : ℝ, (28415256387 / 62500000000 : ℝ) < t → t ≤ (911936804137 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1821225008521 / 4000000000000 : ℝ) with h | h
  · exact I_427 t h1 h
  · exact I_428 t h h2

lemma J_430_432 : ∀ t : ℝ, (1826522208027 / 4000000000000 : ℝ) < t → t ≤ (1831819407533 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (91458540389 / 200000000000 : ℝ) with h | h
  · exact I_430 t h1 h
  · exact I_431 t h h2

lemma J_429_432 : ∀ t : ℝ, (911936804137 / 2000000000000 : ℝ) < t → t ≤ (1831819407533 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1826522208027 / 4000000000000 : ℝ) with h | h
  · exact I_429 t h1 h
  · exact J_430_432 t h h2

lemma J_427_432 : ∀ t : ℝ, (28415256387 / 62500000000 : ℝ) < t → t ≤ (1831819407533 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (911936804137 / 2000000000000 : ℝ) with h | h
  · exact J_427_429 t h1 h
  · exact J_429_432 t h h2

lemma J_432_434 : ∀ t : ℝ, (1831819407533 / 4000000000000 : ℝ) < t → t ≤ (1837116607039 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (917234003643 / 2000000000000 : ℝ) with h | h
  · exact I_432 t h1 h
  · exact I_433 t h h2

lemma J_435_437 : ∀ t : ℝ, (229970650849 / 500000000000 : ℝ) < t → t ≤ (922531203149 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (368482761309 / 800000000000 : ℝ) with h | h
  · exact I_435 t h1 h
  · exact I_436 t h h2

lemma J_434_437 : ∀ t : ℝ, (1837116607039 / 4000000000000 : ℝ) < t → t ≤ (922531203149 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (229970650849 / 500000000000 : ℝ) with h | h
  · exact I_434 t h1 h
  · exact J_435_437 t h h2

lemma J_432_437 : ∀ t : ℝ, (1831819407533 / 4000000000000 : ℝ) < t → t ≤ (922531203149 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1837116607039 / 4000000000000 : ℝ) with h | h
  · exact J_432_434 t h1 h
  · exact J_434_437 t h h2

lemma J_427_437 : ∀ t : ℝ, (28415256387 / 62500000000 : ℝ) < t → t ≤ (922531203149 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1831819407533 / 4000000000000 : ℝ) with h | h
  · exact J_427_432 t h1 h
  · exact J_432_437 t h h2

lemma J_437_439 : ∀ t : ℝ, (922531203149 / 2000000000000 : ℝ) < t → t ≤ (462589901451 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1847711006051 / 4000000000000 : ℝ) with h | h
  · exact I_437 t h1 h
  · exact I_438 t h h2

lemma J_440_442 : ∀ t : ℝ, (1853008205557 / 4000000000000 : ℝ) < t → t ≤ (1858305405063 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (185565680531 / 400000000000 : ℝ) with h | h
  · exact I_440 t h1 h
  · exact I_441 t h h2

lemma J_439_442 : ∀ t : ℝ, (462589901451 / 1000000000000 : ℝ) < t → t ≤ (1858305405063 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1853008205557 / 4000000000000 : ℝ) with h | h
  · exact I_439 t h1 h
  · exact J_440_442 t h h2

lemma J_437_442 : ∀ t : ℝ, (922531203149 / 2000000000000 : ℝ) < t → t ≤ (1858305405063 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (462589901451 / 1000000000000 : ℝ) with h | h
  · exact J_437_439 t h1 h
  · exact J_439_442 t h h2

lemma J_443_445 : ∀ t : ℝ, (116309625301 / 250000000000 : ℝ) < t → t ≤ (933125602161 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1863602604569 / 4000000000000 : ℝ) with h | h
  · exact I_443 t h1 h
  · exact I_444 t h h2

lemma J_442_445 : ∀ t : ℝ, (1858305405063 / 4000000000000 : ℝ) < t → t ≤ (933125602161 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (116309625301 / 250000000000 : ℝ) with h | h
  · exact I_442 t h1 h
  · exact J_443_445 t h h2

lemma J_446_448 : ∀ t : ℝ, (467887100957 / 1000000000000 : ℝ) < t → t ≤ (47053570071 / 100000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (938422801667 / 2000000000000 : ℝ) with h | h
  · exact I_446 t h1 h
  · exact I_447 t h h2

lemma J_445_448 : ∀ t : ℝ, (933125602161 / 2000000000000 : ℝ) < t → t ≤ (47053570071 / 100000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (467887100957 / 1000000000000 : ℝ) with h | h
  · exact I_445 t h1 h
  · exact J_446_448 t h h2

lemma J_442_448 : ∀ t : ℝ, (1858305405063 / 4000000000000 : ℝ) < t → t ≤ (47053570071 / 100000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (933125602161 / 2000000000000 : ℝ) with h | h
  · exact J_442_445 t h1 h
  · exact J_445_448 t h h2

lemma J_437_448 : ∀ t : ℝ, (922531203149 / 2000000000000 : ℝ) < t → t ≤ (47053570071 / 100000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1858305405063 / 4000000000000 : ℝ) with h | h
  · exact J_437_442 t h1 h
  · exact J_442_448 t h h2

lemma J_427_448 : ∀ t : ℝ, (28415256387 / 62500000000 : ℝ) < t → t ≤ (47053570071 / 100000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (922531203149 / 2000000000000 : ℝ) with h | h
  · exact J_427_437 t h1 h
  · exact J_437_448 t h h2

lemma J_448_450 : ∀ t : ℝ, (47053570071 / 100000000000 : ℝ) < t → t ≤ (473184300463 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (943720001173 / 2000000000000 : ℝ) with h | h
  · exact I_448 t h1 h
  · exact I_449 t h h2

lemma J_451_453 : ∀ t : ℝ, (949017200679 / 2000000000000 : ℝ) < t → t ≤ (190862880037 / 400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (59479112527 / 125000000000 : ℝ) with h | h
  · exact I_451 t h1 h
  · exact I_452 t h h2

lemma J_450_453 : ∀ t : ℝ, (473184300463 / 1000000000000 : ℝ) < t → t ≤ (190862880037 / 400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (949017200679 / 2000000000000 : ℝ) with h | h
  · exact I_450 t h1 h
  · exact J_451_453 t h h2

lemma J_448_453 : ∀ t : ℝ, (47053570071 / 100000000000 : ℝ) < t → t ≤ (190862880037 / 400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (473184300463 / 1000000000000 : ℝ) with h | h
  · exact J_448_450 t h1 h
  · exact J_450_453 t h h2

lemma J_454_456 : ∀ t : ℝ, (478481499969 / 1000000000000 : ℝ) < t → t ≤ (240565049861 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (959611599691 / 2000000000000 : ℝ) with h | h
  · exact I_454 t h1 h
  · exact I_455 t h h2

lemma J_453_456 : ∀ t : ℝ, (190862880037 / 400000000000 : ℝ) < t → t ≤ (240565049861 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (478481499969 / 1000000000000 : ℝ) with h | h
  · exact I_453 t h1 h
  · exact J_454_456 t h h2

lemma J_457_459 : ∀ t : ℝ, (19351147979 / 40000000000 : ℝ) < t → t ≤ (489075898981 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (121606824807 / 250000000000 : ℝ) with h | h
  · exact I_457 t h1 h
  · exact I_458 t h h2

lemma J_456_459 : ∀ t : ℝ, (240565049861 / 500000000000 : ℝ) < t → t ≤ (489075898981 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19351147979 / 40000000000 : ℝ) with h | h
  · exact I_456 t h1 h
  · exact J_457_459 t h h2

lemma J_453_459 : ∀ t : ℝ, (190862880037 / 400000000000 : ℝ) < t → t ≤ (489075898981 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (240565049861 / 500000000000 : ℝ) with h | h
  · exact J_453_456 t h1 h
  · exact J_456_459 t h h2

lemma J_448_459 : ∀ t : ℝ, (47053570071 / 100000000000 : ℝ) < t → t ≤ (489075898981 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (190862880037 / 400000000000 : ℝ) with h | h
  · exact J_448_453 t h1 h
  · exact J_453_459 t h h2

lemma J_459_461 : ∀ t : ℝ, (489075898981 / 1000000000000 : ℝ) < t → t ≤ (494373098487 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (245862249367 / 500000000000 : ℝ) with h | h
  · exact I_459 t h1 h
  · exact I_460 t h h2

lemma J_462_464 : ∀ t : ℝ, (1553192807 / 3125000000 : ℝ) < t → t ≤ (504967497499 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (499670297993 / 1000000000000 : ℝ) with h | h
  · exact I_462 t h1 h
  · exact I_463 t h h2

lemma J_461_464 : ∀ t : ℝ, (494373098487 / 1000000000000 : ℝ) < t → t ≤ (504967497499 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1553192807 / 3125000000 : ℝ) with h | h
  · exact I_461 t h1 h
  · exact J_462_464 t h h2

lemma J_459_464 : ∀ t : ℝ, (489075898981 / 1000000000000 : ℝ) < t → t ≤ (504967497499 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (494373098487 / 1000000000000 : ℝ) with h | h
  · exact J_459_461 t h1 h
  · exact J_461_464 t h h2

lemma J_465_467 : ∀ t : ℝ, (102052939401 / 200000000000 : ℝ) < t → t ≤ (16577867570387 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (515561896511 / 1000000000000 : ℝ) with h | h
  · exact I_465 t h1 h
  · exact I_466 t h h2

lemma J_464_467 : ∀ t : ℝ, (504967497499 / 1000000000000 : ℝ) < t → t ≤ (16577867570387 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (102052939401 / 200000000000 : ℝ) with h | h
  · exact I_464 t h1 h
  · exact J_465_467 t h h2

lemma J_468_470 : ∀ t : ℝ, (8328877226211 / 16000000000000 : ℝ) < t → t ≤ (33555169550949 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (16737641334457 / 32000000000000 : ℝ) with h | h
  · exact I_468 t h1 h
  · exact I_469 t h h2

lemma J_467_470 : ∀ t : ℝ, (16577867570387 / 32000000000000 : ℝ) < t → t ≤ (33555169550949 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (8328877226211 / 16000000000000 : ℝ) with h | h
  · exact I_467 t h1 h
  · exact J_468_470 t h h2

lemma J_464_470 : ∀ t : ℝ, (504967497499 / 1000000000000 : ℝ) < t → t ≤ (33555169550949 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (16577867570387 / 32000000000000 : ℝ) with h | h
  · exact J_464_467 t h1 h
  · exact J_467_470 t h h2

lemma J_459_470 : ∀ t : ℝ, (489075898981 / 1000000000000 : ℝ) < t → t ≤ (33555169550949 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (504967497499 / 1000000000000 : ℝ) with h | h
  · exact J_459_464 t h1 h
  · exact J_464_470 t h h2

lemma J_448_470 : ∀ t : ℝ, (47053570071 / 100000000000 : ℝ) < t → t ≤ (33555169550949 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (489075898981 / 1000000000000 : ℝ) with h | h
  · exact J_448_459 t h1 h
  · exact J_459_470 t h h2

lemma J_427_470 : ∀ t : ℝ, (28415256387 / 62500000000 : ℝ) < t → t ≤ (33555169550949 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (47053570071 / 100000000000 : ℝ) with h | h
  · exact J_427_448 t h1 h
  · exact J_448_470 t h h2

lemma J_470_472 : ∀ t : ℝ, (33555169550949 / 64000000000000 : ℝ) < t → t ≤ (33714943315019 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4204382054123 / 8000000000000 : ℝ) with h | h
  · exact I_470 t h1 h
  · exact I_471 t h h2

lemma J_473_475 : ∀ t : ℝ, (16897415098527 / 32000000000000 : ℝ) < t → t ≤ (8488650990281 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (33874717079089 / 64000000000000 : ℝ) with h | h
  · exact I_473 t h1 h
  · exact I_474 t h h2

lemma J_472_475 : ∀ t : ℝ, (33714943315019 / 64000000000000 : ℝ) < t → t ≤ (8488650990281 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (16897415098527 / 32000000000000 : ℝ) with h | h
  · exact I_472 t h1 h
  · exact J_473_475 t h h2

lemma J_470_475 : ∀ t : ℝ, (33555169550949 / 64000000000000 : ℝ) < t → t ≤ (8488650990281 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (33714943315019 / 64000000000000 : ℝ) with h | h
  · exact J_470_472 t h1 h
  · exact J_472_475 t h h2

lemma J_475_477 : ∀ t : ℝ, (8488650990281 / 16000000000000 : ℝ) < t → t ≤ (17057188862597 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (34034490843159 / 64000000000000 : ℝ) with h | h
  · exact I_475 t h1 h
  · exact I_476 t h h2

lemma J_478_480 : ∀ t : ℝ, (34194264607229 / 64000000000000 : ℝ) < t → t ≤ (2142134468079 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (68468416096493 / 128000000000000 : ℝ) with h | h
  · exact I_478 t h1 h
  · exact I_479 t h h2

lemma J_477_480 : ∀ t : ℝ, (17057188862597 / 32000000000000 : ℝ) < t → t ≤ (2142134468079 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (34194264607229 / 64000000000000 : ℝ) with h | h
  · exact I_477 t h1 h
  · exact J_478_480 t h h2

lemma J_475_480 : ∀ t : ℝ, (8488650990281 / 16000000000000 : ℝ) < t → t ≤ (2142134468079 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (17057188862597 / 32000000000000 : ℝ) with h | h
  · exact J_475_477 t h1 h
  · exact J_477_480 t h h2

lemma J_470_480 : ∀ t : ℝ, (33555169550949 / 64000000000000 : ℝ) < t → t ≤ (2142134468079 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (8488650990281 / 16000000000000 : ℝ) with h | h
  · exact J_470_475 t h1 h
  · exact J_475_480 t h h2

lemma J_480_482 : ∀ t : ℝ, (2142134468079 / 4000000000000 : ℝ) < t → t ≤ (34354038371299 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (68628189860563 / 128000000000000 : ℝ) with h | h
  · exact I_480 t h1 h
  · exact I_481 t h h2

lemma J_483_485 : ∀ t : ℝ, (68787963624633 / 128000000000000 : ℝ) < t → t ≤ (68947737388703 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (17216962626667 / 32000000000000 : ℝ) with h | h
  · exact I_483 t h1 h
  · exact I_484 t h h2

lemma J_482_485 : ∀ t : ℝ, (34354038371299 / 64000000000000 : ℝ) < t → t ≤ (68947737388703 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (68787963624633 / 128000000000000 : ℝ) with h | h
  · exact I_482 t h1 h
  · exact J_483_485 t h h2

lemma J_480_485 : ∀ t : ℝ, (2142134468079 / 4000000000000 : ℝ) < t → t ≤ (68947737388703 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (34354038371299 / 64000000000000 : ℝ) with h | h
  · exact J_480_482 t h1 h
  · exact J_482_485 t h h2

lemma J_486_488 : ∀ t : ℝ, (34513812135369 / 64000000000000 : ℝ) < t → t ≤ (8648424754351 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (69107511152773 / 128000000000000 : ℝ) with h | h
  · exact I_486 t h1 h
  · exact I_487 t h h2

lemma J_485_488 : ∀ t : ℝ, (68947737388703 / 128000000000000 : ℝ) < t → t ≤ (8648424754351 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (34513812135369 / 64000000000000 : ℝ) with h | h
  · exact I_485 t h1 h
  · exact J_486_488 t h h2

lemma J_489_491 : ∀ t : ℝ, (69267284916843 / 128000000000000 : ℝ) < t → t ≤ (69427058680913 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (34673585899439 / 64000000000000 : ℝ) with h | h
  · exact I_489 t h1 h
  · exact I_490 t h h2

lemma J_488_491 : ∀ t : ℝ, (8648424754351 / 16000000000000 : ℝ) < t → t ≤ (69427058680913 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (69267284916843 / 128000000000000 : ℝ) with h | h
  · exact I_488 t h1 h
  · exact J_489_491 t h h2

lemma J_485_491 : ∀ t : ℝ, (68947737388703 / 128000000000000 : ℝ) < t → t ≤ (69427058680913 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (8648424754351 / 16000000000000 : ℝ) with h | h
  · exact J_485_488 t h1 h
  · exact J_488_491 t h h2

lemma J_480_491 : ∀ t : ℝ, (2142134468079 / 4000000000000 : ℝ) < t → t ≤ (69427058680913 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (68947737388703 / 128000000000000 : ℝ) with h | h
  · exact J_480_485 t h1 h
  · exact J_485_491 t h h2

lemma J_470_491 : ∀ t : ℝ, (33555169550949 / 64000000000000 : ℝ) < t → t ≤ (69427058680913 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2142134468079 / 4000000000000 : ℝ) with h | h
  · exact J_470_480 t h1 h
  · exact J_480_491 t h h2

lemma J_491_493 : ∀ t : ℝ, (69427058680913 / 128000000000000 : ℝ) < t → t ≤ (69586832444983 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (17376736390737 / 32000000000000 : ℝ) with h | h
  · exact I_491 t h1 h
  · exact I_492 t h h2

lemma J_494_496 : ∀ t : ℝ, (34833359663509 / 64000000000000 : ℝ) < t → t ≤ (4364155818193 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (69746606209053 / 128000000000000 : ℝ) with h | h
  · exact I_494 t h1 h
  · exact I_495 t h h2

lemma J_493_496 : ∀ t : ℝ, (69586832444983 / 128000000000000 : ℝ) < t → t ≤ (4364155818193 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (34833359663509 / 64000000000000 : ℝ) with h | h
  · exact I_493 t h1 h
  · exact J_494_496 t h h2

lemma J_491_496 : ∀ t : ℝ, (69427058680913 / 128000000000000 : ℝ) < t → t ≤ (4364155818193 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (69586832444983 / 128000000000000 : ℝ) with h | h
  · exact J_491_493 t h1 h
  · exact J_493_496 t h h2

lemma J_497_499 : ∀ t : ℝ, (69906379973123 / 128000000000000 : ℝ) < t → t ≤ (70066153737193 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (34993133427579 / 64000000000000 : ℝ) with h | h
  · exact I_497 t h1 h
  · exact I_498 t h h2

lemma J_496_499 : ∀ t : ℝ, (4364155818193 / 8000000000000 : ℝ) < t → t ≤ (70066153737193 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (69906379973123 / 128000000000000 : ℝ) with h | h
  · exact I_496 t h1 h
  · exact J_497_499 t h h2

lemma J_500_502 : ∀ t : ℝ, (17536510154807 / 32000000000000 : ℝ) < t → t ≤ (8808198518421 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (35152907191649 / 64000000000000 : ℝ) with h | h
  · exact I_500 t h1 h
  · exact I_501 t h h2

lemma J_499_502 : ∀ t : ℝ, (70066153737193 / 128000000000000 : ℝ) < t → t ≤ (8808198518421 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (17536510154807 / 32000000000000 : ℝ) with h | h
  · exact I_499 t h1 h
  · exact J_500_502 t h h2

lemma J_496_502 : ∀ t : ℝ, (4364155818193 / 8000000000000 : ℝ) < t → t ≤ (8808198518421 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (70066153737193 / 128000000000000 : ℝ) with h | h
  · exact J_496_499 t h1 h
  · exact J_499_502 t h h2

lemma J_491_502 : ∀ t : ℝ, (69427058680913 / 128000000000000 : ℝ) < t → t ≤ (8808198518421 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4364155818193 / 8000000000000 : ℝ) with h | h
  · exact J_491_496 t h1 h
  · exact J_496_502 t h h2

lemma J_502_504 : ∀ t : ℝ, (8808198518421 / 16000000000000 : ℝ) < t → t ≤ (17696283918877 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (35312680955719 / 64000000000000 : ℝ) with h | h
  · exact I_502 t h1 h
  · exact I_503 t h h2

lemma J_505_507 : ∀ t : ℝ, (35472454719789 / 64000000000000 : ℝ) < t → t ≤ (35632228483859 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1111010675057 / 2000000000000 : ℝ) with h | h
  · exact I_505 t h1 h
  · exact I_506 t h h2

lemma J_504_507 : ∀ t : ℝ, (17696283918877 / 32000000000000 : ℝ) < t → t ≤ (35632228483859 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (35472454719789 / 64000000000000 : ℝ) with h | h
  · exact I_504 t h1 h
  · exact J_505_507 t h h2

lemma J_502_507 : ∀ t : ℝ, (8808198518421 / 16000000000000 : ℝ) < t → t ≤ (35632228483859 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (17696283918877 / 32000000000000 : ℝ) with h | h
  · exact J_502_504 t h1 h
  · exact J_504_507 t h h2

lemma J_508_510 : ∀ t : ℝ, (17856057682947 / 32000000000000 : ℝ) < t → t ≤ (8967972282491 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (35792002247929 / 64000000000000 : ℝ) with h | h
  · exact I_508 t h1 h
  · exact I_509 t h h2

lemma J_507_510 : ∀ t : ℝ, (35632228483859 / 64000000000000 : ℝ) < t → t ≤ (8967972282491 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (17856057682947 / 32000000000000 : ℝ) with h | h
  · exact I_507 t h1 h
  · exact J_508_510 t h h2

lemma J_511_513 : ∀ t : ℝ, (35951776011999 / 64000000000000 : ℝ) < t → t ≤ (36111549776069 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (18015831447017 / 32000000000000 : ℝ) with h | h
  · exact I_511 t h1 h
  · exact I_512 t h h2

lemma J_510_513 : ∀ t : ℝ, (8967972282491 / 16000000000000 : ℝ) < t → t ≤ (36111549776069 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (35951776011999 / 64000000000000 : ℝ) with h | h
  · exact I_510 t h1 h
  · exact J_511_513 t h h2

lemma J_507_513 : ∀ t : ℝ, (35632228483859 / 64000000000000 : ℝ) < t → t ≤ (36111549776069 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (8967972282491 / 16000000000000 : ℝ) with h | h
  · exact J_507_510 t h1 h
  · exact J_510_513 t h h2

lemma J_502_513 : ∀ t : ℝ, (8808198518421 / 16000000000000 : ℝ) < t → t ≤ (36111549776069 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (35632228483859 / 64000000000000 : ℝ) with h | h
  · exact J_502_507 t h1 h
  · exact J_507_513 t h h2

lemma J_491_513 : ∀ t : ℝ, (69427058680913 / 128000000000000 : ℝ) < t → t ≤ (36111549776069 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (8808198518421 / 16000000000000 : ℝ) with h | h
  · exact J_491_502 t h1 h
  · exact J_502_513 t h h2

lemma J_470_513 : ∀ t : ℝ, (33555169550949 / 64000000000000 : ℝ) < t → t ≤ (36111549776069 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (69427058680913 / 128000000000000 : ℝ) with h | h
  · exact J_470_491 t h1 h
  · exact J_491_513 t h h2

lemma J_427_513 : ∀ t : ℝ, (28415256387 / 62500000000 : ℝ) < t → t ≤ (36111549776069 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (33555169550949 / 64000000000000 : ℝ) with h | h
  · exact J_427_470 t h1 h
  · exact J_470_513 t h h2

lemma J_342_513 : ∀ t : ℝ, (2543485761489 / 8000000000000 : ℝ) < t → t ≤ (36111549776069 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (28415256387 / 62500000000 : ℝ) with h | h
  · exact J_342_427 t h1 h
  · exact J_427_513 t h h2

lemma J_513_515 : ∀ t : ℝ, (36111549776069 / 64000000000000 : ℝ) < t → t ≤ (18175605211087 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4523929582263 / 8000000000000 : ℝ) with h | h
  · exact I_513 t h1 h
  · exact I_514 t h h2

lemma J_516_518 : ∀ t : ℝ, (9127746046561 / 16000000000000 : ℝ) < t → t ≤ (2301908232149 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (18335378975157 / 32000000000000 : ℝ) with h | h
  · exact I_516 t h1 h
  · exact I_517 t h h2

lemma J_515_518 : ∀ t : ℝ, (18175605211087 / 32000000000000 : ℝ) < t → t ≤ (2301908232149 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9127746046561 / 16000000000000 : ℝ) with h | h
  · exact I_515 t h1 h
  · exact J_516_518 t h h2

lemma J_513_518 : ∀ t : ℝ, (36111549776069 / 64000000000000 : ℝ) < t → t ≤ (2301908232149 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (18175605211087 / 32000000000000 : ℝ) with h | h
  · exact J_513_515 t h1 h
  · exact J_515_518 t h h2

lemma J_518_520 : ∀ t : ℝ, (2301908232149 / 4000000000000 : ℝ) < t → t ≤ (9287519810631 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (18495152739227 / 32000000000000 : ℝ) with h | h
  · exact I_518 t h1 h
  · exact I_519 t h h2

lemma J_521_523 : ∀ t : ℝ, (4683703346333 / 8000000000000 : ℝ) < t → t ≤ (297724389273 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9447293574701 / 16000000000000 : ℝ) with h | h
  · exact I_521 t h1 h
  · exact I_522 t h h2

lemma J_520_523 : ∀ t : ℝ, (9287519810631 / 16000000000000 : ℝ) < t → t ≤ (297724389273 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4683703346333 / 8000000000000 : ℝ) with h | h
  · exact I_520 t h1 h
  · exact J_521_523 t h h2

lemma J_518_523 : ∀ t : ℝ, (2301908232149 / 4000000000000 : ℝ) < t → t ≤ (297724389273 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9287519810631 / 16000000000000 : ℝ) with h | h
  · exact J_518_520 t h1 h
  · exact J_520_523 t h h2

lemma J_513_523 : ∀ t : ℝ, (36111549776069 / 64000000000000 : ℝ) < t → t ≤ (297724389273 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2301908232149 / 4000000000000 : ℝ) with h | h
  · exact J_513_518 t h1 h
  · exact J_518_523 t h h2

lemma J_523_525 : ∀ t : ℝ, (297724389273 / 500000000000 : ℝ) < t → t ≤ (9595973061673 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19123153518409 / 32000000000000 : ℝ) with h | h
  · exact I_523 t h1 h
  · exact I_524 t h h2

lemma J_526_528 : ∀ t : ℝ, (19260738728283 / 32000000000000 : ℝ) < t → t ≤ (966476566661 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (38590270061503 / 64000000000000 : ℝ) with h | h
  · exact I_526 t h1 h
  · exact I_527 t h h2

lemma J_525_528 : ∀ t : ℝ, (9595973061673 / 16000000000000 : ℝ) < t → t ≤ (966476566661 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19260738728283 / 32000000000000 : ℝ) with h | h
  · exact I_525 t h1 h
  · exact J_526_528 t h h2

lemma J_523_528 : ∀ t : ℝ, (297724389273 / 500000000000 : ℝ) < t → t ≤ (966476566661 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9595973061673 / 16000000000000 : ℝ) with h | h
  · exact J_523_525 t h1 h
  · exact J_525_528 t h h2

lemma J_529_531 : ∀ t : ℝ, (38727855271377 / 64000000000000 : ℝ) < t → t ≤ (38865440481251 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19398323938157 / 32000000000000 : ℝ) with h | h
  · exact I_529 t h1 h
  · exact I_530 t h h2

lemma J_528_531 : ∀ t : ℝ, (966476566661 / 1600000000000 : ℝ) < t → t ≤ (38865440481251 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (38727855271377 / 64000000000000 : ℝ) with h | h
  · exact I_528 t h1 h
  · exact J_529_531 t h h2

lemma J_532_534 : ∀ t : ℝ, (9733558271547 / 16000000000000 : ℝ) < t → t ≤ (19535909148031 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (312024205529 / 512000000000 : ℝ) with h | h
  · exact I_532 t h1 h
  · exact I_533 t h h2

lemma J_531_534 : ∀ t : ℝ, (38865440481251 / 64000000000000 : ℝ) < t → t ≤ (19535909148031 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9733558271547 / 16000000000000 : ℝ) with h | h
  · exact I_531 t h1 h
  · exact J_532_534 t h h2

lemma J_528_534 : ∀ t : ℝ, (966476566661 / 1600000000000 : ℝ) < t → t ≤ (19535909148031 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (38865440481251 / 64000000000000 : ℝ) with h | h
  · exact J_528_531 t h1 h
  · exact J_531_534 t h h2

lemma J_523_534 : ∀ t : ℝ, (297724389273 / 500000000000 : ℝ) < t → t ≤ (19535909148031 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (966476566661 / 1600000000000 : ℝ) with h | h
  · exact J_523_528 t h1 h
  · exact J_528_534 t h h2

lemma J_513_534 : ∀ t : ℝ, (36111549776069 / 64000000000000 : ℝ) < t → t ≤ (19535909148031 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (297724389273 / 500000000000 : ℝ) with h | h
  · exact J_513_523 t h1 h
  · exact J_523_534 t h h2

lemma J_534_536 : ∀ t : ℝ, (19535909148031 / 32000000000000 : ℝ) < t → t ≤ (2450587719121 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (39140610900999 / 64000000000000 : ℝ) with h | h
  · exact I_534 t h1 h
  · exact I_535 t h h2

lemma J_537_539 : ∀ t : ℝ, (39278196110873 / 64000000000000 : ℝ) < t → t ≤ (39415781320747 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (3934698871581 / 6400000000000 : ℝ) with h | h
  · exact I_537 t h1 h
  · exact I_538 t h h2

lemma J_536_539 : ∀ t : ℝ, (2450587719121 / 4000000000000 : ℝ) < t → t ≤ (39415781320747 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (39278196110873 / 64000000000000 : ℝ) with h | h
  · exact I_536 t h1 h
  · exact J_537_539 t h h2

lemma J_534_539 : ∀ t : ℝ, (19535909148031 / 32000000000000 : ℝ) < t → t ≤ (39415781320747 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2450587719121 / 4000000000000 : ℝ) with h | h
  · exact J_534_536 t h1 h
  · exact J_536_539 t h h2

lemma J_539_541 : ∀ t : ℝ, (39415781320747 / 64000000000000 : ℝ) < t → t ≤ (39553366530621 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (9871143481421 / 16000000000000 : ℝ) with h | h
  · exact I_539 t h1 h
  · exact I_540 t h h2

lemma J_542_544 : ∀ t : ℝ, (19811079567779 / 32000000000000 : ℝ) < t → t ≤ (4969968043179 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7938190348099 / 12800000000000 : ℝ) with h | h
  · exact I_542 t h1 h
  · exact I_543 t h h2

lemma J_541_544 : ∀ t : ℝ, (39553366530621 / 64000000000000 : ℝ) < t → t ≤ (4969968043179 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19811079567779 / 32000000000000 : ℝ) with h | h
  · exact I_541 t h1 h
  · exact J_542_544 t h h2

lemma J_539_544 : ∀ t : ℝ, (39415781320747 / 64000000000000 : ℝ) < t → t ≤ (4969968043179 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (39553366530621 / 64000000000000 : ℝ) with h | h
  · exact J_539_541 t h1 h
  · exact J_541_544 t h h2

lemma J_534_544 : ∀ t : ℝ, (19535909148031 / 32000000000000 : ℝ) < t → t ≤ (4969968043179 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (39415781320747 / 64000000000000 : ℝ) with h | h
  · exact J_534_539 t h1 h
  · exact J_539_544 t h h2

lemma J_544_546 : ∀ t : ℝ, (4969968043179 / 8000000000000 : ℝ) < t → t ≤ (19948664777653 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (39828536950369 / 64000000000000 : ℝ) with h | h
  · exact I_544 t h1 h
  · exact I_545 t h h2

lemma J_547_549 : ∀ t : ℝ, (39966122160243 / 64000000000000 : ℝ) < t → t ≤ (40103707370117 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2001745738259 / 3200000000000 : ℝ) with h | h
  · exact I_547 t h1 h
  · exact I_548 t h h2

lemma J_546_549 : ∀ t : ℝ, (19948664777653 / 32000000000000 : ℝ) < t → t ≤ (40103707370117 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (39966122160243 / 64000000000000 : ℝ) with h | h
  · exact I_546 t h1 h
  · exact J_547_549 t h h2

lemma J_544_549 : ∀ t : ℝ, (4969968043179 / 8000000000000 : ℝ) < t → t ≤ (40103707370117 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19948664777653 / 32000000000000 : ℝ) with h | h
  · exact J_544_546 t h1 h
  · exact J_546_549 t h h2

lemma J_550_552 : ∀ t : ℝ, (20086249987527 / 32000000000000 : ℝ) < t → t ≤ (1259690162029 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (40241292579991 / 64000000000000 : ℝ) with h | h
  · exact I_550 t h1 h
  · exact I_551 t h h2

lemma J_549_552 : ∀ t : ℝ, (40103707370117 / 64000000000000 : ℝ) < t → t ≤ (1259690162029 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20086249987527 / 32000000000000 : ℝ) with h | h
  · exact I_549 t h1 h
  · exact J_550_552 t h h2

lemma J_553_555 : ∀ t : ℝ, (8075775557973 / 12800000000000 : ℝ) < t → t ≤ (40516462999739 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20223835197401 / 32000000000000 : ℝ) with h | h
  · exact I_553 t h1 h
  · exact I_554 t h h2

lemma J_552_555 : ∀ t : ℝ, (1259690162029 / 2000000000000 : ℝ) < t → t ≤ (40516462999739 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (8075775557973 / 12800000000000 : ℝ) with h | h
  · exact I_552 t h1 h
  · exact J_553_555 t h h2

lemma J_549_555 : ∀ t : ℝ, (40103707370117 / 64000000000000 : ℝ) < t → t ≤ (40516462999739 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1259690162029 / 2000000000000 : ℝ) with h | h
  · exact J_549_552 t h1 h
  · exact J_552_555 t h h2

lemma J_544_555 : ∀ t : ℝ, (4969968043179 / 8000000000000 : ℝ) < t → t ≤ (40516462999739 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (40103707370117 / 64000000000000 : ℝ) with h | h
  · exact J_544_549 t h1 h
  · exact J_549_555 t h h2

lemma J_534_555 : ∀ t : ℝ, (19535909148031 / 32000000000000 : ℝ) < t → t ≤ (40516462999739 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4969968043179 / 8000000000000 : ℝ) with h | h
  · exact J_534_544 t h1 h
  · exact J_544_555 t h h2

lemma J_513_555 : ∀ t : ℝ, (36111549776069 / 64000000000000 : ℝ) < t → t ≤ (40516462999739 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (19535909148031 / 32000000000000 : ℝ) with h | h
  · exact J_513_534 t h1 h
  · exact J_534_555 t h h2

lemma J_555_557 : ∀ t : ℝ, (40516462999739 / 64000000000000 : ℝ) < t → t ≤ (40654048209613 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10146313901169 / 16000000000000 : ℝ) with h | h
  · exact I_555 t h1 h
  · exact I_556 t h h2

lemma J_558_560 : ∀ t : ℝ, (814456816291 / 1280000000000 : ℝ) < t → t ≤ (5107553253053 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (40791633419487 / 64000000000000 : ℝ) with h | h
  · exact I_558 t h1 h
  · exact I_559 t h h2

lemma J_557_560 : ∀ t : ℝ, (40654048209613 / 64000000000000 : ℝ) < t → t ≤ (5107553253053 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (814456816291 / 1280000000000 : ℝ) with h | h
  · exact I_557 t h1 h
  · exact J_558_560 t h h2

lemma J_555_560 : ∀ t : ℝ, (40516462999739 / 64000000000000 : ℝ) < t → t ≤ (5107553253053 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (40654048209613 / 64000000000000 : ℝ) with h | h
  · exact J_555_557 t h1 h
  · exact J_557_560 t h h2

lemma J_560_562 : ∀ t : ℝ, (5107553253053 / 8000000000000 : ℝ) < t → t ≤ (10283899111043 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20499005617149 / 32000000000000 : ℝ) with h | h
  · exact I_560 t h1 h
  · exact I_561 t h h2

lemma J_563_565 : ∀ t : ℝ, (20636590827023 / 32000000000000 : ℝ) < t → t ≤ (20774176036897 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (517634585799 / 800000000000 : ℝ) with h | h
  · exact I_563 t h1 h
  · exact I_564 t h h2

lemma J_562_565 : ∀ t : ℝ, (10283899111043 / 16000000000000 : ℝ) < t → t ≤ (20774176036897 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20636590827023 / 32000000000000 : ℝ) with h | h
  · exact I_562 t h1 h
  · exact J_563_565 t h h2

lemma J_560_565 : ∀ t : ℝ, (5107553253053 / 8000000000000 : ℝ) < t → t ≤ (20774176036897 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10283899111043 / 16000000000000 : ℝ) with h | h
  · exact J_560_562 t h1 h
  · exact J_562_565 t h h2

lemma J_555_565 : ∀ t : ℝ, (40516462999739 / 64000000000000 : ℝ) < t → t ≤ (20774176036897 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5107553253053 / 8000000000000 : ℝ) with h | h
  · exact J_555_560 t h1 h
  · exact J_560_565 t h h2

lemma J_565_567 : ∀ t : ℝ, (20774176036897 / 32000000000000 : ℝ) < t → t ≤ (20911761246771 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10421484320917 / 16000000000000 : ℝ) with h | h
  · exact I_565 t h1 h
  · exact I_566 t h h2

lemma J_568_570 : ∀ t : ℝ, (5245138462927 / 8000000000000 : ℝ) < t → t ≤ (664241383483 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10559069530791 / 16000000000000 : ℝ) with h | h
  · exact I_568 t h1 h
  · exact I_569 t h h2

lemma J_567_570 : ∀ t : ℝ, (20911761246771 / 32000000000000 : ℝ) < t → t ≤ (664241383483 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5245138462927 / 8000000000000 : ℝ) with h | h
  · exact I_567 t h1 h
  · exact J_568_570 t h h2

lemma J_565_570 : ∀ t : ℝ, (20774176036897 / 32000000000000 : ℝ) < t → t ≤ (664241383483 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20911761246771 / 32000000000000 : ℝ) with h | h
  · exact J_565_567 t h1 h
  · exact J_567_570 t h h2

lemma J_571_573 : ∀ t : ℝ, (4261528693017 / 6400000000000 : ℝ) < t → t ≤ (21411481852343 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10679781329357 / 16000000000000 : ℝ) with h | h
  · exact I_571 t h1 h
  · exact I_572 t h h2

lemma J_570_573 : ∀ t : ℝ, (664241383483 / 1000000000000 : ℝ) < t → t ≤ (21411481852343 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4261528693017 / 6400000000000 : ℝ) with h | h
  · exact I_570 t h1 h
  · exact J_571_573 t h h2

lemma J_574_576 : ∀ t : ℝ, (5365850261493 / 8000000000000 : ℝ) < t → t ≤ (43082559672831 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (21515320239601 / 32000000000000 : ℝ) with h | h
  · exact I_574 t h1 h
  · exact I_575 t h h2

lemma J_573_576 : ∀ t : ℝ, (21411481852343 / 32000000000000 : ℝ) < t → t ≤ (43082559672831 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5365850261493 / 8000000000000 : ℝ) with h | h
  · exact I_573 t h1 h
  · exact J_574_576 t h h2

lemma J_570_576 : ∀ t : ℝ, (664241383483 / 1000000000000 : ℝ) < t → t ≤ (43082559672831 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (21411481852343 / 32000000000000 : ℝ) with h | h
  · exact J_570_573 t h1 h
  · exact J_573_576 t h h2

lemma J_565_576 : ∀ t : ℝ, (20774176036897 / 32000000000000 : ℝ) < t → t ≤ (43082559672831 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (664241383483 / 1000000000000 : ℝ) with h | h
  · exact J_565_570 t h1 h
  · exact J_570_576 t h h2

lemma J_555_576 : ∀ t : ℝ, (40516462999739 / 64000000000000 : ℝ) < t → t ≤ (43082559672831 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (20774176036897 / 32000000000000 : ℝ) with h | h
  · exact J_555_565 t h1 h
  · exact J_565_576 t h h2

lemma J_576_578 : ∀ t : ℝ, (43082559672831 / 64000000000000 : ℝ) < t → t ≤ (43186398060089 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2156723943323 / 3200000000000 : ℝ) with h | h
  · exact I_576 t h1 h
  · exact I_577 t h h2

lemma J_579_581 : ∀ t : ℝ, (21619158626859 / 32000000000000 : ℝ) < t → t ≤ (2708884727561 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (43290236447347 / 64000000000000 : ℝ) with h | h
  · exact I_579 t h1 h
  · exact I_580 t h h2

lemma J_578_581 : ∀ t : ℝ, (43186398060089 / 64000000000000 : ℝ) < t → t ≤ (2708884727561 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (21619158626859 / 32000000000000 : ℝ) with h | h
  · exact I_578 t h1 h
  · exact J_579_581 t h h2

lemma J_576_581 : ∀ t : ℝ, (43082559672831 / 64000000000000 : ℝ) < t → t ≤ (2708884727561 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (43186398060089 / 64000000000000 : ℝ) with h | h
  · exact J_576_578 t h1 h
  · exact J_578_581 t h h2

lemma J_582_584 : ∀ t : ℝ, (8678814966921 / 12800000000000 : ℝ) < t → t ≤ (43497913221863 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (21722997014117 / 32000000000000 : ℝ) with h | h
  · exact I_582 t h1 h
  · exact I_583 t h h2

lemma J_581_584 : ∀ t : ℝ, (2708884727561 / 4000000000000 : ℝ) < t → t ≤ (43497913221863 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (8678814966921 / 12800000000000 : ℝ) with h | h
  · exact I_581 t h1 h
  · exact J_582_584 t h h2

lemma J_585_587 : ∀ t : ℝ, (10887458103873 / 16000000000000 : ℝ) < t → t ≤ (174614683211 / 256000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (43601751609121 / 64000000000000 : ℝ) with h | h
  · exact I_585 t h1 h
  · exact I_586 t h h2

lemma J_584_587 : ∀ t : ℝ, (43497913221863 / 64000000000000 : ℝ) < t → t ≤ (174614683211 / 256000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10887458103873 / 16000000000000 : ℝ) with h | h
  · exact I_584 t h1 h
  · exact J_585_587 t h h2

lemma J_581_587 : ∀ t : ℝ, (2708884727561 / 4000000000000 : ℝ) < t → t ≤ (174614683211 / 256000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (43497913221863 / 64000000000000 : ℝ) with h | h
  · exact J_581_584 t h1 h
  · exact J_584_587 t h h2

lemma J_576_587 : ∀ t : ℝ, (43082559672831 / 64000000000000 : ℝ) < t → t ≤ (174614683211 / 256000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2708884727561 / 4000000000000 : ℝ) with h | h
  · exact J_576_581 t h1 h
  · exact J_581_587 t h h2

lemma J_587_589 : ∀ t : ℝ, (174614683211 / 256000000000 : ℝ) < t → t ≤ (5469688648751 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (43705589996379 / 64000000000000 : ℝ) with h | h
  · exact I_587 t h1 h
  · exact I_588 t h h2

lemma J_590_592 : ∀ t : ℝ, (43809428383637 / 64000000000000 : ℝ) < t → t ≤ (8782653354179 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (21930673788633 / 32000000000000 : ℝ) with h | h
  · exact I_590 t h1 h
  · exact I_591 t h h2

lemma J_589_592 : ∀ t : ℝ, (5469688648751 / 8000000000000 : ℝ) < t → t ≤ (8782653354179 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (43809428383637 / 64000000000000 : ℝ) with h | h
  · exact I_589 t h1 h
  · exact J_590_592 t h h2

lemma J_587_592 : ∀ t : ℝ, (174614683211 / 256000000000 : ℝ) < t → t ≤ (8782653354179 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5469688648751 / 8000000000000 : ℝ) with h | h
  · exact J_587_589 t h1 h
  · exact J_589_592 t h h2

lemma J_593_595 : ∀ t : ℝ, (10991296491131 / 16000000000000 : ℝ) < t → t ≤ (22034512175891 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (44017105158153 / 64000000000000 : ℝ) with h | h
  · exact I_593 t h1 h
  · exact I_594 t h h2

lemma J_592_595 : ∀ t : ℝ, (8782653354179 / 12800000000000 : ℝ) < t → t ≤ (22034512175891 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (10991296491131 / 16000000000000 : ℝ) with h | h
  · exact I_592 t h1 h
  · exact J_593_595 t h h2

lemma J_596_598 : ∀ t : ℝ, (44120943545411 / 64000000000000 : ℝ) < t → t ≤ (44224781932669 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (276080392119 / 400000000000 : ℝ) with h | h
  · exact I_596 t h1 h
  · exact I_597 t h h2

lemma J_595_598 : ∀ t : ℝ, (22034512175891 / 32000000000000 : ℝ) < t → t ≤ (44224781932669 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (44120943545411 / 64000000000000 : ℝ) with h | h
  · exact I_595 t h1 h
  · exact J_596_598 t h h2

lemma J_592_598 : ∀ t : ℝ, (8782653354179 / 12800000000000 : ℝ) < t → t ≤ (44224781932669 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (22034512175891 / 32000000000000 : ℝ) with h | h
  · exact J_592_595 t h1 h
  · exact J_595_598 t h h2

lemma J_587_598 : ∀ t : ℝ, (174614683211 / 256000000000 : ℝ) < t → t ≤ (44224781932669 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (8782653354179 / 12800000000000 : ℝ) with h | h
  · exact J_587_592 t h1 h
  · exact J_592_598 t h h2

lemma J_576_598 : ∀ t : ℝ, (43082559672831 / 64000000000000 : ℝ) < t → t ≤ (44224781932669 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (174614683211 / 256000000000 : ℝ) with h | h
  · exact J_576_587 t h1 h
  · exact J_587_598 t h h2

lemma J_555_598 : ∀ t : ℝ, (40516462999739 / 64000000000000 : ℝ) < t → t ≤ (44224781932669 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (43082559672831 / 64000000000000 : ℝ) with h | h
  · exact J_555_576 t h1 h
  · exact J_576_598 t h h2

lemma J_513_598 : ∀ t : ℝ, (36111549776069 / 64000000000000 : ℝ) < t → t ≤ (44224781932669 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (40516462999739 / 64000000000000 : ℝ) with h | h
  · exact J_513_555 t h1 h
  · exact J_555_598 t h h2

lemma J_598_600 : ∀ t : ℝ, (44224781932669 / 64000000000000 : ℝ) < t → t ≤ (44328620319927 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (22138350563149 / 32000000000000 : ℝ) with h | h
  · exact I_598 t h1 h
  · exact I_599 t h h2

lemma J_601_603 : ∀ t : ℝ, (11095134878389 / 16000000000000 : ℝ) < t → t ≤ (22242188950407 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (8886491741437 / 12800000000000 : ℝ) with h | h
  · exact I_601 t h1 h
  · exact I_602 t h h2

lemma J_600_603 : ∀ t : ℝ, (44328620319927 / 64000000000000 : ℝ) < t → t ≤ (22242188950407 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11095134878389 / 16000000000000 : ℝ) with h | h
  · exact I_600 t h1 h
  · exact J_601_603 t h h2

lemma J_598_603 : ∀ t : ℝ, (44224781932669 / 64000000000000 : ℝ) < t → t ≤ (22242188950407 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (44328620319927 / 64000000000000 : ℝ) with h | h
  · exact J_598_600 t h1 h
  · exact J_600_603 t h h2

lemma J_603_605 : ∀ t : ℝ, (22242188950407 / 32000000000000 : ℝ) < t → t ≤ (4469205467533 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5573527036009 / 8000000000000 : ℝ) with h | h
  · exact I_603 t h1 h
  · exact I_604 t h h2

lemma J_606_608 : ∀ t : ℝ, (11198973265647 / 16000000000000 : ℝ) < t → t ≤ (2812723114819 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (22449865724923 / 32000000000000 : ℝ) with h | h
  · exact I_606 t h1 h
  · exact I_607 t h h2

lemma J_605_608 : ∀ t : ℝ, (4469205467533 / 6400000000000 : ℝ) < t → t ≤ (2812723114819 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11198973265647 / 16000000000000 : ℝ) with h | h
  · exact I_605 t h1 h
  · exact J_606_608 t h h2

lemma J_603_608 : ∀ t : ℝ, (22242188950407 / 32000000000000 : ℝ) < t → t ≤ (2812723114819 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4469205467533 / 6400000000000 : ℝ) with h | h
  · exact J_603_605 t h1 h
  · exact J_605_608 t h h2

lemma J_598_608 : ∀ t : ℝ, (44224781932669 / 64000000000000 : ℝ) < t → t ≤ (2812723114819 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (22242188950407 / 32000000000000 : ℝ) with h | h
  · exact J_598_603 t h1 h
  · exact J_603_608 t h h2

lemma J_608_610 : ∀ t : ℝ, (2812723114819 / 4000000000000 : ℝ) < t → t ≤ (2260562330581 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (22553704112181 / 32000000000000 : ℝ) with h | h
  · exact I_608 t h1 h
  · exact I_609 t h h2

lemma J_611_613 : ∀ t : ℝ, (22657542499439 / 32000000000000 : ℝ) < t → t ≤ (22761380886697 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5677365423267 / 8000000000000 : ℝ) with h | h
  · exact I_611 t h1 h
  · exact I_612 t h h2

lemma J_610_613 : ∀ t : ℝ, (2260562330581 / 3200000000000 : ℝ) < t → t ≤ (22761380886697 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (22657542499439 / 32000000000000 : ℝ) with h | h
  · exact I_610 t h1 h
  · exact J_611_613 t h h2

lemma J_608_613 : ∀ t : ℝ, (2812723114819 / 4000000000000 : ℝ) < t → t ≤ (22761380886697 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2260562330581 / 3200000000000 : ℝ) with h | h
  · exact J_608_610 t h1 h
  · exact J_610_613 t h h2

lemma J_614_616 : ∀ t : ℝ, (11406650040163 / 16000000000000 : ℝ) < t → t ≤ (11489045952349 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (89520072139 / 125000000000 : ℝ) with h | h
  · exact I_614 t h1 h
  · exact I_615 t h h2

lemma J_613_616 : ∀ t : ℝ, (22761380886697 / 32000000000000 : ℝ) < t → t ≤ (11489045952349 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11406650040163 / 16000000000000 : ℝ) with h | h
  · exact I_613 t h1 h
  · exact J_614_616 t h h2

lemma J_617_619 : ∀ t : ℝ, (4601713724651 / 6400000000000 : ℝ) < t → t ≤ (23069522060369 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5759761335453 / 8000000000000 : ℝ) with h | h
  · exact I_617 t h1 h
  · exact I_618 t h h2

lemma J_616_619 : ∀ t : ℝ, (11489045952349 / 16000000000000 : ℝ) < t → t ≤ (23069522060369 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4601713724651 / 6400000000000 : ℝ) with h | h
  · exact I_616 t h1 h
  · exact J_617_619 t h h2

lemma J_613_619 : ∀ t : ℝ, (22761380886697 / 32000000000000 : ℝ) < t → t ≤ (23069522060369 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11489045952349 / 16000000000000 : ℝ) with h | h
  · exact J_613_616 t h1 h
  · exact J_616_619 t h h2

lemma J_608_619 : ∀ t : ℝ, (2812723114819 / 4000000000000 : ℝ) < t → t ≤ (23069522060369 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (22761380886697 / 32000000000000 : ℝ) with h | h
  · exact J_608_613 t h1 h
  · exact J_613_619 t h h2

lemma J_598_619 : ∀ t : ℝ, (44224781932669 / 64000000000000 : ℝ) < t → t ≤ (23069522060369 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2812723114819 / 4000000000000 : ℝ) with h | h
  · exact J_598_608 t h1 h
  · exact J_608_619 t h h2

lemma J_619_621 : ∀ t : ℝ, (23069522060369 / 32000000000000 : ℝ) < t → t ≤ (23130475497483 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11549999389463 / 16000000000000 : ℝ) with h | h
  · exact I_619 t h1 h
  · exact I_620 t h h2

lemma J_622_624 : ∀ t : ℝ, (579023805401 / 800000000000 : ℝ) < t → t ≤ (11610952826577 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23191428934597 / 32000000000000 : ℝ) with h | h
  · exact I_622 t h1 h
  · exact I_623 t h h2

lemma J_621_624 : ∀ t : ℝ, (23130475497483 / 32000000000000 : ℝ) < t → t ≤ (11610952826577 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (579023805401 / 800000000000 : ℝ) with h | h
  · exact I_621 t h1 h
  · exact J_622_624 t h h2

lemma J_619_624 : ∀ t : ℝ, (23069522060369 / 32000000000000 : ℝ) < t → t ≤ (11610952826577 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23130475497483 / 32000000000000 : ℝ) with h | h
  · exact J_619_621 t h1 h
  · exact J_621_624 t h h2

lemma J_625_627 : ∀ t : ℝ, (23252382371711 / 32000000000000 : ℝ) < t → t ≤ (932533432353 / 1280000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5820714772567 / 8000000000000 : ℝ) with h | h
  · exact I_625 t h1 h
  · exact I_626 t h h2

lemma J_624_627 : ∀ t : ℝ, (11610952826577 / 16000000000000 : ℝ) < t → t ≤ (932533432353 / 1280000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23252382371711 / 32000000000000 : ℝ) with h | h
  · exact I_624 t h1 h
  · exact J_625_627 t h h2

lemma J_628_630 : ∀ t : ℝ, (11671906263691 / 16000000000000 : ℝ) < t → t ≤ (1462797872781 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23374289245939 / 32000000000000 : ℝ) with h | h
  · exact I_628 t h1 h
  · exact I_629 t h h2

lemma J_627_630 : ∀ t : ℝ, (932533432353 / 1280000000000 : ℝ) < t → t ≤ (1462797872781 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11671906263691 / 16000000000000 : ℝ) with h | h
  · exact I_627 t h1 h
  · exact J_628_630 t h h2

lemma J_624_630 : ∀ t : ℝ, (11610952826577 / 16000000000000 : ℝ) < t → t ≤ (1462797872781 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (932533432353 / 1280000000000 : ℝ) with h | h
  · exact J_624_627 t h1 h
  · exact J_627_630 t h h2

lemma J_619_630 : ∀ t : ℝ, (23069522060369 / 32000000000000 : ℝ) < t → t ≤ (1462797872781 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11610952826577 / 16000000000000 : ℝ) with h | h
  · exact J_619_624 t h1 h
  · exact J_624_630 t h h2

lemma J_630_632 : ∀ t : ℝ, (1462797872781 / 2000000000000 : ℝ) < t → t ≤ (2346571940161 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23435242683053 / 32000000000000 : ℝ) with h | h
  · exact I_630 t h1 h
  · exact I_631 t h h2

lemma J_633_635 : ∀ t : ℝ, (23496196120167 / 32000000000000 : ℝ) < t → t ≤ (23557149557281 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (5881668209681 / 8000000000000 : ℝ) with h | h
  · exact I_633 t h1 h
  · exact I_634 t h h2

lemma J_632_635 : ∀ t : ℝ, (2346571940161 / 3200000000000 : ℝ) < t → t ≤ (23557149557281 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23496196120167 / 32000000000000 : ℝ) with h | h
  · exact I_632 t h1 h
  · exact J_633_635 t h h2

lemma J_630_635 : ∀ t : ℝ, (1462797872781 / 2000000000000 : ℝ) < t → t ≤ (23557149557281 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2346571940161 / 3200000000000 : ℝ) with h | h
  · exact J_630_632 t h1 h
  · exact J_632_635 t h h2

lemma J_636_638 : ∀ t : ℝ, (11793813137919 / 16000000000000 : ℝ) < t → t ≤ (2956072464119 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4723620598879 / 6400000000000 : ℝ) with h | h
  · exact I_636 t h1 h
  · exact I_637 t h h2

lemma J_635_638 : ∀ t : ℝ, (23557149557281 / 32000000000000 : ℝ) < t → t ≤ (2956072464119 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11793813137919 / 16000000000000 : ℝ) with h | h
  · exact I_635 t h1 h
  · exact J_636_638 t h h2

lemma J_639_641 : ∀ t : ℝ, (23679056431509 / 32000000000000 : ℝ) < t → t ≤ (23740009868623 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11854766575033 / 16000000000000 : ℝ) with h | h
  · exact I_639 t h1 h
  · exact I_640 t h h2

lemma J_638_641 : ∀ t : ℝ, (2956072464119 / 4000000000000 : ℝ) < t → t ≤ (23740009868623 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23679056431509 / 32000000000000 : ℝ) with h | h
  · exact I_638 t h1 h
  · exact J_639_641 t h h2

lemma J_635_641 : ∀ t : ℝ, (23557149557281 / 32000000000000 : ℝ) < t → t ≤ (23740009868623 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2956072464119 / 4000000000000 : ℝ) with h | h
  · exact J_635_638 t h1 h
  · exact J_638_641 t h h2

lemma J_630_641 : ∀ t : ℝ, (1462797872781 / 2000000000000 : ℝ) < t → t ≤ (23740009868623 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23557149557281 / 32000000000000 : ℝ) with h | h
  · exact J_630_635 t h1 h
  · exact J_635_641 t h h2

lemma J_619_641 : ∀ t : ℝ, (23069522060369 / 32000000000000 : ℝ) < t → t ≤ (23740009868623 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1462797872781 / 2000000000000 : ℝ) with h | h
  · exact J_619_630 t h1 h
  · exact J_630_641 t h h2

lemma J_598_641 : ∀ t : ℝ, (44224781932669 / 64000000000000 : ℝ) < t → t ≤ (23740009868623 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23069522060369 / 32000000000000 : ℝ) with h | h
  · exact J_598_619 t h1 h
  · exact J_619_641 t h h2

lemma J_641_643 : ∀ t : ℝ, (23740009868623 / 32000000000000 : ℝ) < t → t ≤ (23800963305737 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1188524329359 / 1600000000000 : ℝ) with h | h
  · exact I_641 t h1 h
  · exact I_642 t h h2

lemma J_644_646 : ∀ t : ℝ, (11915720012147 / 16000000000000 : ℝ) < t → t ≤ (765809953469387 / 1024000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (746637295669 / 1000000000000 : ℝ) with h | h
  · exact I_644 t h1 h
  · exact I_645 t h h2

lemma J_643_646 : ∀ t : ℝ, (23800963305737 / 32000000000000 : ℝ) < t → t ≤ (765809953469387 / 1024000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (11915720012147 / 16000000000000 : ℝ) with h | h
  · exact I_643 t h1 h
  · exact J_644_646 t h h2

lemma J_641_646 : ∀ t : ℝ, (23740009868623 / 32000000000000 : ℝ) < t → t ≤ (765809953469387 / 1024000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23800963305737 / 32000000000000 : ℝ) with h | h
  · exact J_641_643 t h1 h
  · exact J_643_646 t h h2

lemma J_646_648 : ∀ t : ℝ, (765809953469387 / 1024000000000000 : ℝ) < t → t ≤ (768316678878049 / 1024000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (383531658086859 / 512000000000000 : ℝ) with h | h
  · exact I_646 t h1 h
  · exact I_647 t h h2

lemma J_649_651 : ∀ t : ℝ, (38478502079119 / 51200000000000 : ℝ) < t → t ≤ (386038383495521 / 512000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (770823404286711 / 1024000000000000 : ℝ) with h | h
  · exact I_649 t h1 h
  · exact I_650 t h h2

lemma J_648_651 : ∀ t : ℝ, (768316678878049 / 1024000000000000 : ℝ) < t → t ≤ (386038383495521 / 512000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (38478502079119 / 51200000000000 : ℝ) with h | h
  · exact I_648 t h1 h
  · exact J_649_651 t h h2

lemma J_646_651 : ∀ t : ℝ, (765809953469387 / 1024000000000000 : ℝ) < t → t ≤ (386038383495521 / 512000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (768316678878049 / 1024000000000000 : ℝ) with h | h
  · exact J_646_648 t h1 h
  · exact J_648_651 t h h2

lemma J_641_651 : ∀ t : ℝ, (23740009868623 / 32000000000000 : ℝ) < t → t ≤ (386038383495521 / 512000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (765809953469387 / 1024000000000000 : ℝ) with h | h
  · exact J_641_646 t h1 h
  · exact J_646_651 t h h2

lemma J_651_653 : ∀ t : ℝ, (386038383495521 / 512000000000000 : ℝ) < t → t ≤ (96822936549963 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (773330129695373 / 1024000000000000 : ℝ) with h | h
  · exact I_651 t h1 h
  · exact I_652 t h h2

lemma J_654_656 : ∀ t : ℝ, (155167371020807 / 204800000000000 : ℝ) < t → t ≤ (194899235804257 / 256000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (388545108904183 / 512000000000000 : ℝ) with h | h
  · exact I_654 t h1 h
  · exact I_655 t h h2

lemma J_653_656 : ∀ t : ℝ, (96822936549963 / 128000000000000 : ℝ) < t → t ≤ (194899235804257 / 256000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (155167371020807 / 204800000000000 : ℝ) with h | h
  · exact I_653 t h1 h
  · exact J_654_656 t h h2

lemma J_651_656 : ∀ t : ℝ, (386038383495521 / 512000000000000 : ℝ) < t → t ≤ (194899235804257 / 256000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (96822936549963 / 128000000000000 : ℝ) with h | h
  · exact J_651_653 t h1 h
  · exact J_653_656 t h h2

lemma J_657_659 : ∀ t : ℝ, (78210366862569 / 102400000000000 : ℝ) < t → t ≤ (393558559721507 / 512000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (49038149627147 / 64000000000000 : ℝ) with h | h
  · exact I_657 t h1 h
  · exact I_658 t h h2

lemma J_656_659 : ∀ t : ℝ, (194899235804257 / 256000000000000 : ℝ) < t → t ≤ (393558559721507 / 512000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (78210366862569 / 102400000000000 : ℝ) with h | h
  · exact I_656 t h1 h
  · exact J_657_659 t h h2

lemma J_660_662 : ∀ t : ℝ, (197405961212919 / 256000000000000 : ℝ) < t → t ≤ (794637295669 / 1024000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (396065285130169 / 512000000000000 : ℝ) with h | h
  · exact I_660 t h1 h
  · exact I_661 t h h2

lemma J_659_662 : ∀ t : ℝ, (393558559721507 / 512000000000000 : ℝ) < t → t ≤ (794637295669 / 1024000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (197405961212919 / 256000000000000 : ℝ) with h | h
  · exact I_659 t h1 h
  · exact J_660_662 t h h2

lemma J_656_662 : ∀ t : ℝ, (194899235804257 / 256000000000000 : ℝ) < t → t ≤ (794637295669 / 1024000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (393558559721507 / 512000000000000 : ℝ) with h | h
  · exact J_656_659 t h1 h
  · exact J_659_662 t h h2

lemma J_651_662 : ∀ t : ℝ, (386038383495521 / 512000000000000 : ℝ) < t → t ≤ (794637295669 / 1024000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (194899235804257 / 256000000000000 : ℝ) with h | h
  · exact J_651_656 t h1 h
  · exact J_656_662 t h h2

lemma J_641_662 : ∀ t : ℝ, (23740009868623 / 32000000000000 : ℝ) < t → t ≤ (794637295669 / 1024000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (386038383495521 / 512000000000000 : ℝ) with h | h
  · exact J_641_651 t h1 h
  · exact J_651_662 t h h2

lemma J_662_664 : ∀ t : ℝ, (794637295669 / 1024000000000 : ℝ) < t → t ≤ (199912686621581 / 256000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (398572010538831 / 512000000000000 : ℝ) with h | h
  · exact I_662 t h1 h
  · exact I_663 t h h2

lemma J_665_667 : ∀ t : ℝ, (25145756165739 / 32000000000000 : ℝ) < t → t ≤ (101836387367287 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (202419412030243 / 256000000000000 : ℝ) with h | h
  · exact I_665 t h1 h
  · exact I_666 t h h2

lemma J_664_667 : ∀ t : ℝ, (199912686621581 / 256000000000000 : ℝ) < t → t ≤ (101836387367287 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (25145756165739 / 32000000000000 : ℝ) with h | h
  · exact I_664 t h1 h
  · exact J_665_667 t h h2

lemma J_662_667 : ∀ t : ℝ, (794637295669 / 1024000000000 : ℝ) < t → t ≤ (101836387367287 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (199912686621581 / 256000000000000 : ℝ) with h | h
  · exact J_662_664 t h1 h
  · exact J_664_667 t h h2

lemma J_668_670 : ∀ t : ℝ, (40985227487781 / 51200000000000 : ℝ) < t → t ≤ (104343112775949 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (51544875035809 / 64000000000000 : ℝ) with h | h
  · exact I_668 t h1 h
  · exact I_669 t h h2

lemma J_667_670 : ∀ t : ℝ, (101836387367287 / 128000000000000 : ℝ) < t → t ≤ (104343112775949 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (40985227487781 / 51200000000000 : ℝ) with h | h
  · exact I_667 t h1 h
  · exact J_668_670 t h h2

lemma J_671_673 : ∀ t : ℝ, (2639911887007 / 3200000000000 : ℝ) < t → t ≤ (54051600444471 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (106849838184611 / 128000000000000 : ℝ) with h | h
  · exact I_671 t h1 h
  · exact I_672 t h h2

lemma J_670_673 : ∀ t : ℝ, (104343112775949 / 128000000000000 : ℝ) < t → t ≤ (54051600444471 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2639911887007 / 3200000000000 : ℝ) with h | h
  · exact I_670 t h1 h
  · exact J_671_673 t h h2

lemma J_667_673 : ∀ t : ℝ, (101836387367287 / 128000000000000 : ℝ) < t → t ≤ (54051600444471 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (104343112775949 / 128000000000000 : ℝ) with h | h
  · exact J_667_670 t h1 h
  · exact J_670_673 t h h2

lemma J_662_673 : ∀ t : ℝ, (794637295669 / 1024000000000 : ℝ) < t → t ≤ (54051600444471 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (101836387367287 / 128000000000000 : ℝ) with h | h
  · exact J_662_667 t h1 h
  · exact J_667_673 t h h2

lemma J_673_675 : ∀ t : ℝ, (54051600444471 / 64000000000000 : ℝ) < t → t ≤ (56558325853133 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (27652481574401 / 32000000000000 : ℝ) with h | h
  · exact I_673 t h1 h
  · exact I_674 t h h2

lemma J_676_678 : ∀ t : ℝ, (7226461069683 / 8000000000000 : ℝ) < t → t ≤ (15706284843697 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (30159206983063 / 32000000000000 : ℝ) with h | h
  · exact I_676 t h1 h
  · exact I_677 t h h2

lemma J_675_678 : ∀ t : ℝ, (56558325853133 / 64000000000000 : ℝ) < t → t ≤ (15706284843697 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (7226461069683 / 8000000000000 : ℝ) with h | h
  · exact I_675 t h1 h
  · exact J_676_678 t h h2

lemma J_673_678 : ∀ t : ℝ, (54051600444471 / 64000000000000 : ℝ) < t → t ≤ (15706284843697 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (56558325853133 / 64000000000000 : ℝ) with h | h
  · exact J_673_675 t h1 h
  · exact J_675_678 t h h2

lemma J_679_681 : ∀ t : ℝ, (4239911887007 / 4000000000000 : ℝ) < t → t ≤ (1946637295669 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (18213010252359 / 16000000000000 : ℝ) with h | h
  · exact I_679 t h1 h
  · exact I_680 t h h2

lemma J_678_681 : ∀ t : ℝ, (15706284843697 / 16000000000000 : ℝ) < t → t ≤ (1946637295669 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (4239911887007 / 4000000000000 : ℝ) with h | h
  · exact I_678 t h1 h
  · exact J_679_681 t h h2

lemma J_682_684 : ∀ t : ℝ, (2746637295669 / 2000000000000 : ℝ) < t → t ≤ (2 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (6746637295669 / 4000000000000 : ℝ) with h | h
  · exact I_682 t h1 h
  · exact I_683 t h h2

lemma J_681_684 : ∀ t : ℝ, (1946637295669 / 1600000000000 : ℝ) < t → t ≤ (2 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2746637295669 / 2000000000000 : ℝ) with h | h
  · exact I_681 t h1 h
  · exact J_682_684 t h h2

lemma J_678_684 : ∀ t : ℝ, (15706284843697 / 16000000000000 : ℝ) < t → t ≤ (2 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (1946637295669 / 1600000000000 : ℝ) with h | h
  · exact J_678_681 t h1 h
  · exact J_681_684 t h h2

lemma J_673_684 : ∀ t : ℝ, (54051600444471 / 64000000000000 : ℝ) < t → t ≤ (2 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (15706284843697 / 16000000000000 : ℝ) with h | h
  · exact J_673_678 t h1 h
  · exact J_678_684 t h h2

lemma J_662_684 : ∀ t : ℝ, (794637295669 / 1024000000000 : ℝ) < t → t ≤ (2 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (54051600444471 / 64000000000000 : ℝ) with h | h
  · exact J_662_673 t h1 h
  · exact J_673_684 t h h2

lemma J_641_684 : ∀ t : ℝ, (23740009868623 / 32000000000000 : ℝ) < t → t ≤ (2 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (794637295669 / 1024000000000 : ℝ) with h | h
  · exact J_641_662 t h1 h
  · exact J_662_684 t h h2

lemma J_598_684 : ∀ t : ℝ, (44224781932669 / 64000000000000 : ℝ) < t → t ≤ (2 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (23740009868623 / 32000000000000 : ℝ) with h | h
  · exact J_598_641 t h1 h
  · exact J_641_684 t h h2

lemma J_513_684 : ∀ t : ℝ, (36111549776069 / 64000000000000 : ℝ) < t → t ≤ (2 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (44224781932669 / 64000000000000 : ℝ) with h | h
  · exact J_513_598 t h1 h
  · exact J_598_684 t h h2

lemma J_342_684 : ∀ t : ℝ, (2543485761489 / 8000000000000 : ℝ) < t → t ≤ (2 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (36111549776069 / 64000000000000 : ℝ) with h | h
  · exact J_342_513 t h1 h
  · exact J_513_684 t h h2

lemma J_0_684 : ∀ t : ℝ, (0 : ℝ) < t → t ≤ (2 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  rcases le_or_gt t (2543485761489 / 8000000000000 : ℝ) with h | h
  · exact J_0_342 t h1 h
  · exact J_342_684 t h h2

theorem potential_ineq_le_two : ∀ t : ℝ, 0 < t → t ≤ (2 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := J_0_684

end Apery
