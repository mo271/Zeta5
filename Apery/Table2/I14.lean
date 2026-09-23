import Apery.Table2.U14
import Apery.Table2.U15

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_560 : (25738408495496259445718755170118923 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (5107553253053 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5107553253053 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (79902700619667 / 100000000000000 : ℝ) ≤ Real.sqrt (5107553253053 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5107553253053 / 8000000000000 : ℝ) ≤ (19975675154917 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (19975675154917 / 25000000000000 : ℝ) = (25000000000000 / 19975675154917 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (79902700619667 / 100000000000000 : ℝ) = (2500000000000 / 26634233539889 : ℝ) := by norm_num
  have hL1 : (24687355328449 / 50000000000000 : ℝ) ≤ Real.log (1 + (5107553253053 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5107553253053 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-8798983446187 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (79902700619668 / 228001724856801 : ℝ) ≤ (337073685830853 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (19975675154917 / 25000000000000 : ℝ) ≤ (337073685830853 / 500000000000000 : ℝ) := by
    have hw : (128001724856801 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (19975675154917 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (19975675154917 / 25000000000000 : ℝ) / (1 + (128001724856801 / 100000000000000 : ℝ)) = (79902700619668 / 228001724856801 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89664895513319061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 19975675154917 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 19975675154917 : ℝ) = (19975675154917 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 26634233539889 : ℝ) ≤ (93589946885721 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89664895513319061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (19975675154917 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (79902700619667 / 100000000000000 : ℝ)) ≤ (93589946885721 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_560 : ∀ t : ℝ, (5107553253053 / 8000000000000 : ℝ) < t → t ≤ (20499005617149 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-74870660352842710512773431 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20499005617149 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_561
  have hV : (25738408495496259445718755170118923 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5107553253053 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_560 (Vfield_monotoneOn (show (5107553253053 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5107553253053 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_561 : (25785140028369923227448138381507003 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (20499005617149 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20499005617149 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (80037111737987 / 100000000000000 : ℝ) ≤ Real.sqrt (20499005617149 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20499005617149 / 32000000000000 : ℝ) ≤ (20009277934497 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20009277934497 / 25000000000000 : ℝ) = (25000000000000 / 20009277934497 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (80037111737987 / 100000000000000 : ℝ) = (7500000000000 / 80037111737987 : ℝ) := by norm_num
  have hL1 : (24752916299637 / 50000000000000 : ℝ) ≤ Real.log (1 + (20499005617149 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20499005617149 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-10915423458319 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (6669759311499 / 19007139295490 : ℝ) ≤ (337483596173139 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20009277934497 / 25000000000000 : ℝ) ≤ (337483596173139 / 500000000000000 : ℝ) := by
    have hw : (3202141788647 / 2500000000000 : ℝ) ≤ Real.sqrt (1 + (20009277934497 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (20009277934497 / 25000000000000 : ℝ) / (1 + (3202141788647 / 2500000000000 : ℝ)) = (6669759311499 / 19007139295490 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89582913444861861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 20009277934497 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 20009277934497 : ℝ) = (20009277934497 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 80037111737987 : ℝ) ≤ (46716844782709 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89582913444861861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20009277934497 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (80037111737987 / 100000000000000 : ℝ)) ≤ (46716844782709 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_561 : ∀ t : ℝ, (20499005617149 / 32000000000000 : ℝ) < t → t ≤ (10283899111043 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-74447121075095110967487169 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10283899111043 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_562
  have hV : (25785140028369923227448138381507003 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20499005617149 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_561 (Vfield_monotoneOn (show (20499005617149 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20499005617149 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_562 : (25831794778308223013855632523706589 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (10283899111043 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10283899111043 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (80171297509781 / 100000000000000 : ℝ) ≤ Real.sqrt (10283899111043 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10283899111043 / 16000000000000 : ℝ) ≤ (40085648754891 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (40085648754891 / 50000000000000 : ℝ) = (50000000000000 / 40085648754891 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (80171297509781 / 100000000000000 : ℝ) = (7500000000000 / 80171297509781 : ℝ) := by norm_num
  have hL1 : (49636782837129 / 100000000000000 : ℝ) ≤ Real.log (1 + (10283899111043 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10283899111043 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-4332957712721 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (80171297509782 / 228169563252755 : ℝ) ≤ (67578456680501 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (40085648754891 / 50000000000000 : ℝ) ≤ (67578456680501 / 100000000000000 : ℝ) := by
    have hw : (25633912650551 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (40085648754891 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (40085648754891 / 50000000000000 : ℝ) / (1 + (25633912650551 / 20000000000000 : ℝ)) = (80171297509782 / 228169563252755 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89501175998988661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 40085648754891 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 40085648754891 : ℝ) = (40085648754891 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 80171297509781 : ℝ) ≤ (93278212305391 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89501175998988661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (40085648754891 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (80171297509781 / 100000000000000 : ℝ)) ≤ (93278212305391 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_562 : ∀ t : ℝ, (10283899111043 / 16000000000000 : ℝ) < t → t ≤ (20636590827023 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-37013612939416703100287277 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20636590827023 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_563
  have hV : (25831794778308223013855632523706589 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10283899111043 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_562 (Vfield_monotoneOn (show (10283899111043 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10283899111043 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_563 : (1035134924122752788103887841224403 / 200000000000000000000000000000000 : ℝ) ≤ Vfield (20636590827023 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20636590827023 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (3212210362587 / 4000000000000 : ℝ) ≤ Real.sqrt (20636590827023 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20636590827023 / 32000000000000 : ℝ) ≤ (20076314766169 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20076314766169 / 25000000000000 : ℝ) = (25000000000000 / 20076314766169 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3212210362587 / 4000000000000 : ℝ) = (100000000000 / 1070736787529 : ℝ) := by norm_num
  have hL1 : (12441890454893 / 25000000000000 : ℝ) ≤ Real.log (1 + (20636590827023 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20636590827023 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-42998559786041 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (40152629532338 / 114126700042659 : ℝ) ≤ (42287469269261 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20076314766169 / 25000000000000 : ℝ) ≤ (42287469269261 / 62500000000000 : ℝ) := by
    have hw : (64126700042659 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (20076314766169 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (20076314766169 / 25000000000000 : ℝ) / (1 + (64126700042659 / 50000000000000 : ℝ)) = (40152629532338 / 114126700042659 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89419681848672061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 20076314766169 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 20076314766169 : ℝ) = (20076314766169 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (100000000000 / 1070736787529 : ℝ) ≤ (93123508636823 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89419681848672061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20076314766169 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3212210362587 / 4000000000000 : ℝ)) ≤ (93123508636823 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_563 : ∀ t : ℝ, (20636590827023 / 32000000000000 : ℝ) < t → t ≤ (517634585799 / 800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-18402708976492692956476219 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (517634585799 / 800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_564
  have hV : (1035134924122752788103887841224403 / 200000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20636590827023 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_563 (Vfield_monotoneOn (show (20636590827023 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20636590827023 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_564 : (25924875357666100072070308532566641 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (517634585799 / 800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (517634585799 / 800000000000 : ℝ) := by norm_num
  have hs1 : (80438997522889 / 100000000000000 : ℝ) ≤ Real.sqrt (517634585799 / 800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (517634585799 / 800000000000 : ℝ) ≤ (8043899752289 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8043899752289 / 10000000000000 : ℝ) = (10000000000000 / 8043899752289 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (80438997522889 / 100000000000000 : ℝ) = (7500000000000 / 80438997522889 : ℝ) := by norm_num
  have hL1 : (49898169993949 / 100000000000000 : ℝ) ≤ Real.log (1 + (517634585799 / 800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((517634585799 / 800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-42668634555591 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (80438997522890 / 228337182151111 : ℝ) ≤ (338706015008453 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8043899752289 / 10000000000000 : ℝ) ≤ (338706015008453 / 500000000000000 : ℝ) := by
    have hw : (128337182151111 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (8043899752289 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (8043899752289 / 10000000000000 : ℝ) / (1 + (128337182151111 / 100000000000000 : ℝ)) = (80438997522890 / 228337182151111 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89338429677799061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 8043899752289 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 8043899752289 : ℝ) = (8043899752289 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 80438997522889 : ℝ) ≤ (11621196520719 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89338429677799061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8043899752289 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (80438997522889 / 100000000000000 : ℝ)) ≤ (11621196520719 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_564 : ∀ t : ℝ, (517634585799 / 800000000000 : ℝ) < t → t ≤ (20774176036897 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-18299456144682472289748299 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20774176036897 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_565
  have hV : (25924875357666100072070308532566641 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (517634585799 / 800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_564 (Vfield_monotoneOn (show (517634585799 / 800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (517634585799 / 800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_565 : (12985650947200426291700600665915537 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (20774176036897 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20774176036897 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (40286256997673 / 50000000000000 : ℝ) ≤ Real.sqrt (20774176036897 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20774176036897 / 32000000000000 : ℝ) ≤ (80572513995347 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (80572513995347 / 100000000000000 : ℝ) = (100000000000000 / 80572513995347 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (40286256997673 / 50000000000000 : ℝ) = (3750000000000 / 40286256997673 : ℝ) := by norm_num
  have hL1 : (50028607805857 / 100000000000000 : ℝ) ≤ Real.log (1 + (20774176036897 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20774176036897 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-661559285207 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (80572513995347 / 228420909557323 : ℝ) ≤ (339111072492211 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (80572513995347 / 100000000000000 : ℝ) ≤ (339111072492211 / 500000000000000 : ℝ) := by
    have hw : (128420909557323 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (80572513995347 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (80572513995347 / 100000000000000 : ℝ) / (1 + (128420909557323 / 100000000000000 : ℝ)) = (80572513995347 / 228420909557323 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89257418181047461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 80572513995347 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 80572513995347 : ℝ) = (80572513995347 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 40286256997673 : ℝ) ≤ (92816396571957 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89257418181047461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (80572513995347 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (40286256997673 / 50000000000000 : ℝ)) ≤ (92816396571957 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_565 : ∀ t : ℝ, (20774176036897 / 32000000000000 : ℝ) < t → t ≤ (10421484320917 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-909850949515378833833229 / 1250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10421484320917 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_566
  have hV : (12985650947200426291700600665915537 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20774176036897 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_565 (Vfield_monotoneOn (show (20774176036897 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20774176036897 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_566 : (13008826531444132861862961953427641 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (10421484320917 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10421484320917 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (40352904791889 / 50000000000000 : ℝ) ≤ Real.sqrt (10421484320917 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10421484320917 / 16000000000000 : ℝ) ≤ (80705809583779 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (80705809583779 / 100000000000000 : ℝ) = (100000000000000 / 80705809583779 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (40352904791889 / 50000000000000 : ℝ) = (1250000000000 / 13450968263963 : ℝ) := by norm_num
  have hL1 : (50158875699151 / 100000000000000 : ℝ) ≤ Real.log (1 + (10421484320917 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10421484320917 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-42012031767023 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (80705809583779 / 228504582410796 : ℝ) ≤ (169757466539307 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (80705809583779 / 100000000000000 : ℝ) ≤ (169757466539307 / 250000000000000 : ℝ) := by
    have hw : (32126145602699 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (80705809583779 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (80705809583779 / 100000000000000 : ℝ) / (1 + (32126145602699 / 25000000000000 : ℝ)) = (80705809583779 / 228504582410796 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89176646063766861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 80705809583779 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 80705809583779 : ℝ) = (80705809583779 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 13450968263963 : ℝ) ≤ (741311804863 / 8000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89176646063766861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (80705809583779 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (40352904791889 / 50000000000000 : ℝ)) ≤ (741311804863 / 8000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_566 : ∀ t : ℝ, (10421484320917 / 16000000000000 : ℝ) < t → t ≤ (20911761246771 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-1447629668160662627328529 / 2000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20911761246771 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_567
  have hV : (13008826531444132861862961953427641 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10421484320917 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_566 (Vfield_monotoneOn (show (10421484320917 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10421484320917 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_567 : (5212785842017521034140345235267423 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (20911761246771 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20911761246771 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (16167777076167 / 20000000000000 : ℝ) ≤ Real.sqrt (20911761246771 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20911761246771 / 32000000000000 : ℝ) ≤ (20209721345209 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20209721345209 / 25000000000000 : ℝ) = (25000000000000 / 20209721345209 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16167777076167 / 20000000000000 : ℝ) = (500000000000 / 5389259025389 : ℝ) := by norm_num
  have hL1 : (10057794823191 / 20000000000000 : ℝ) ≤ Real.log (1 + (20911761246771 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20911761246771 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-41685340054633 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7348989580076 / 20780745528911 : ℝ) ≤ (339917603188177 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20209721345209 / 25000000000000 : ℝ) ≤ (339917603188177 / 500000000000000 : ℝ) := by
    have hw : (128588200818021 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (20209721345209 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (20209721345209 / 25000000000000 : ℝ) / (1 + (128588200818021 / 100000000000000 : ℝ)) = (7348989580076 / 20780745528911 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89096112041854261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 20209721345209 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 20209721345209 : ℝ) = (20209721345209 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 5389259025389 : ℝ) ≤ (3700492123901 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89096112041854261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20209721345209 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16167777076167 / 20000000000000 : ℝ)) ≤ (3700492123901 / 40000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_567 : ∀ t : ℝ, (20911761246771 / 32000000000000 : ℝ) < t → t ≤ (5245138462927 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-71977948430519159289483359 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5245138462927 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_568
  have hV : (5212785842017521034140345235267423 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20911761246771 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_567 (Vfield_monotoneOn (show (20911761246771 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20911761246771 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_568 : (26110130680330177562337307187340341 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (5245138462927 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5245138462927 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (80971742470189 / 100000000000000 : ℝ) ≤ Real.sqrt (5245138462927 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5245138462927 / 8000000000000 : ℝ) ≤ (8097174247019 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8097174247019 / 10000000000000 : ℝ) = (10000000000000 / 8097174247019 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (80971742470189 / 100000000000000 : ℝ) = (7500000000000 / 80971742470189 : ℝ) := by norm_num
  have hL1 : (50418903496667 / 100000000000000 : ℝ) ≤ Real.log (1 + (5245138462927 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5245138462927 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-41359712142587 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (80971742470190 / 228671764885147 : ℝ) ≤ (1361276356757 / 4000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8097174247019 / 10000000000000 : ℝ) ≤ (1361276356757 / 2000000000000 : ℝ) := by
    have hw : (128671764885147 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (8097174247019 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (8097174247019 / 10000000000000 : ℝ) / (1 + (128671764885147 / 100000000000000 : ℝ)) = (80971742470190 / 228671764885147 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89015814841639661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 8097174247019 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 8097174247019 : ℝ) = (8097174247019 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 80971742470189 : ℝ) ≤ (2886292904233 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89015814841639661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8097174247019 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (80971742470189 / 100000000000000 : ℝ)) ≤ (2886292904233 / 31250000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_568 : ∀ t : ℝ, (5245138462927 / 8000000000000 : ℝ) < t → t ≤ (10559069530791 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-8897461554974204833763227 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10559069530791 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_569
  have hV : (26110130680330177562337307187340341 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5245138462927 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_568 (Vfield_monotoneOn (show (5245138462927 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5245138462927 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_569 : (26202310954293445473148021435357417 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (10559069530791 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10559069530791 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (81236804816193 / 100000000000000 : ℝ) ≤ Real.sqrt (10559069530791 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10559069530791 / 16000000000000 : ℝ) ≤ (40618402408097 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (40618402408097 / 50000000000000 : ℝ) = (50000000000000 / 40618402408097 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (81236804816193 / 100000000000000 : ℝ) = (2500000000000 / 27078934938731 : ℝ) := by norm_num
  have hL1 : (25339128451427 / 50000000000000 : ℝ) ≤ Real.log (1 + (10559069530791 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10559069530791 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-8142324032841 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (81236804816194 / 228838730421967 : ℝ) ≤ (341118534082007 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (40618402408097 / 50000000000000 : ℝ) ≤ (341118534082007 / 500000000000000 : ℝ) := by
    have hw : (128838730421967 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (40618402408097 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (40618402408097 / 50000000000000 : ℝ) / (1 + (128838730421967 / 100000000000000 : ℝ)) = (81236804816194 / 228838730421967 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88855925863088261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 40618402408097 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 40618402408097 : ℝ) = (40618402408097 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 27078934938731 : ℝ) ≤ (92061715580859 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88855925863088261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (40618402408097 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (81236804816193 / 100000000000000 : ℝ)) ≤ (92061715580859 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_569 : ∀ t : ℝ, (10559069530791 / 16000000000000 : ℝ) < t → t ≤ (664241383483 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-351963251446177563633493 / 500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (664241383483 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_570
  have hV : (26202310954293445473148021435357417 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10559069530791 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_569 (Vfield_monotoneOn (show (10559069530791 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10559069530791 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_570 : (13147098293953420572704381718758601 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (664241383483 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (664241383483 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (40750502557729 / 50000000000000 : ℝ) ≤ Real.sqrt (664241383483 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (664241383483 / 1000000000000 : ℝ) ≤ (81501005115459 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (81501005115459 / 100000000000000 : ℝ) = (100000000000000 / 81501005115459 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (40750502557729 / 50000000000000 : ℝ) = (3750000000000 / 40750502557729 : ℝ) := by norm_num
  have hL1 : (50936939406781 / 100000000000000 : ℝ) ≤ Real.log (1 + (664241383483 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((664241383483 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-20033850693141 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (81501005115459 / 229005479863570 : ℝ) ≤ (170956658841191 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (81501005115459 / 100000000000000 : ℝ) ≤ (170956658841191 / 250000000000000 : ℝ) := by
    have hw : (12900547986357 / 10000000000000 : ℝ) ≤ Real.sqrt (1 + (81501005115459 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (81501005115459 / 100000000000000 : ℝ) / (1 + (12900547986357 / 10000000000000 : ℝ)) = (81501005115459 / 229005479863570 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88696969143013261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 81501005115459 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 81501005115459 : ℝ) = (81501005115459 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 40750502557729 : ℝ) ≤ (45882478036187 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88696969143013261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (81501005115459 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (40750502557729 / 50000000000000 : ℝ)) ≤ (45882478036187 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_570 : ∀ t : ℝ, (664241383483 / 1000000000000 : ℝ) < t → t ≤ (4261528693017 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-34829757014656814886200803 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4261528693017 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_571
  have hV : (13147098293953420572704381718758601 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (664241383483 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_570 (Vfield_monotoneOn (show (664241383483 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (664241383483 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_571 : (26328794554912005375874064550320137 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (4261528693017 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4261528693017 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (81600481511073 / 100000000000000 : ℝ) ≤ Real.sqrt (4261528693017 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4261528693017 / 6400000000000 : ℝ) ≤ (40800240755537 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (40800240755537 / 50000000000000 : ℝ) = (50000000000000 / 40800240755537 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (81600481511073 / 100000000000000 : ℝ) = (2500000000000 / 27200160503691 : ℝ) := by norm_num
  have hL1 : (51034382268883 / 100000000000000 : ℝ) ≤ Real.log (1 + (4261528693017 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4261528693017 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-19912892758833 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (40800240755537 / 114534174246749 : ℝ) ≤ (85553009052407 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (40800240755537 / 50000000000000 : ℝ) ≤ (85553009052407 / 125000000000000 : ℝ) := by
    have hw : (64534174246749 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (40800240755537 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (40800240755537 / 50000000000000 : ℝ) / (1 + (64534174246749 / 50000000000000 : ℝ)) = (40800240755537 / 114534174246749 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88637225437564061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 40800240755537 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 40800240755537 : ℝ) = (40800240755537 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 27200160503691 : ℝ) ≤ (91653714323551 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88637225437564061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (40800240755537 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (81600481511073 / 100000000000000 : ℝ)) ≤ (91653714323551 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_571 : ∀ t : ℝ, (4261528693017 / 6400000000000 : ℝ) < t → t ≤ (10679781329357 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-69185235703237215865644859 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10679781329357 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_572
  have hV : (26328794554912005375874064550320137 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4261528693017 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_571 (Vfield_monotoneOn (show (4261528693017 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4261528693017 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_572 : (26363351086109133754001242342987477 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (10679781329357 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10679781329357 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (81699836785933 / 100000000000000 : ℝ) ≤ Real.sqrt (10679781329357 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10679781329357 / 16000000000000 : ℝ) ≤ (40849918392967 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (40849918392967 / 50000000000000 : ℝ) = (50000000000000 / 40849918392967 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (81699836785933 / 100000000000000 : ℝ) = (7500000000000 / 81699836785933 : ℝ) := by norm_num
  have hL1 : (6391466284037 / 12500000000000 : ℝ) ≤ Real.log (1 + (10679781329357 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10679781329357 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-39584453469853 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (2149995704893 / 6029768066192 : ℝ) ≤ (342510100579737 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (40849918392967 / 50000000000000 : ℝ) ≤ (342510100579737 / 500000000000000 : ℝ) := by
    have hw : (4035349578603 / 3125000000000 : ℝ) ≤ Real.sqrt (1 + (40849918392967 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (40849918392967 / 50000000000000 : ℝ) / (1 + (4035349578603 / 3125000000000 : ℝ)) = (2149995704893 / 6029768066192 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88577612563542261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 40849918392967 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 40849918392967 : ℝ) = (40849918392967 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 81699836785933 : ℝ) ≤ (45771438078077 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88577612563542261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (40849918392967 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (81699836785933 / 100000000000000 : ℝ)) ≤ (45771438078077 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_572 : ∀ t : ℝ, (10679781329357 / 16000000000000 : ℝ) < t → t ≤ (21411481852343 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-1718870785725420258921963 / 2500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (21411481852343 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_573
  have hV : (26363351086109133754001242342987477 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10679781329357 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_572 (Vfield_monotoneOn (show (10679781329357 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10679781329357 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_573 : (13198933161161686318343146911147917 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (21411481852343 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (21411481852343 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (40899535690693 / 50000000000000 : ℝ) ≤ Real.sqrt (21411481852343 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (21411481852343 / 32000000000000 : ℝ) ≤ (81799071381387 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (81799071381387 / 100000000000000 : ℝ) = (100000000000000 / 81799071381387 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (40899535690693 / 50000000000000 : ℝ) = (3750000000000 / 40899535690693 : ℝ) := by norm_num
  have hL1 : (6403622950191 / 12500000000000 : ℝ) ≤ Real.log (1 + (21411481852343 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((21411481852343 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-9835925607933 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (81799071381387 / 229193993973625 : ℝ) ≤ (171403756693919 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (81799071381387 / 100000000000000 : ℝ) ≤ (171403756693919 / 250000000000000 : ℝ) := by
    have hw : (1033551951789 / 800000000000 : ℝ) ≤ Real.sqrt (1 + (81799071381387 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (81799071381387 / 100000000000000 : ℝ) / (1 + (1033551951789 / 800000000000 : ℝ)) = (81799071381387 / 229193993973625 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88518130001922061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 81799071381387 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 81799071381387 : ℝ) = (81799071381387 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 40899535690693 : ℝ) ≤ (22858109783939 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88518130001922061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (81799071381387 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (40899535690693 / 50000000000000 : ℝ)) ≤ (22858109783939 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_573 : ∀ t : ℝ, (21411481852343 / 32000000000000 : ℝ) < t → t ≤ (5365850261493 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-34173921584130904447420519 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5365850261493 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_574
  have hV : (13198933161161686318343146911147917 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (21411481852343 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_573 (Vfield_monotoneOn (show (21411481852343 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (21411481852343 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_574 : (26432340403592761936205752405032821 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (5365850261493 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5365850261493 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (81898185736109 / 100000000000000 : ℝ) ≤ Real.sqrt (5365850261493 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5365850261493 / 8000000000000 : ℝ) ≤ (8189818573611 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8189818573611 / 10000000000000 : ℝ) = (10000000000000 / 8189818573611 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (81898185736109 / 100000000000000 : ℝ) = (7500000000000 / 81898185736109 : ℝ) := by norm_num
  have hL1 : (25663071220273 / 50000000000000 : ℝ) ≤ Real.log (1 + (5365850261493 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5365850261493 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-7820705922489 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (81898185736110 / 229256770913041 : ℝ) ≤ (171552138606749 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8189818573611 / 10000000000000 : ℝ) ≤ (171552138606749 / 250000000000000 : ℝ) := by
    have hw : (129256770913041 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (8189818573611 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (8189818573611 / 10000000000000 : ℝ) / (1 + (129256770913041 / 100000000000000 : ℝ)) = (81898185736110 / 229256770913041 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88458777236790061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 8189818573611 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 8189818573611 : ℝ) = (8189818573611 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 81898185736109 : ℝ) ≤ (18264480169687 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88458777236790061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8189818573611 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (81898185736109 / 100000000000000 : ℝ)) ≤ (18264480169687 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_574 : ∀ t : ℝ, (5365850261493 / 8000000000000 : ℝ) < t → t ≤ (21515320239601 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-33978164130025198872990949 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (21515320239601 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_575
  have hV : (26432340403592761936205752405032821 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5365850261493 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_574 (Vfield_monotoneOn (show (5365850261493 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5365850261493 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_575 : (211734187753380447915548614785241 / 40000000000000000000000000000000 : ℝ) ≤ Vfield (21515320239601 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (21515320239601 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (655977442289 / 800000000000 : ℝ) ≤ Real.sqrt (21515320239601 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (21515320239601 / 32000000000000 : ℝ) ≤ (40998590143063 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (40998590143063 / 50000000000000 : ℝ) = (50000000000000 / 40998590143063 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (655977442289 / 800000000000 : ℝ) = (60000000000 / 655977442289 : ℝ) := by norm_num
  have hL1 : (10284641394557 / 20000000000000 : ℝ) ≤ Real.log (1 + (21515320239601 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((21515320239601 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-9715983060299 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (5856941449009 / 16379965526999 : ℝ) ≤ (343400394620839 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (40998590143063 / 50000000000000 : ℝ) ≤ (343400394620839 / 500000000000000 : ℝ) := by
    have hw : (64659758688993 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (40998590143063 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (40998590143063 / 50000000000000 : ℝ) / (1 + (64659758688993 / 50000000000000 : ℝ)) = (5856941449009 / 16379965526999 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88399553755321861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 40998590143063 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 40998590143063 : ℝ) = (40998590143063 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (60000000000 / 655977442289 : ℝ) ≤ (45606379450281 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88399553755321861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (40998590143063 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (655977442289 / 800000000000 : ℝ)) ≤ (45606379450281 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_575 : ∀ t : ℝ, (21515320239601 / 32000000000000 : ℝ) < t → t ≤ (43082559672831 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-67765019167362973157608471 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (43082559672831 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_576
  have hV : (211734187753380447915548614785241 / 40000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (21515320239601 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_575 (Vfield_monotoneOn (show (21515320239601 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (21515320239601 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_576 : (13241987332191965471074284528133857 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (43082559672831 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (43082559672831 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (41023316384953 / 50000000000000 : ℝ) ≤ Real.sqrt (43082559672831 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (43082559672831 / 64000000000000 : ℝ) ≤ (82046632769907 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (82046632769907 / 100000000000000 : ℝ) = (100000000000000 / 82046632769907 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41023316384953 / 50000000000000 : ℝ) = (3750000000000 / 41023316384953 : ℝ) := by norm_num
  have hL1 : (25735851965519 / 50000000000000 : ℝ) ≤ Real.log (1 + (43082559672831 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((43082559672831 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-38744348488149 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82046632769907 / 229350879196393 : ℝ) ≤ (68709642342947 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (82046632769907 / 100000000000000 : ℝ) ≤ (68709642342947 / 100000000000000 : ℝ) := by
    have hw : (129350879196393 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (82046632769907 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (82046632769907 / 100000000000000 : ℝ) / (1 + (129350879196393 / 100000000000000 : ℝ)) = (82046632769907 / 229350879196393 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88369990336542661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 82046632769907 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 82046632769907 : ℝ) = (82046632769907 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 41023316384953 : ℝ) ≤ (45579042905701 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88369990336542661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (82046632769907 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41023316384953 / 50000000000000 : ℝ)) ≤ (45579042905701 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_576 : ∀ t : ℝ, (43082559672831 / 64000000000000 : ℝ) < t → t ≤ (2156723943323 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-67576200340573673115391469 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2156723943323 / 3200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_577
  have hV : (13241987332191965471074284528133857 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (43082559672831 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_576 (Vfield_monotoneOn (show (43082559672831 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (43082559672831 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_577 : (26501165657542544872236915482218501 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2156723943323 / 3200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2156723943323 / 3200000000000 : ℝ) := by norm_num
  have hs1 : (82096055464829 / 100000000000000 : ℝ) ≤ Real.sqrt (2156723943323 / 3200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2156723943323 / 3200000000000 : ℝ) ≤ (8209605546483 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8209605546483 / 10000000000000 : ℝ) = (10000000000000 / 8209605546483 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (82096055464829 / 100000000000000 : ℝ) = (7500000000000 / 82096055464829 : ℝ) := by norm_num
  have hL1 : (51520177381143 / 100000000000000 : ℝ) ≤ Real.log (1 + (2156723943323 / 3200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2156723943323 / 3200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-7724981513411 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (8209605546483 / 22938223341280 : ℝ) ≤ (42961983519833 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8209605546483 / 10000000000000 : ℝ) ≤ (42961983519833 / 62500000000000 : ℝ) := by
    have hw : (80863895883 / 62500000000 : ℝ) ≤ Real.sqrt (1 + (8209605546483 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (8209605546483 / 10000000000000 : ℝ) / (1 + (80863895883 / 62500000000 : ℝ)) = (8209605546483 / 22938223341280 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88340459047756861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 8209605546483 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 8209605546483 : ℝ) = (8209605546483 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 82096055464829 : ℝ) ≤ (45551755459287 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88340459047756861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8209605546483 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (82096055464829 / 100000000000000 : ℝ)) ≤ (45551755459287 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_577 : ∀ t : ℝ, (2156723943323 / 3200000000000 : ℝ) < t → t ≤ (43186398060089 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-421185040792104226047837 / 625000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (43186398060089 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_578
  have hV : (26501165657542544872236915482218501 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2156723943323 / 3200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_577 (Vfield_monotoneOn (show (2156723943323 / 3200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2156723943323 / 3200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_578 : (13259173232919168453171423380917539 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (43186398060089 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (43186398060089 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (41072724212331 / 50000000000000 : ℝ) ≤ Real.sqrt (43186398060089 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (43186398060089 / 64000000000000 : ℝ) ≤ (82145448424663 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (82145448424663 / 100000000000000 : ℝ) = (100000000000000 / 82145448424663 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41072724212331 / 50000000000000 : ℝ) = (1250000000000 / 13690908070777 : ℝ) := by norm_num
  have hL1 : (51568627345877 / 100000000000000 : ℝ) ≤ Real.log (1 + (43186398060089 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((43186398060089 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-19252804568561 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82145448424663 / 229413580032734 : ℝ) ≤ (343843364268853 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (82145448424663 / 100000000000000 : ℝ) ≤ (343843364268853 / 500000000000000 : ℝ) := by
    have hw : (64706790016367 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (82145448424663 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (82145448424663 / 100000000000000 : ℝ) / (1 + (64706790016367 / 50000000000000 : ℝ)) = (82145448424663 / 229413580032734 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88310959825719061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 82145448424663 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 82145448424663 : ℝ) = (82145448424663 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 13690908070777 : ℝ) ≤ (91049033928483 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88310959825719061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (82145448424663 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41072724212331 / 50000000000000 : ℝ)) ≤ (91049033928483 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_578 : ∀ t : ℝ, (43186398060089 / 64000000000000 : ℝ) < t → t ≤ (21619158626859 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-16801255533237353403494269 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (21619158626859 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_579
  have hV : (13259173232919168453171423380917539 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (43186398060089 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_578 (Vfield_monotoneOn (show (43186398060089 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (43186398060089 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_579 : (26535517106413514572739005892850459 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (21619158626859 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (21619158626859 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (82194811703011 / 100000000000000 : ℝ) ≤ Real.sqrt (21619158626859 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (21619158626859 / 32000000000000 : ℝ) ≤ (20548702925753 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20548702925753 / 25000000000000 : ℝ) = (25000000000000 / 20548702925753 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (82194811703011 / 100000000000000 : ℝ) = (7500000000000 / 82194811703011 : ℝ) := by norm_num
  have hL1 : (12904263461997 / 25000000000000 : ℝ) ≤ Real.log (1 + (21619158626859 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((21619158626859 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1535458114351 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82194811703012 / 229444919061713 : ℝ) ≤ (343990700360593 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20548702925753 / 25000000000000 : ℝ) ≤ (343990700360593 / 500000000000000 : ℝ) := by
    have hw : (129444919061713 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (20548702925753 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (20548702925753 / 25000000000000 : ℝ) / (1 + (129444919061713 / 100000000000000 : ℝ)) = (82194811703012 / 229444919061713 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88281492607371061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 20548702925753 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 20548702925753 : ℝ) = (20548702925753 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 82194811703011 : ℝ) ≤ (2274866363719 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88281492607371061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20548702925753 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (82194811703011 / 100000000000000 : ℝ)) ≤ (2274866363719 / 25000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_579 : ∀ t : ℝ, (21619158626859 / 32000000000000 : ℝ) < t → t ≤ (43290236447347 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-33511134503282609189144367 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (43290236447347 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_580
  have hV : (26535517106413514572739005892850459 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (21619158626859 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_579 (Vfield_monotoneOn (show (21619158626859 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (21619158626859 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_580 : (26552677596361898865570312041317311 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (43290236447347 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (43290236447347 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (82244145353319 / 100000000000000 : ℝ) ≤ Real.sqrt (43290236447347 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (43290236447347 / 64000000000000 : ℝ) ≤ (2056103633833 / 2500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2056103633833 / 2500000000000 : ℝ) = (2500000000000 / 2056103633833 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (82244145353319 / 100000000000000 : ℝ) = (2500000000000 / 27414715117773 : ℝ) := by norm_num
  have hL1 : (12916364227547 / 25000000000000 : ℝ) ≤ Real.log (1 + (43290236447347 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((43290236447347 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-38267438393653 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82244145353320 / 229476250505249 : ℝ) ≤ (5377154324191 / 15625000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2056103633833 / 2500000000000 : ℝ) ≤ (5377154324191 / 7812500000000 : ℝ) := by
    have hw : (129476250505249 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (2056103633833 / 2500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (2056103633833 / 2500000000000 : ℝ) / (1 + (129476250505249 / 100000000000000 : ℝ)) = (82244145353320 / 229476250505249 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88252057329844861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (2500000000000 / 2056103633833 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (2500000000000 / 2056103633833 : ℝ) = (2056103633833 / 2500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 27414715117773 : ℝ) ≤ (90940372488261 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88252057329844861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2056103633833 / 2500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (82244145353319 / 100000000000000 : ℝ)) ≤ (90940372488261 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_580 : ∀ t : ℝ, (43290236447347 / 64000000000000 : ℝ) < t → t ≤ (2708884727561 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-33420598916386471960832197 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2708884727561 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_581
  have hV : (26552677596361898865570312041317311 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (43290236447347 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_580 (Vfield_monotoneOn (show (43290236447347 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (43290236447347 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_581 : (26569827952731292540175363171308337 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2708884727561 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2708884727561 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (82293449428873 / 100000000000000 : ℝ) ≤ Real.sqrt (2708884727561 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2708884727561 / 4000000000000 : ℝ) ≤ (41146724714437 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (41146724714437 / 50000000000000 : ℝ) = (50000000000000 / 41146724714437 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (82293449428873 / 100000000000000 : ℝ) = (7500000000000 / 82293449428873 : ℝ) := by norm_num
  have hL1 : (25856918277579 / 50000000000000 : ℝ) ≤ Real.log (1 + (2708884727561 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2708884727561 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-19074282702299 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82293449428874 / 229507574368847 : ℝ) ≤ (344284893745173 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (41146724714437 / 50000000000000 : ℝ) ≤ (344284893745173 / 500000000000000 : ℝ) := by
    have hw : (129507574368847 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (41146724714437 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (41146724714437 / 50000000000000 : ℝ) / (1 + (129507574368847 / 100000000000000 : ℝ)) = (82293449428874 / 229507574368847 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88222653930455061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 41146724714437 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 41146724714437 : ℝ) = (41146724714437 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 82293449428873 : ℝ) ≤ (22721546864263 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88222653930455061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (41146724714437 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (82293449428873 / 100000000000000 : ℝ)) ≤ (22721546864263 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_581 : ∀ t : ℝ, (2708884727561 / 4000000000000 : ℝ) < t → t ≤ (8678814966921 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-66661681920747107137891783 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (8678814966921 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_582
  have hV : (26569827952731292540175363171308337 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2708884727561 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_581 (Vfield_monotoneOn (show (2708884727561 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2708884727561 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_582 : (6646742048130290635056652469407531 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (8678814966921 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (8678814966921 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (20585680995699 / 25000000000000 : ℝ) ≤ Real.sqrt (8678814966921 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (8678814966921 / 12800000000000 : ℝ) ≤ (82342723982797 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (82342723982797 / 100000000000000 : ℝ) = (100000000000000 / 82342723982797 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (20585680995699 / 25000000000000 : ℝ) = (625000000000 / 6861893665233 : ℝ) := by norm_num
  have hL1 : (25881096402773 / 50000000000000 : ℝ) ≤ Real.log (1 + (8678814966921 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((8678814966921 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-38029833555659 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82342723982797 / 229538890658006 : ℝ) ≤ (172215875831957 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (82342723982797 / 100000000000000 : ℝ) ≤ (172215875831957 / 250000000000000 : ℝ) := by
    have hw : (64769445329003 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (82342723982797 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (82342723982797 / 100000000000000 : ℝ) / (1 + (64769445329003 / 50000000000000 : ℝ)) = (82342723982797 / 229538890658006 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88193282346706861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 82342723982797 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 82342723982797 : ℝ) = (82342723982797 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (625000000000 / 6861893665233 : ℝ) ≤ (90832099166409 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88193282346706861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (82342723982797 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (20585680995699 / 25000000000000 : ℝ)) ≤ (90832099166409 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_582 : ∀ t : ℝ, (8678814966921 / 12800000000000 : ℝ) < t → t ≤ (21722997014117 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-66483612614407083173664069 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (21722997014117 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_583
  have hV : (6646742048130290635056652469407531 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (8678814966921 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_582 (Vfield_monotoneOn (show (8678814966921 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (8678814966921 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_583 : (3325512291585606723422702196661883 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (21722997014117 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (21722997014117 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (10298996133507 / 12500000000000 : ℝ) ≤ Real.sqrt (21722997014117 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (21722997014117 / 32000000000000 : ℝ) ≤ (82391969068057 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (82391969068057 / 100000000000000 : ℝ) = (100000000000000 / 82391969068057 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10298996133507 / 12500000000000 : ℝ) = (312500000000 / 3432998711169 : ℝ) := by norm_num
  have hL1 : (10362105136793 / 20000000000000 : ℝ) ≤ Real.log (1 + (21722997014117 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((21722997014117 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-18955621256037 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82391969068057 / 229570199378219 : ℝ) ≤ (86144612704003 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (82391969068057 / 100000000000000 : ℝ) ≤ (86144612704003 / 125000000000000 : ℝ) := by
    have hw : (129570199378219 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (82391969068057 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (82391969068057 / 100000000000000 : ℝ) / (1 + (129570199378219 / 100000000000000 : ℝ)) = (82391969068057 / 229570199378219 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88163942516287261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 82391969068057 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 82391969068057 : ℝ) = (82391969068057 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (312500000000 / 3432998711169 : ℝ) ≤ (11347263416101 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88163942516287261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (82391969068057 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10298996133507 / 12500000000000 : ℝ)) ≤ (11347263416101 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_583 : ∀ t : ℝ, (21722997014117 / 32000000000000 : ℝ) < t → t ≤ (43497913221863 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-4144180989802573872404027 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (43497913221863 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_584
  have hV : (3325512291585606723422702196661883 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (21722997014117 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_583 (Vfield_monotoneOn (show (21722997014117 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (21722997014117 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_584 : (1331060919506408890916440284260337 / 250000000000000000000000000000000 : ℝ) ≤ Vfield (43497913221863 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (43497913221863 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (4122059236873 / 5000000000000 : ℝ) ≤ Real.sqrt (43497913221863 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (43497913221863 / 64000000000000 : ℝ) ≤ (82441184737461 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (82441184737461 / 100000000000000 : ℝ) = (100000000000000 / 82441184737461 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4122059236873 / 5000000000000 : ℝ) = (375000000000 / 4122059236873 : ℝ) := by norm_num
  have hL1 : (25929417606499 / 50000000000000 : ℝ) ≤ Real.log (1 + (43497913221863 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((43497913221863 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1511711677611 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (27480394912487 / 76533833511657 : ℝ) ≤ (344724991512099 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (82441184737461 / 100000000000000 : ℝ) ≤ (344724991512099 / 500000000000000 : ℝ) := by
    have hw : (129601500534971 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (82441184737461 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (82441184737461 / 100000000000000 : ℝ) / (1 + (129601500534971 / 100000000000000 : ℝ)) = (27480394912487 / 76533833511657 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88134634377069861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 82441184737461 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 82441184737461 : ℝ) = (82441184737461 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (375000000000 / 4122059236873 : ℝ) ≤ (90724211657923 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88134634377069861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (82441184737461 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4122059236873 / 5000000000000 : ℝ)) ≤ (90724211657923 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_584 : ∀ t : ℝ, (43497913221863 / 64000000000000 : ℝ) < t → t ≤ (10887458103873 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-66131449443726342546613293 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10887458103873 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_585
  have hV : (1331060919506408890916440284260337 / 250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (43497913221863 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_584 (Vfield_monotoneOn (show (43497913221863 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (43497913221863 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_585 : (26638328381710855004728945471088771 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (10887458103873 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10887458103873 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (82490371043659 / 100000000000000 : ℝ) ≤ Real.sqrt (10887458103873 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10887458103873 / 16000000000000 : ℝ) ≤ (4124518552183 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4124518552183 / 5000000000000 : ℝ) = (5000000000000 / 4124518552183 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (82490371043659 / 100000000000000 : ℝ) = (7500000000000 / 82490371043659 : ℝ) := by norm_num
  have hL1 : (25953560707597 / 50000000000000 : ℝ) ≤ Real.log (1 + (10887458103873 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10887458103873 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-37674481507877 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (4124518552183 / 11481639706687 : ℝ) ≤ (43108921757737 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4124518552183 / 5000000000000 : ℝ) ≤ (43108921757737 / 62500000000000 : ℝ) := by
    have hw : (6481639706687 / 5000000000000 : ℝ) ≤ Real.sqrt (1 + (4124518552183 / 5000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (4124518552183 / 5000000000000 : ℝ) / (1 + (6481639706687 / 5000000000000 : ℝ)) = (4124518552183 / 11481639706687 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88105357867110461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 4124518552183 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 4124518552183 : ℝ) = (4124518552183 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 82490371043659 : ℝ) ≤ (22667602967153 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88105357867110461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4124518552183 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (82490371043659 / 100000000000000 : ℝ)) ≤ (22667602967153 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_585 : ∀ t : ℝ, (10887458103873 / 16000000000000 : ℝ) < t → t ≤ (43601751609121 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-32978600582776434491542373 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (43601751609121 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_586
  have hV : (26638328381710855004728945471088771 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10887458103873 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_585 (Vfield_monotoneOn (show (10887458103873 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10887458103873 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_586 : (26655428324245864120836952935099043 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (43601751609121 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (43601751609121 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (82539528039147 / 100000000000000 : ℝ) ≤ Real.sqrt (43601751609121 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (43601751609121 / 64000000000000 : ℝ) ≤ (20634882009787 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20634882009787 / 25000000000000 : ℝ) = (25000000000000 / 20634882009787 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (82539528039147 / 100000000000000 : ℝ) = (2500000000000 / 27513176013049 : ℝ) := by norm_num
  have hL1 : (12988846078267 / 25000000000000 : ℝ) ≤ Real.log (1 + (43601751609121 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((43601751609121 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-37556310883671 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82539528039148 / 229664080179999 : ℝ) ≤ (69003519754841 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20634882009787 / 25000000000000 : ℝ) ≤ (69003519754841 / 100000000000000 : ℝ) := by
    have hw : (129664080179999 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (20634882009787 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (20634882009787 / 25000000000000 : ℝ) / (1 + (129664080179999 / 100000000000000 : ℝ)) = (82539528039148 / 229664080179999 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88076112924648661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 20634882009787 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 20634882009787 : ℝ) = (20634882009787 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 27513176013049 : ℝ) ≤ (90616707676919 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88076112924648661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20634882009787 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (82539528039147 / 100000000000000 : ℝ)) ≤ (90616707676919 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_586 : ∀ t : ℝ, (43601751609121 / 64000000000000 : ℝ) < t → t ≤ (174614683211 / 256000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-65784086985985354805796897 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (174614683211 / 256000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_587
  have hV : (26655428324245864120836952935099043 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (43601751609121 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_586 (Vfield_monotoneOn (show (43601751609121 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (43601751609121 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_587 : (1333625911724981995776107056802197 / 250000000000000000000000000000000 : ℝ) ≤ Vfield (174614683211 / 256000000000 : ℝ) := by
  have hp : (0 : ℝ) < (174614683211 / 256000000000 : ℝ) := by norm_num
  have hs1 : (4129432788813 / 5000000000000 : ℝ) ≤ Real.sqrt (174614683211 / 256000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (174614683211 / 256000000000 : ℝ) ≤ (82588655776261 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (82588655776261 / 100000000000000 : ℝ) = (100000000000000 / 82588655776261 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4129432788813 / 5000000000000 : ℝ) = (125000000000 / 1376477596271 : ℝ) := by norm_num
  have hL1 : (26001811964553 / 50000000000000 : ℝ) ≤ Real.log (1 + (174614683211 / 256000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((174614683211 / 256000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-37438279737623 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82588655776261 / 229695358679213 : ℝ) ≤ (21572729122307 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (82588655776261 / 100000000000000 : ℝ) ≤ (21572729122307 / 31250000000000 : ℝ) := by
    have hw : (129695358679213 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (82588655776261 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (82588655776261 / 100000000000000 : ℝ) / (1 + (129695358679213 / 100000000000000 : ℝ)) = (82588655776261 / 229695358679213 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88046899488107261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 82588655776261 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 82588655776261 : ℝ) = (82588655776261 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (125000000000 / 1376477596271 : ℝ) ≤ (90563098800063 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88046899488107261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (82588655776261 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4129432788813 / 5000000000000 : ℝ)) ≤ (90563098800063 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_587 : ∀ t : ℝ, (174614683211 / 256000000000 : ℝ) < t → t ≤ (43705589996379 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-32806024924189971373562741 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (43705589996379 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_588
  have hV : (1333625911724981995776107056802197 / 250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (174614683211 / 256000000000 : ℝ) := by norm_num
    refine le_trans V_pt_587 (Vfield_monotoneOn (show (174614683211 / 256000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (174614683211 / 256000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_588 : (13344799064596727306375400028046479 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (43705589996379 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (43705589996379 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (41318877153591 / 50000000000000 : ℝ) ≤ Real.sqrt (43705589996379 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (43705589996379 / 64000000000000 : ℝ) ≤ (82637754307183 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (82637754307183 / 100000000000000 : ℝ) = (100000000000000 / 82637754307183 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41318877153591 / 50000000000000 : ℝ) = (1250000000000 / 13772959051197 : ℝ) := by norm_num
  have hL1 : (26025920142879 / 50000000000000 : ℝ) ≤ Real.log (1 + (43705589996379 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((43705589996379 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-18660193870433 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82637754307183 / 229726629636841 : ℝ) ≤ (21581848494813 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (82637754307183 / 100000000000000 : ℝ) ≤ (21581848494813 / 31250000000000 : ℝ) := by
    have hw : (129726629636841 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (82637754307183 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (82637754307183 / 100000000000000 : ℝ) / (1 + (129726629636841 / 100000000000000 : ℝ)) = (82637754307183 / 229726629636841 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (88017717496088061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 82637754307183 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 82637754307183 : ℝ) = (82637754307183 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 13772959051197 : ℝ) ≤ (90509584956431 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (88017717496088061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (82637754307183 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41318877153591 / 50000000000000 : ℝ)) ≤ (90509584956431 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_588 : ∀ t : ℝ, (43705589996379 / 64000000000000 : ℝ) < t → t ≤ (5469688648751 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-13088207722544622895417283 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5469688648751 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_589
  have hV : (13344799064596727306375400028046479 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (43705589996379 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_588 (Vfield_monotoneOn (show (43705589996379 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (43705589996379 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_589 : (13353334012500728856826893948339161 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (5469688648751 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5469688648751 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (41343411841969 / 50000000000000 : ℝ) ≤ Real.sqrt (5469688648751 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5469688648751 / 8000000000000 : ℝ) ≤ (82686823683939 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (82686823683939 / 100000000000000 : ℝ) = (100000000000000 / 82686823683939 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41343411841969 / 50000000000000 : ℝ) = (3750000000000 / 41343411841969 : ℝ) := by norm_num
  have hL1 : (52100033405443 / 100000000000000 : ℝ) ≤ Real.log (1 + (5469688648751 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5469688648751 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-7440526913139 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82686823683939 / 229757893058336 : ℝ) ≤ (86363832240141 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (82686823683939 / 100000000000000 : ℝ) ≤ (86363832240141 / 125000000000000 : ℝ) := by
    have hw : (4054934158073 / 3125000000000 : ℝ) ≤ Real.sqrt (1 + (82686823683939 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (82686823683939 / 100000000000000 : ℝ) / (1 + (4054934158073 / 3125000000000 : ℝ)) = (82686823683939 / 229757893058336 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87988566887376861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 82686823683939 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 82686823683939 : ℝ) = (82686823683939 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 41343411841969 : ℝ) ≤ (11307020733197 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87988566887376861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (82686823683939 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41343411841969 / 50000000000000 : ℝ)) ≤ (11307020733197 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_589 : ∀ t : ℝ, (5469688648751 / 8000000000000 : ℝ) < t → t ≤ (43809428383637 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-32635503603063058698880607 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (43809428383637 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_590
  have hV : (13353334012500728856826893948339161 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5469688648751 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_589 (Vfield_monotoneOn (show (5469688648751 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5469688648751 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_590 : (13361863969276505773229329076390569 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (43809428383637 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (43809428383637 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (41367931979201 / 50000000000000 : ℝ) ≤ Real.sqrt (43809428383637 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (43809428383637 / 64000000000000 : ℝ) ≤ (82735863958403 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (82735863958403 / 100000000000000 : ℝ) = (100000000000000 / 82735863958403 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41367931979201 / 50000000000000 : ℝ) = (3750000000000 / 41367931979201 : ℝ) := by norm_num
  have hL1 : (52148203310547 / 100000000000000 : ℝ) ≤ Real.log (1 + (43809428383637 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((43809428383637 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-927125497139 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82735863958403 / 229789148949145 : ℝ) ≤ (172800462696381 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (82735863958403 / 100000000000000 : ℝ) ≤ (172800462696381 / 250000000000000 : ℝ) := by
    have hw : (25957829789829 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (82735863958403 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (82735863958403 / 100000000000000 : ℝ) / (1 + (25957829789829 / 20000000000000 : ℝ)) = (82735863958403 / 229789148949145 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87959447600937261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 82735863958403 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 82735863958403 : ℝ) = (82735863958403 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 41367931979201 : ℝ) ≤ (90402841248207 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87959447600937261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (82735863958403 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41367931979201 / 50000000000000 : ℝ)) ≤ (90402841248207 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_590 : ∀ t : ℝ, (43809428383637 / 64000000000000 : ℝ) < t → t ≤ (21930673788633 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-65101913924676510561694767 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (21930673788633 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_591
  have hV : (13361863969276505773229329076390569 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (43809428383637 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_590 (Vfield_monotoneOn (show (43809428383637 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (43809428383637 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_591 : (6685194471607810472939692491600637 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (21930673788633 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (21930673788633 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (20696218795573 / 25000000000000 : ℝ) ≤ Real.sqrt (21930673788633 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (21930673788633 / 32000000000000 : ℝ) ≤ (82784875182293 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (82784875182293 / 100000000000000 : ℝ) = (100000000000000 / 82784875182293 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (20696218795573 / 25000000000000 : ℝ) = (1875000000000 / 20696218795573 : ℝ) := by norm_num
  have hL1 : (2087854000937 / 4000000000000 : ℝ) ≤ Real.log (1 + (21930673788633 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((21930673788633 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-36967543375063 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82784875182293 / 229820397314704 : ℝ) ≤ (86436591379471 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (82784875182293 / 100000000000000 : ℝ) ≤ (86436591379471 / 125000000000000 : ℝ) := by
    have hw : (8113774832169 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (82784875182293 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (82784875182293 / 100000000000000 : ℝ) / (1 + (8113774832169 / 6250000000000 : ℝ)) = (82784875182293 / 229820397314704 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87930359575912861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 82784875182293 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 82784875182293 : ℝ) = (82784875182293 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 20696218795573 : ℝ) ≤ (11293701353273 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87930359575912861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (82784875182293 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (20696218795573 / 25000000000000 : ℝ)) ≤ (11293701353273 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_591 : ∀ t : ℝ, (21930673788633 / 32000000000000 : ℝ) < t → t ≤ (8782653354179 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-64933720854900674375321999 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (8782653354179 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_592
  have hV : (6685194471607810472939692491600637 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (21930673788633 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_591 (Vfield_monotoneOn (show (21930673788633 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (21930673788633 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_592 : (1070312715406980568099210878139703 / 200000000000000000000000000000000 : ℝ) ≤ Vfield (8782653354179 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (8782653354179 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (3313354296287 / 4000000000000 : ℝ) ≤ Real.sqrt (8782653354179 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (8782653354179 / 12800000000000 : ℝ) ≤ (10354232175897 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (10354232175897 / 12500000000000 : ℝ) = (12500000000000 / 10354232175897 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3313354296287 / 4000000000000 : ℝ) = (300000000000 / 3313354296287 : ℝ) := by norm_num
  have hL1 : (52244473566399 / 100000000000000 : ℝ) ≤ Real.log (1 + (8782653354179 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((8782653354179 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-36850204709951 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82833857407176 / 229851638160449 : ℝ) ≤ (8647291240983 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (10354232175897 / 12500000000000 : ℝ) ≤ (8647291240983 / 12500000000000 : ℝ) := by
    have hw : (129851638160449 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (10354232175897 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (10354232175897 / 12500000000000 : ℝ) / (1 + (129851638160449 / 100000000000000 : ℝ)) = (82833857407176 / 229851638160449 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87901302751625661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 10354232175897 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 10354232175897 : ℝ) = (10354232175897 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (300000000000 / 3313354296287 : ℝ) ≤ (5643529645157 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87901302751625661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (10354232175897 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3313354296287 / 4000000000000 : ℝ)) ≤ (5643529645157 / 62500000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_592 : ∀ t : ℝ, (8782653354179 / 12800000000000 : ℝ) < t → t ≤ (10991296491131 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-64766393390687885537074881 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10991296491131 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_593
  have hV : (1070312715406980568099210878139703 / 200000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (8782653354179 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_592 (Vfield_monotoneOn (show (8782653354179 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (8782653354179 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_593 : (5354969590255148529423418551875717 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (10991296491131 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10991296491131 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (16576562136893 / 20000000000000 : ℝ) ≤ Real.sqrt (10991296491131 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10991296491131 / 16000000000000 : ℝ) ≤ (41441405342233 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (41441405342233 / 50000000000000 : ℝ) = (50000000000000 / 41441405342233 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16576562136893 / 20000000000000 : ℝ) = (1500000000000 / 16576562136893 : ℝ) := by norm_num
  have hL1 : (26146286980879 / 50000000000000 : ℝ) ≤ Real.log (1 + (10991296491131 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10991296491131 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-4591625445889 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (3187800410941 / 8841648903531 : ℝ) ≤ (34603677805957 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (41441405342233 / 50000000000000 : ℝ) ≤ (34603677805957 / 50000000000000 : ℝ) := by
    have hw : (64941435745903 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (41441405342233 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (41441405342233 / 50000000000000 : ℝ) / (1 + (64941435745903 / 50000000000000 : ℝ)) = (3187800410941 / 8841648903531 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87872277067575661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 41441405342233 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 41441405342233 : ℝ) = (41441405342233 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 16576562136893 : ℝ) ≤ (18048686292267 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87872277067575661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (41441405342233 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16576562136893 / 20000000000000 : ℝ)) ≤ (18048686292267 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_593 : ∀ t : ℝ, (10991296491131 / 16000000000000 : ℝ) < t → t ≤ (44017105158153 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-16149974956767753370230233 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (44017105158153 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_594
  have hV : (5354969590255148529423418551875717 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10991296491131 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_593 (Vfield_monotoneOn (show (10991296491131 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10991296491131 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_594 : (13395934050590968037417618655189759 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (44017105158153 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (44017105158153 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (41465867532711 / 50000000000000 : ℝ) ≤ Real.sqrt (44017105158153 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (44017105158153 / 64000000000000 : ℝ) ≤ (82931735065423 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (82931735065423 / 100000000000000 : ℝ) = (100000000000000 / 82931735065423 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41465867532711 / 50000000000000 : ℝ) = (1250000000000 / 13821955844237 : ℝ) := by norm_num
  have hL1 : (52340651231759 / 100000000000000 : ℝ) ≤ Real.log (1 + (44017105158153 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((44017105158153 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-18307969812283 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82931735065423 / 229914097314192 : ℝ) ≤ (346181751080243 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (82931735065423 / 100000000000000 : ℝ) ≤ (346181751080243 / 500000000000000 : ℝ) := by
    have hw : (8119631082137 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (82931735065423 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (82931735065423 / 100000000000000 : ℝ) / (1 + (8119631082137 / 6250000000000 : ℝ)) = (82931735065423 / 229914097314192 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87843282463441061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 82931735065423 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 82931735065423 : ℝ) = (82931735065423 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 13821955844237 : ℝ) ≤ (22547620491983 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87843282463441061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (82931735065423 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41465867532711 / 50000000000000 : ℝ)) ≤ (22547620491983 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_594 : ∀ t : ℝ, (44017105158153 / 64000000000000 : ℝ) < t → t ≤ (22034512175891 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-64434211016416232240795473 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (22034512175891 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_595
  have hV : (13395934050590968037417618655189759 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (44017105158153 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_594 (Vfield_monotoneOn (show (44017105158153 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (44017105158153 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_595 : (13404439175648219270327707759060251 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (22034512175891 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (22034512175891 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (41490315300579 / 50000000000000 : ℝ) ≤ Real.sqrt (22034512175891 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (22034512175891 / 32000000000000 : ℝ) ≤ (82980630601159 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (82980630601159 / 100000000000000 : ℝ) = (100000000000000 / 82980630601159 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41490315300579 / 50000000000000 : ℝ) = (1250000000000 / 13830105100193 : ℝ) := by norm_num
  have hL1 : (13097176349657 / 25000000000000 : ℝ) ≤ Real.log (1 + (22034512175891 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((22034512175891 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-18249506280733 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (82980630601159 / 229945315633023 : ℝ) ≤ (43290821125259 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (82980630601159 / 100000000000000 : ℝ) ≤ (43290821125259 / 62500000000000 : ℝ) := by
    have hw : (129945315633023 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (82980630601159 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (82980630601159 / 100000000000000 : ℝ) / (1 + (129945315633023 / 100000000000000 : ℝ)) = (82980630601159 / 229945315633023 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87814318879075261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 82980630601159 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 82980630601159 : ℝ) = (82980630601159 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 13830105100193 : ℝ) ≤ (90137625568707 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87814318879075261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (82980630601159 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41490315300579 / 50000000000000 : ℝ)) ≤ (90137625568707 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_595 : ∀ t : ℝ, (22034512175891 / 32000000000000 : ℝ) < t → t ≤ (44120943545411 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-32134650038942768634843931 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (44120943545411 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_596
  have hV : (13404439175648219270327707759060251 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (22034512175891 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_595 (Vfield_monotoneOn (show (22034512175891 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (22034512175891 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_596 : (13412939358988871232360528177287773 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (44120943545411 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (44120943545411 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (41514748671317 / 50000000000000 : ℝ) ≤ Real.sqrt (44120943545411 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (44120943545411 / 64000000000000 : ℝ) ≤ (16605899468527 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16605899468527 / 20000000000000 : ℝ) = (20000000000000 / 16605899468527 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41514748671317 / 50000000000000 : ℝ) = (3750000000000 / 41514748671317 : ℝ) := by norm_num
  have hL1 : (52436736484559 / 100000000000000 : ℝ) ≤ Real.log (1 + (44120943545411 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((44120943545411 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-4547777757261 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (83029497342635 / 229976526453704 : ℝ) ≤ (173235616062457 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16605899468527 / 20000000000000 : ℝ) ≤ (173235616062457 / 250000000000000 : ℝ) := by
    have hw : (16247065806713 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (16605899468527 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (16605899468527 / 20000000000000 : ℝ) / (1 + (16247065806713 / 12500000000000 : ℝ)) = (83029497342635 / 229976526453704 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87785386254506861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 16605899468527 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 16605899468527 : ℝ) = (16605899468527 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 41514748671317 : ℝ) ≤ (90084861991183 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87785386254506861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16605899468527 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41514748671317 / 50000000000000 : ℝ)) ≤ (90084861991183 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_596 : ∀ t : ℝ, (44120943545411 / 64000000000000 : ℝ) < t → t ≤ (276080392119 / 400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-32052571068931126634799227 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (276080392119 / 400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_597
  have hV : (13412939358988871232360528177287773 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (44120943545411 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_596 (Vfield_monotoneOn (show (44120943545411 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (44120943545411 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_597 : (26842869217538806348689165524481771 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (276080392119 / 400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (276080392119 / 400000000000 : ℝ) := by norm_num
  have hs1 : (83078335340659 / 100000000000000 : ℝ) ≤ Real.sqrt (276080392119 / 400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (276080392119 / 400000000000 : ℝ) ≤ (4153916767033 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4153916767033 / 5000000000000 : ℝ) = (5000000000000 / 4153916767033 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (83078335340659 / 100000000000000 : ℝ) = (7500000000000 / 83078335340659 : ℝ) := by norm_num
  have hL1 : (1640148265991 / 3125000000000 : ℝ) ≤ Real.log (1 + (276080392119 / 400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((276080392119 / 400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1450622711833 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (83078335340660 / 230007729781637 : ℝ) ≤ (346615740747737 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4153916767033 / 5000000000000 : ℝ) ≤ (346615740747737 / 500000000000000 : ℝ) := by
    have hw : (130007729781637 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (4153916767033 / 5000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (4153916767033 / 5000000000000 : ℝ) / (1 + (130007729781637 / 100000000000000 : ℝ)) = (83078335340660 / 230007729781637 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87756484529942261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 4153916767033 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 4153916767033 : ℝ) = (4153916767033 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 83078335340659 : ℝ) ≤ (18006438192801 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87756484529942261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4153916767033 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (83078335340659 / 100000000000000 : ℝ)) ≤ (18006438192801 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_597 : ∀ t : ℝ, (276080392119 / 400000000000 : ℝ) < t → t ≤ (44224781932669 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-799271426593582936082721 / 1250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (44224781932669 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_598
  have hV : (26842869217538806348689165524481771 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (276080392119 / 400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_597 (Vfield_monotoneOn (show (276080392119 / 400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (276080392119 / 400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_598 : (13429924933124467483102256392941243 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (44224781932669 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (44224781932669 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (41563572322947 / 50000000000000 : ℝ) ≤ Real.sqrt (44224781932669 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (44224781932669 / 64000000000000 : ℝ) ≤ (16625428929179 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16625428929179 / 20000000000000 : ℝ) = (20000000000000 / 16625428929179 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41563572322947 / 50000000000000 : ℝ) = (1250000000000 / 13854524107649 : ℝ) := by norm_num
  have hL1 : (26266364751109 / 50000000000000 : ℝ) ≤ Real.log (1 + (44224781932669 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((44224781932669 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-7229809891437 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (83127144645895 / 230038925622213 : ℝ) ≤ (6935201903373 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16625428929179 / 20000000000000 : ℝ) ≤ (6935201903373 / 10000000000000 : ℝ) := by
    have hw : (130038925622213 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (16625428929179 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (16625428929179 / 20000000000000 : ℝ) / (1 + (130038925622213 / 100000000000000 : ℝ)) = (83127144645895 / 230038925622213 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87727613645759661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 16625428929179 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 16625428929179 : ℝ) = (16625428929179 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 13854524107649 : ℝ) ≤ (89979612216921 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87727613645759661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16625428929179 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41563572322947 / 50000000000000 : ℝ)) ≤ (89979612216921 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_598 : ∀ t : ℝ, (44224781932669 / 64000000000000 : ℝ) < t → t ≤ (22138350563149 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-6377899458709889793121613 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (22138350563149 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_599
  have hV : (13429924933124467483102256392941243 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (44224781932669 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_598 (Vfield_monotoneOn (show (44224781932669 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (44224781932669 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_599 : (13438410340167007829379543004849363 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (22138350563149 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (22138350563149 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (41587962654427 / 50000000000000 : ℝ) ≤ Real.sqrt (22138350563149 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (22138350563149 / 32000000000000 : ℝ) ≤ (16635185061771 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16635185061771 / 20000000000000 : ℝ) = (20000000000000 / 16635185061771 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41587962654427 / 50000000000000 : ℝ) = (3750000000000 / 41587962654427 : ℝ) := by norm_num
  have hL1 : (26290345739087 / 50000000000000 : ℝ) ≤ Real.log (1 + (22138350563149 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((22138350563149 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-18016333362893 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (83175925308855 / 230070113980822 : ℝ) ≤ (10840759240153 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16635185061771 / 20000000000000 : ℝ) ≤ (10840759240153 / 15625000000000 : ℝ) := by
    have hw : (65035056990411 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (16635185061771 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (16635185061771 / 20000000000000 : ℝ) / (1 + (65035056990411 / 50000000000000 : ℝ)) = (83175925308855 / 230070113980822 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87698773542510461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 16635185061771 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 16635185061771 : ℝ) = (16635185061771 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 41587962654427 : ℝ) ≤ (89927125480783 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87698773542510461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16635185061771 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41587962654427 / 50000000000000 : ℝ)) ≤ (89927125480783 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_599 : ∀ t : ℝ, (22138350563149 / 32000000000000 : ℝ) < t → t ≤ (44328620319927 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2544678540295758231133367 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (44328620319927 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_600
  have hV : (13438410340167007829379543004849363 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (22138350563149 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_599 (Vfield_monotoneOn (show (22138350563149 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (22138350563149 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
