import Apery.Table2.U17

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_680 : (17528679900644804251837784415044561 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (18213010252359 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (18213010252359 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (106691758855707 / 100000000000000 : ℝ) ≤ Real.sqrt (18213010252359 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (18213010252359 / 16000000000000 : ℝ) ≤ (26672939713927 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (26672939713927 / 25000000000000 : ℝ) = (25000000000000 / 26672939713927 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (106691758855707 / 100000000000000 : ℝ) = (2500000000000 / 35563919618569 : ℝ) := by norm_num
  have hL1 : (38000863310849 / 50000000000000 : ℝ) ≤ Real.log (1 + (18213010252359 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((18213010252359 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (6723840937213 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : (1882584801379 / 5000000000000 : ℝ) ≤ Real.arctan (1250000000000000000000000000 / 3161518502640852989497699161 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (1882584801379 / 2500000000000 : ℝ) ≤ Real.arctan (25000000000000 / 26672939713927 : ℝ) := by
    have hw : Real.sqrt (1 + (25000000000000 / 26672939713927 : ℝ) ^ 2) ≤ (68529061158943 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
    have := arctan_ge_half (by norm_num) hw
    have e : (25000000000000 / 26672939713927 : ℝ) / (1 + (68529061158943 / 50000000000000 : ℝ)) = (1250000000000000000000000000 / 3161518502640852989497699161 : ℝ) := by norm_num
    rw [e] at this; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 35563919618569 : ℝ) ≤ (70180516032621 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (1882584801379 / 2500000000000 : ℝ) ≤ Real.arctan (1 / (26672939713927 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (106691758855707 / 100000000000000 : ℝ)) ≤ (70180516032621 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_680 : ∀ t : ℝ, (18213010252359 / 16000000000000 : ℝ) < t → t ≤ (1946637295669 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (168502135005455457605183 / 3125000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1946637295669 / 1600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_681
  have hV : (17528679900644804251837784415044561 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (18213010252359 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_680 (Vfield_monotoneOn (show (18213010252359 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (18213010252359 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_681 : (18155406556000236159866441615367729 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1946637295669 / 1600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1946637295669 / 1600000000000 : ℝ) := by norm_num
  have hs1 : (110301781934523 / 100000000000000 : ℝ) ≤ Real.sqrt (1946637295669 / 1600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1946637295669 / 1600000000000 : ℝ) ≤ (27575445483631 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (27575445483631 / 25000000000000 : ℝ) = (25000000000000 / 27575445483631 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (110301781934523 / 100000000000000 : ℝ) = (2500000000000 / 36767260644841 : ℝ) := by norm_num
  have hL1 : (19899907116239 / 25000000000000 : ℝ) ≤ Real.log (1 + (1946637295669 / 1600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1946637295669 / 1600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (802849974041 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : (368225789955147 / 1000000000000000 : ℝ) ≤ Real.arctan (2500000000000000000000000000 / 6479647708702324331297804759 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (368225789955147 / 500000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 27575445483631 : ℝ) := by
    have hw : Real.sqrt (1 + (25000000000000 / 27575445483631 : ℝ) ^ 2) ≤ (134978894993689 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
    have := arctan_ge_half (by norm_num) hw
    have e : (25000000000000 / 27575445483631 : ℝ) / (1 + (134978894993689 / 100000000000000 : ℝ)) = (2500000000000000000000000000 / 6479647708702324331297804759 : ℝ) := by norm_num
    rw [e] at this; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 36767260644841 : ℝ) ≤ (1357815518977 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (368225789955147 / 500000000000000 : ℝ) ≤ Real.arctan (1 / (27575445483631 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (110301781934523 / 100000000000000 : ℝ)) ≤ (1357815518977 / 20000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_681 : ∀ t : ℝ, (1946637295669 / 1600000000000 : ℝ) < t → t ≤ (2746637295669 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (18323011354893284491293279 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2746637295669 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_682
  have hV : (18155406556000236159866441615367729 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1946637295669 / 1600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_681 (Vfield_monotoneOn (show (1946637295669 / 1600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1946637295669 / 1600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_682 : (19349487434554307036064352782279743 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (2746637295669 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2746637295669 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (117188678968341 / 100000000000000 : ℝ) ≤ Real.sqrt (2746637295669 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2746637295669 / 2000000000000 : ℝ) ≤ (58594339484171 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (58594339484171 / 50000000000000 : ℝ) = (50000000000000 / 58594339484171 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (117188678968341 / 100000000000000 : ℝ) = (2500000000000 / 39062892989447 : ℝ) := by norm_num
  have hL1 : (86428924891813 / 100000000000000 : ℝ) ≤ Real.log (1 + (2746637295669 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2746637295669 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (32131773346169 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : (176605272008289 / 500000000000000 : ℝ) ≤ Real.arctan (500000000000000000000000000 / 1356222345585293656062102679 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (176605272008289 / 250000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 58594339484171 : ℝ) := by
    have hw : Real.sqrt (1 + (50000000000000 / 58594339484171 : ℝ) ^ 2) ≤ (13145961837349 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
    have := arctan_ge_half (by norm_num) hw
    have e : (50000000000000 / 58594339484171 : ℝ) / (1 + (13145961837349 / 10000000000000 : ℝ)) = (500000000000000000000000000 / 1356222345585293656062102679 : ℝ) := by norm_num
    rw [e] at this; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 39062892989447 : ℝ) ≤ (63912191547799 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (176605272008289 / 250000000000000 : ℝ) ≤ Real.arctan (1 / (58594339484171 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (117188678968341 / 100000000000000 : ℝ)) ≤ (63912191547799 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_682 : ∀ t : ℝ, (2746637295669 / 2000000000000 : ℝ) < t → t ≤ (6746637295669 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (39665646947802634623546901 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (6746637295669 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_683
  have hV : (19349487434554307036064352782279743 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2746637295669 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_682 (Vfield_monotoneOn (show (2746637295669 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2746637295669 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_683 : (1077123751888125030543531896696157 / 125000000000000000000000000000000 : ℝ) ≤ Vfield (6746637295669 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (6746637295669 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (6493572444959 / 5000000000000 : ℝ) ≤ Real.sqrt (6746637295669 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (6746637295669 / 4000000000000 : ℝ) ≤ (129871448899181 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (129871448899181 / 100000000000000 : ℝ) = (100000000000000 / 129871448899181 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6493572444959 / 5000000000000 : ℝ) = (375000000000 / 6493572444959 : ℝ) := by norm_num
  have hL1 : (98829853314839 / 100000000000000 : ℝ) ≤ Real.log (1 + (6746637295669 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((6746637295669 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (52607928720709 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : (32808690420463 / 100000000000000 : ℝ) ≤ Real.arctan (156250000000000000000000000 / 459034015033018216859166517 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (32808690420463 / 50000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 129871448899181 : ℝ) := by
    have hw : Real.sqrt (1 + (100000000000000 / 129871448899181 : ℝ) ^ 2) ≤ (1972026017257 / 1562500000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
    have := arctan_ge_half (by norm_num) hw
    have e : (100000000000000 / 129871448899181 : ℝ) / (1 + (1972026017257 / 1562500000000 : ℝ)) = (156250000000000000000000000 / 459034015033018216859166517 : ℝ) := by norm_num
    rw [e] at this; linarith [hA4]
  have hA5 : Real.arctan (375000000000 / 6493572444959 : ℝ) ≤ (57685343624467 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (32808690420463 / 50000000000000 : ℝ) ≤ Real.arctan (1 / (129871448899181 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6493572444959 / 5000000000000 : ℝ)) ≤ (57685343624467 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_683 : ∀ t : ℝ, (6746637295669 / 4000000000000 : ℝ) < t → t ≤ (2 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (1423430150552660227493191 / 2500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_684
  have hV : (1077123751888125030543531896696157 / 125000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (6746637295669 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_683 (Vfield_monotoneOn (show (6746637295669 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (6746637295669 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
