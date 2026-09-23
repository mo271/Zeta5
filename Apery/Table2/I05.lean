import Apery.Table2.U05
import Apery.Table2.U06

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_200 : (5981621305360960613221901983228527 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (2479551745141 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2479551745141 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (19683240591383 / 50000000000000 : ℝ) ≤ Real.sqrt (2479551745141 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2479551745141 / 16000000000000 : ℝ) ≤ (39366481182767 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39366481182767 / 100000000000000 : ℝ) = (100000000000000 / 39366481182767 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (19683240591383 / 50000000000000 : ℝ) = (3750000000000 / 19683240591383 : ℝ) := by norm_num
  have hL1 : (576304349857 / 4000000000000 : ℝ) ≤ Real.log (1 + (2479551745141 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2479551745141 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-182885725599851 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39366481182767 / 100000000000000 : ℝ) ≤ (187516552955771 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119576322088335461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 39366481182767 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 39366481182767 : ℝ) = (39366481182767 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 19683240591383 : ℝ) ≤ (94130640258227 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119576322088335461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39366481182767 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (19683240591383 / 50000000000000 : ℝ)) ≤ (94130640258227 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_200 : ∀ t : ℝ, (2479551745141 / 16000000000000 : ℝ) < t → t ≤ (19893193996399 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-26598870611921795448146677 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19893193996399 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_201
  have hV : (5981621305360960613221901983228527 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2479551745141 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_200 (Vfield_monotoneOn (show (2479551745141 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2479551745141 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_201 : (11981305949401432553917413694399981 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (19893193996399 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19893193996399 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (39422782511749 / 100000000000000 : ℝ) ≤ Real.sqrt (19893193996399 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19893193996399 / 128000000000000 : ℝ) ≤ (157691130047 / 400000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (157691130047 / 400000000000 : ℝ) = (400000000000 / 157691130047 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (39422782511749 / 100000000000000 : ℝ) = (7500000000000 / 39422782511749 : ℝ) := by norm_num
  have hL1 : (288920174269 / 2000000000000 : ℝ) ≤ Real.log (1 + (19893193996399 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19893193996399 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-18260989071053 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (157691130047 / 400000000000 : ℝ) ≤ (375520481563763 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119527584523113361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (400000000000 / 157691130047 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (400000000000 / 157691130047 : ℝ) = (157691130047 / 400000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 39422782511749 : ℝ) ≤ (93999355724489 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119527584523113361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (157691130047 / 400000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (39422782511749 / 100000000000000 : ℝ)) ≤ (93999355724489 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_201 : ∀ t : ℝ, (19893193996399 / 128000000000000 : ℝ) < t → t ≤ (1994997403167 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-212592781595739050430173053 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1994997403167 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_202
  have hV : (11981305949401432553917413694399981 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19893193996399 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_201 (Vfield_monotoneOn (show (19893193996399 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19893193996399 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_202 : (2999837407220898752099924675445633 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (1994997403167 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1994997403167 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (9869750887257 / 25000000000000 : ℝ) ≤ Real.sqrt (1994997403167 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1994997403167 / 12800000000000 : ℝ) ≤ (39479003549029 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39479003549029 / 100000000000000 : ℝ) = (100000000000000 / 39479003549029 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (9869750887257 / 25000000000000 : ℝ) = (625000000000 / 3289916962419 : ℝ) := by norm_num
  have hL1 : (14484393940559 / 100000000000000 : ℝ) ≤ Real.log (1 + (1994997403167 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1994997403167 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-36466962915527 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39479003549029 / 100000000000000 : ℝ) ≤ (188003487676379 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119478935144213861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 39479003549029 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 39479003549029 : ℝ) = (39479003549029 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (625000000000 / 3289916962419 : ℝ) ≤ (93868619034381 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119478935144213861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39479003549029 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (9869750887257 / 25000000000000 : ℝ)) ≤ (93868619034381 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_202 : ∀ t : ℝ, (1994997403167 / 12800000000000 : ℝ) < t → t ≤ (20006754066941 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-212396879878256695594943851 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20006754066941 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_203
  have hV : (2999837407220898752099924675445633 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1994997403167 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_202 (Vfield_monotoneOn (show (1994997403167 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1994997403167 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_203 : (6008686854937777080485816371416099 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (20006754066941 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20006754066941 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (19767572318571 / 50000000000000 : ℝ) ≤ Real.sqrt (20006754066941 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20006754066941 / 128000000000000 : ℝ) ≤ (39535144637143 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39535144637143 / 100000000000000 : ℝ) = (100000000000000 / 39535144637143 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (19767572318571 / 50000000000000 : ℝ) = (1250000000000 / 6589190772857 : ℝ) := by norm_num
  have hL1 : (7261382219533 / 50000000000000 : ℝ) ≤ Real.log (1 + (20006754066941 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20006754066941 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-182060493038297 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39535144637143 / 100000000000000 : ℝ) ≤ (94123147729553 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119430373587668461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 39535144637143 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 39535144637143 : ℝ) = (39535144637143 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 6589190772857 : ℝ) ≤ (46869213193917 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119430373587668461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39535144637143 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (19767572318571 / 50000000000000 : ℝ)) ≤ (46869213193917 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_203 : ∀ t : ℝ, (20006754066941 / 128000000000000 : ℝ) < t → t ≤ (5015883525553 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-212203156297500969800649653 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5015883525553 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_204
  have hV : (6008686854937777080485816371416099 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20006754066941 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_203 (Vfield_monotoneOn (show (20006754066941 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20006754066941 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_204 : (6017689126391965866450751970293131 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (5015883525553 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5015883525553 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (19795603058099 / 50000000000000 : ℝ) ≤ Real.sqrt (5015883525553 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5015883525553 / 32000000000000 : ℝ) ≤ (39591206116199 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39591206116199 / 100000000000000 : ℝ) = (100000000000000 / 39591206116199 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (19795603058099 / 50000000000000 : ℝ) = (3750000000000 / 19795603058099 : ℝ) := by norm_num
  have hL1 : (3640280055067 / 25000000000000 : ℝ) ≤ Real.log (1 + (5015883525553 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5015883525553 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-181786921963811 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39591206116199 / 100000000000000 : ℝ) ≤ (376977331874593 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119381899492030361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 39591206116199 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 39591206116199 : ℝ) = (39591206116199 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 19795603058099 : ℝ) ≤ (187217548043183 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119381899492030361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39591206116199 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (19795603058099 / 50000000000000 : ℝ)) ≤ (187217548043183 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_204 : ∀ t : ℝ, (5015883525553 / 32000000000000 : ℝ) < t → t ≤ (20120314137483 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-53002879052746460830809883 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20120314137483 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_205
  have hV : (6017689126391965866450751970293131 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5015883525553 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_204 (Vfield_monotoneOn (show (5015883525553 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5015883525553 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_205 : (120533633177190146672383729225791 / 50000000000000000000000000000000 : ℝ) ≤ Vfield (20120314137483 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20120314137483 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (396471883239 / 1000000000000 : ℝ) ≤ Real.sqrt (20120314137483 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20120314137483 / 128000000000000 : ℝ) ≤ (39647188323901 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39647188323901 / 100000000000000 : ℝ) = (100000000000000 / 39647188323901 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (396471883239 / 1000000000000 : ℝ) = (25000000000 / 132157294413 : ℝ) := by norm_num
  have hL1 : (14599461295451 / 100000000000000 : ℝ) ≤ Real.log (1 + (20120314137483 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20120314137483 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-709039442419 / 390625000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39647188323901 / 100000000000000 : ℝ) ≤ (4718265022643 / 12500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119333512498345661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 39647188323901 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 39647188323901 : ℝ) = (39647188323901 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (25000000000 / 132157294413 : ℝ) ≤ (186959316417481 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119333512498345661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39647188323901 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (396471883239 / 1000000000000 : ℝ)) ≤ (186959316417481 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_205 : ∀ t : ℝ, (20120314137483 / 128000000000000 : ℝ) < t → t ≤ (10088547086377 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-211821872735909329910577773 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10088547086377 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_206
  have hV : (120533633177190146672383729225791 / 50000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20120314137483 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_205 (Vfield_monotoneOn (show (20120314137483 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20120314137483 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_206 : (3017832241124057211675819224853717 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (10088547086377 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10088547086377 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (9925772898893 / 25000000000000 : ℝ) ≤ Real.sqrt (10088547086377 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10088547086377 / 64000000000000 : ℝ) ≤ (39703091595573 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39703091595573 / 100000000000000 : ℝ) = (100000000000000 / 39703091595573 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (9925772898893 / 25000000000000 : ℝ) = (1875000000000 / 9925772898893 : ℝ) := by norm_num
  have hL1 : (14637787675887 / 100000000000000 : ℝ) ≤ Real.log (1 + (10088547086377 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10088547086377 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-18124201486317 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39703091595573 / 100000000000000 : ℝ) ≤ (94486051073401 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119285212250129261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 39703091595573 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 39703091595573 : ℝ) = (39703091595573 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 9925772898893 : ℝ) ≤ (93351075258263 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119285212250129261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39703091595573 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (9925772898893 / 25000000000000 : ℝ)) ≤ (93351075258263 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_206 : ∀ t : ℝ, (10088547086377 / 64000000000000 : ℝ) < t → t ≤ (809354968321 / 5120000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-13227134116184695664811203 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (809354968321 / 5120000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_207
  have hV : (3017832241124057211675819224853717 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10088547086377 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_206 (Vfield_monotoneOn (show (10088547086377 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10088547086377 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_207 : (6044637626318340772364745535841441 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (809354968321 / 5120000000000 : ℝ) := by
  have hp : (0 : ℝ) < (809354968321 / 5120000000000 : ℝ) := by norm_num
  have hs1 : (19879458132089 / 50000000000000 : ℝ) ≤ Real.sqrt (809354968321 / 5120000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (809354968321 / 5120000000000 : ℝ) ≤ (39758916264179 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39758916264179 / 100000000000000 : ℝ) = (100000000000000 / 39758916264179 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (19879458132089 / 50000000000000 : ℝ) = (3750000000000 / 19879458132089 : ℝ) := by norm_num
  have hL1 : (14676099372837 / 100000000000000 : ℝ) ≤ Real.log (1 + (809354968321 / 5120000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((809354968321 / 5120000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-180970670747103 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39758916264179 / 100000000000000 : ℝ) ≤ (189213171430727 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119236998393344261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 39758916264179 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 39758916264179 : ℝ) = (39758916264179 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 19879458132089 : ℝ) ≤ (93223021514601 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119236998393344261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39758916264179 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (19879458132089 / 50000000000000 : ℝ)) ≤ (93223021514601 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_207 : ∀ t : ℝ, (809354968321 / 5120000000000 : ℝ) < t → t ≤ (634082945103 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-8457930466961649398642007 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (634082945103 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_208
  have hV : (6044637626318340772364745535841441 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (809354968321 / 5120000000000 : ℝ) := by norm_num
    refine le_trans V_pt_207 (Vfield_monotoneOn (show (809354968321 / 5120000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (809354968321 / 5120000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_208 : (242144044827415688924750441611183 / 100000000000000000000000000000000 : ℝ) ≤ Vfield (634082945103 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (634082945103 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (796293253207 / 2000000000000 : ℝ) ≤ Real.sqrt (634082945103 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (634082945103 / 4000000000000 : ℝ) ≤ (39814662660351 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39814662660351 / 100000000000000 : ℝ) = (100000000000000 / 39814662660351 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (796293253207 / 2000000000000 : ℝ) = (150000000000 / 796293253207 : ℝ) := by norm_num
  have hL1 : (7357198198773 / 50000000000000 : ℝ) ≤ Real.log (1 + (634082945103 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((634082945103 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-90350030457671 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39814662660351 / 100000000000000 : ℝ) ≤ (9472690525779 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119188870576373661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 39814662660351 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 39814662660351 : ℝ) = (39814662660351 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (150000000000 / 796293253207 : ℝ) ≤ (37238197342883 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119188870576373661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39814662660351 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (796293253207 / 2000000000000 : ℝ)) ≤ (37238197342883 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_208 : ∀ t : ℝ, (634082945103 / 4000000000000 : ℝ) < t → t ≤ (20347434278567 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-211264151726189821744656991 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20347434278567 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_209
  have hV : (242144044827415688924750441611183 / 100000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (634082945103 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_208 (Vfield_monotoneOn (show (634082945103 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (634082945103 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_209 : (12125109989638737330613766935335983 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (20347434278567 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20347434278567 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (39870331112407 / 100000000000000 : ℝ) ≤ Real.sqrt (20347434278567 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20347434278567 / 128000000000000 : ℝ) ≤ (4983791389051 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4983791389051 / 12500000000000 : ℝ) = (12500000000000 / 4983791389051 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (39870331112407 / 100000000000000 : ℝ) = (7500000000000 / 39870331112407 : ℝ) := by norm_num
  have hL1 : (14752678761249 / 100000000000000 : ℝ) ≤ Real.log (1 + (20347434278567 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20347434278567 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-36086036280903 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4983791389051 / 12500000000000 : ℝ) ≤ (94847010573723 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119140828450000461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 4983791389051 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 4983791389051 : ℝ) = (4983791389051 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 39870331112407 : ℝ) ≤ (185936974400253 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119140828450000461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4983791389051 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (39870331112407 / 100000000000000 : ℝ)) ≤ (185936974400253 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_209 : ∀ t : ℝ, (20347434278567 / 128000000000000 : ℝ) < t → t ≤ (10202107156919 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-42216350488797373449267849 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10202107156919 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_210
  have hV : (12125109989638737330613766935335983 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20347434278567 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_209 (Vfield_monotoneOn (show (20347434278567 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20347434278567 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_210 : (6071499278046980125908247342318879 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (10202107156919 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10202107156919 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (19962960973191 / 50000000000000 : ℝ) ≤ Real.sqrt (10202107156919 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10202107156919 / 64000000000000 : ℝ) ≤ (39925921946383 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39925921946383 / 100000000000000 : ℝ) = (100000000000000 / 39925921946383 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (19962960973191 / 50000000000000 : ℝ) = (1250000000000 / 6654320324397 : ℝ) := by norm_num
  have hL1 : (7395473237583 / 50000000000000 : ℝ) ≤ Real.log (1 + (10202107156919 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10202107156919 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-90080514141627 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39925921946383 / 100000000000000 : ℝ) ≤ (37986761012109 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119092871667380661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 39925921946383 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 39925921946383 : ℝ) = (39925921946383 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 6654320324397 : ℝ) ≤ (185683998983117 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119092871667380661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39925921946383 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (19962960973191 / 50000000000000 : ℝ)) ≤ (185683998983117 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_210 : ∀ t : ℝ, (10202107156919 / 64000000000000 : ℝ) < t → t ≤ (20460994349109 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-105450502323199298535375727 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20460994349109 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_211
  have hV : (6071499278046980125908247342318879 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10202107156919 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_210 (Vfield_monotoneOn (show (10202107156919 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10202107156919 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_211 : (12160867999102143590835406177707453 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (20460994349109 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20460994349109 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (39981435486037 / 100000000000000 : ℝ) ≤ Real.sqrt (20460994349109 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20460994349109 / 128000000000000 : ℝ) ≤ (19990717743019 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (19990717743019 / 50000000000000 : ℝ) = (50000000000000 / 19990717743019 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (39981435486037 / 100000000000000 : ℝ) = (7500000000000 / 39981435486037 : ℝ) := by norm_num
  have hL1 : (2965839910101 / 20000000000000 : ℝ) ≤ Real.log (1 + (20460994349109 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20460994349109 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-44973149412963 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (19990717743019 / 50000000000000 : ℝ) ≤ (380346327954629 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119044999884026761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 19990717743019 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 19990717743019 : ℝ) = (19990717743019 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 39981435486037 : ℝ) ≤ (185432053426921 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119044999884026761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (19990717743019 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (39981435486037 / 100000000000000 : ℝ)) ≤ (185432053426921 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_211 : ∀ t : ℝ, (20460994349109 / 128000000000000 : ℝ) < t → t ≤ (1025888719219 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-26340231639045353439991581 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1025888719219 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_212
  have hV : (12160867999102143590835406177707453 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20460994349109 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_211 (Vfield_monotoneOn (show (20460994349109 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20460994349109 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_212 : (3044679594186452675735700023223487 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (1025888719219 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1025888719219 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (10009218013223 / 25000000000000 : ℝ) ≤ Real.sqrt (1025888719219 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1025888719219 / 6400000000000 : ℝ) ≤ (40036872052893 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (40036872052893 / 100000000000000 : ℝ) = (100000000000000 / 40036872052893 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10009218013223 / 25000000000000 : ℝ) = (1875000000000 / 10009218013223 : ℝ) := by norm_num
  have hL1 : (14867437998463 / 100000000000000 : ℝ) ≤ Real.log (1 + (1025888719219 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1025888719219 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-89812442820959 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (40036872052893 / 100000000000000 : ℝ) ≤ (95206049804277 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118997212757778861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 40036872052893 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 40036872052893 : ℝ) = (40036872052893 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 10009218013223 : ℝ) ≤ (92590565381117 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118997212757778861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (40036872052893 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10009218013223 / 25000000000000 : ℝ)) ≤ (92590565381117 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_212 : ∀ t : ℝ, (1025888719219 / 6400000000000 : ℝ) < t → t ≤ (20574554419651 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-5263606155135533184578611 / 2500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20574554419651 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_213
  have hV : (3044679594186452675735700023223487 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1025888719219 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_212 (Vfield_monotoneOn (show (1025888719219 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1025888719219 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_213 : (2439309949365030029439590703273481 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (20574554419651 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20574554419651 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (8018446393249 / 20000000000000 : ℝ) ≤ Real.sqrt (20574554419651 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20574554419651 / 128000000000000 : ℝ) ≤ (20046115983123 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20046115983123 / 50000000000000 : ℝ) = (50000000000000 / 20046115983123 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8018446393249 / 20000000000000 : ℝ) = (1500000000000 / 8018446393249 : ℝ) := by norm_num
  have hL1 : (14905661830219 / 100000000000000 : ℝ) ≤ Real.log (1 + (20574554419651 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20574554419651 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3587157768321 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20046115983123 / 50000000000000 : ℝ) ≤ (190650613653527 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118949509948784261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 20046115983123 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 20046115983123 : ℝ) = (20046115983123 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 8018446393249 : ℝ) ≤ (92465612042741 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118949509948784261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20046115983123 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8018446393249 / 20000000000000 : ℝ)) ≤ (92465612042741 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_213 : ∀ t : ℝ, (20574554419651 / 128000000000000 : ℝ) < t → t ≤ (10315667227461 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-210368135534784835856916081 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10315667227461 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_214
  have hV : (2439309949365030029439590703273481 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20574554419651 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_213 (Vfield_monotoneOn (show (20574554419651 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20574554419651 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_214 : (12214362166859369038508692646848879 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (10315667227461 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10315667227461 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (40147515543191 / 100000000000000 : ℝ) ≤ Real.sqrt (10315667227461 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10315667227461 / 64000000000000 : ℝ) ≤ (5018439442899 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5018439442899 / 12500000000000 : ℝ) = (12500000000000 / 5018439442899 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (40147515543191 / 100000000000000 : ℝ) = (7500000000000 / 40147515543191 : ℝ) := by norm_num
  have hL1 : (7471935528473 / 50000000000000 : ℝ) ≤ Real.log (1 + (10315667227461 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10315667227461 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-71636640867 / 40000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5018439442899 / 12500000000000 : ℝ) ≤ (190888707800061 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118901891119477461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 5018439442899 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 5018439442899 : ℝ) = (5018439442899 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 40147515543191 : ℝ) ≤ (92341163279079 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118901891119477461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5018439442899 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (40147515543191 / 100000000000000 : ℝ)) ≤ (92341163279079 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_214 : ∀ t : ℝ, (10315667227461 / 64000000000000 : ℝ) < t → t ≤ (20688114490193 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-210193475673214011402427247 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20688114490193 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_215
  have hV : (12214362166859369038508692646848879 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10315667227461 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_214 (Vfield_monotoneOn (show (10315667227461 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10315667227461 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_215 : (2446431138817690994656545955436601 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (20688114490193 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20688114490193 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (8040544619729 / 20000000000000 : ℝ) ≤ Real.sqrt (20688114490193 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20688114490193 / 128000000000000 : ℝ) ≤ (20101361549323 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20101361549323 / 50000000000000 : ℝ) = (50000000000000 / 20101361549323 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8040544619729 / 20000000000000 : ℝ) = (1500000000000 / 8040544619729 : ℝ) := by norm_num
  have hL1 : (7491032844899 / 50000000000000 : ℝ) ≤ Real.log (1 + (20688114490193 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20688114490193 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3576520462397 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20101361549323 / 50000000000000 : ℝ) ≤ (95563191862333 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118854355934556461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 20101361549323 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 20101361549323 : ℝ) = (20101361549323 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 8040544619729 : ℝ) ≤ (184434431406031 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118854355934556461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20101361549323 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8040544619729 / 20000000000000 : ℝ)) ≤ (184434431406031 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_215 : ∀ t : ℝ, (20688114490193 / 128000000000000 : ℝ) < t → t ≤ (2593111815683 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-52505055972598568875297307 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2593111815683 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_216
  have hV : (2446431138817690994656545955436601 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20688114490193 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_215 (Vfield_monotoneOn (show (20688114490193 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20688114490193 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_216 : (6124965192737577823577618583876689 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (2593111815683 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2593111815683 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (20128927472681 / 50000000000000 : ℝ) ≤ Real.sqrt (2593111815683 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2593111815683 / 16000000000000 : ℝ) ≤ (40257854945363 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (40257854945363 / 100000000000000 : ℝ) = (100000000000000 / 40257854945363 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (20128927472681 / 50000000000000 : ℝ) = (3750000000000 / 20128927472681 : ℝ) := by norm_num
  have hL1 : (187753071749 / 1250000000000 : ℝ) ≤ Real.log (1 + (2593111815683 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2593111815683 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-178561147526689 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (40257854945363 / 100000000000000 : ℝ) ≤ (95681821546317 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118806904060962861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 40257854945363 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 40257854945363 : ℝ) = (40257854945363 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 20128927472681 : ℝ) ≤ (184187531918371 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118806904060962861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (40257854945363 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (20128927472681 / 50000000000000 : ℝ)) ≤ (184187531918371 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_216 : ∀ t : ℝ, (2593111815683 / 16000000000000 : ℝ) < t → t ≤ (4160334912147 / 25600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-209848339924151509302055897 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4160334912147 / 25600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_217
  have hV : (6124965192737577823577618583876689 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2593111815683 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_216 (Vfield_monotoneOn (show (2593111815683 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2593111815683 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_217 : (12267686297707785299850743808441009 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (4160334912147 / 25600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4160334912147 / 25600000000000 : ℝ) := by norm_num
  have hs1 : (40312911393961 / 100000000000000 : ℝ) ≤ Real.sqrt (4160334912147 / 25600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4160334912147 / 25600000000000 : ℝ) ≤ (20156455696981 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20156455696981 / 50000000000000 : ℝ) = (50000000000000 / 20156455696981 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (40312911393961 / 100000000000000 : ℝ) = (7500000000000 / 40312911393961 : ℝ) := by norm_num
  have hL1 : (15058411218443 / 100000000000000 : ℝ) ≤ Real.log (1 + (4160334912147 / 25600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4160334912147 / 25600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-178296971671301 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20156455696981 / 50000000000000 : ℝ) ≤ (383200975116327 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118759535167856961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 20156455696981 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 20156455696981 : ℝ) = (20156455696981 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 40312911393961 : ℝ) ≤ (91970810723587 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118759535167856961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20156455696981 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (40312911393961 / 100000000000000 : ℝ)) ≤ (91970810723587 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_217 : ∀ t : ℝ, (4160334912147 / 25600000000000 : ℝ) < t → t ≤ (10429227298003 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-209677785774909788097272433 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10429227298003 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_218
  have hV : (12267686297707785299850743808441009 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4160334912147 / 25600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_217 (Vfield_monotoneOn (show (4160334912147 / 25600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4160334912147 / 25600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_218 : (12285423487200159834165153222796629 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (10429227298003 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10429227298003 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (40367892752941 / 100000000000000 : ℝ) ≤ Real.sqrt (10429227298003 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10429227298003 / 64000000000000 : ℝ) ≤ (20183946376471 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20183946376471 / 50000000000000 : ℝ) = (50000000000000 / 20183946376471 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (40367892752941 / 100000000000000 : ℝ) = (7500000000000 / 40367892752941 : ℝ) := by norm_num
  have hL1 : (3019312427297 / 20000000000000 : ℝ) ≤ Real.log (1 + (10429227298003 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10429227298003 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-35606698373269 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20183946376471 / 50000000000000 : ℝ) ≤ (383673837528883 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118712248926601361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 20183946376471 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 20183946376471 : ℝ) = (20183946376471 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 40367892752941 : ℝ) ≤ (45924173351607 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118712248926601361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20183946376471 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (40367892752941 / 100000000000000 : ℝ)) ≤ (45924173351607 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_218 : ∀ t : ℝ, (10429227298003 / 64000000000000 : ℝ) < t → t ≤ (20915234631277 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-104754262760959215723163967 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20915234631277 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_219
  have hV : (12285423487200159834165153222796629 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10429227298003 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_218 (Vfield_monotoneOn (show (10429227298003 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10429227298003 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_219 : (6151571005046872987602267353420919 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (20915234631277 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20915234631277 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (20211399664351 / 50000000000000 : ℝ) ≤ Real.sqrt (20915234631277 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20915234631277 / 128000000000000 : ℝ) ≤ (40422799328703 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (40422799328703 / 100000000000000 : ℝ) = (100000000000000 / 40422799328703 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (20211399664351 / 50000000000000 : ℝ) = (3750000000000 / 20211399664351 : ℝ) := by norm_num
  have hL1 : (236479664143 / 1562500000000 : ℝ) ≤ Real.log (1 + (20915234631277 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20915234631277 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-177770704453551 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (40422799328703 / 100000000000000 : ℝ) ≤ (96036469171877 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118665045010738861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 40422799328703 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 40422799328703 : ℝ) = (40422799328703 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 20211399664351 : ℝ) ≤ (183452741271369 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118665045010738861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (40422799328703 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (20211399664351 / 50000000000000 : ℝ)) ≤ (183452741271369 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_219 : ∀ t : ℝ, (20915234631277 / 128000000000000 : ℝ) < t → t ≤ (5243003666637 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-261675656448115308859621 / 125000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5243003666637 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_220
  have hV : (6151571005046872987602267353420919 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20915234631277 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_219 (Vfield_monotoneOn (show (20915234631277 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20915234631277 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_220 : (12320841922260138477091263220856023 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (5243003666637 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5243003666637 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (40477631425567 / 100000000000000 : ℝ) ≤ Real.sqrt (5243003666637 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5243003666637 / 32000000000000 : ℝ) ≤ (1264925982049 / 3125000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1264925982049 / 3125000000000 : ℝ) = (3125000000000 / 1264925982049 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (40477631425567 / 100000000000000 : ℝ) = (7500000000000 / 40477631425567 : ℝ) := by norm_num
  have hL1 : (7586410167769 / 50000000000000 : ℝ) ≤ Real.log (1 + (5243003666637 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5243003666637 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-88754302901707 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1264925982049 / 3125000000000 : ℝ) ≤ (384617095835189 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118617923095970761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (3125000000000 / 1264925982049 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (3125000000000 / 1264925982049 : ℝ) = (1264925982049 / 3125000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 40477631425567 : ℝ) ≤ (183209758577743 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118617923095970761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1264925982049 / 3125000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (40477631425567 / 100000000000000 : ℝ)) ≤ (183209758577743 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_220 : ∀ t : ℝ, (5243003666637 / 32000000000000 : ℝ) < t → t ≤ (21028794701819 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-209173752443905051609840227 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (21028794701819 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_221
  have hV : (12320841922260138477091263220856023 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5243003666637 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_220 (Vfield_monotoneOn (show (5243003666637 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5243003666637 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_221 : (12338523279302466888981049386405969 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (21028794701819 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (21028794701819 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (40532389345801 / 100000000000000 : ℝ) ≤ Real.sqrt (21028794701819 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (21028794701819 / 128000000000000 : ℝ) ≤ (20266194672901 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20266194672901 / 50000000000000 : ℝ) = (50000000000000 / 20266194672901 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (40532389345801 / 100000000000000 : ℝ) = (7500000000000 / 40532389345801 : ℝ) := by norm_num
  have hL1 : (7605463819361 / 50000000000000 : ℝ) ≤ Real.log (1 + (21028794701819 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((21028794701819 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-177247192314893 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20266194672901 / 50000000000000 : ℝ) ≤ (385087498193527 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118570882860136961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 20266194672901 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 20266194672901 : ℝ) = (20266194672901 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 40532389345801 : ℝ) ≤ (182967738921083 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118570882860136961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20266194672901 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (40532389345801 / 100000000000000 : ℝ)) ≤ (182967738921083 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_221 : ∀ t : ℝ, (21028794701819 / 128000000000000 : ℝ) < t → t ≤ (2108557473709 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-104504088384959845303302891 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2108557473709 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_222
  have hV : (12338523279302466888981049386405969 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (21028794701819 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_221 (Vfield_monotoneOn (show (21028794701819 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (21028794701819 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_222 : (12356186136556491991018061938389701 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2108557473709 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2108557473709 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (40587073389629 / 100000000000000 : ℝ) ≤ Real.sqrt (2108557473709 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2108557473709 / 12800000000000 : ℝ) ≤ (4058707338963 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4058707338963 / 10000000000000 : ℝ) = (10000000000000 / 4058707338963 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (40587073389629 / 100000000000000 : ℝ) = (7500000000000 / 40587073389629 : ℝ) := by norm_num
  have hL1 : (3812255106443 / 25000000000000 : ℝ) ≤ Real.log (1 + (2108557473709 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2108557473709 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-88493230207557 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4058707338963 / 10000000000000 : ℝ) ≤ (192778543481461 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118523923983197461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 4058707338963 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 4058707338963 : ℝ) = (4058707338963 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 40587073389629 : ℝ) ≤ (36545335191203 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118523923983197461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4058707338963 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (40587073389629 / 100000000000000 : ℝ)) ≤ (36545335191203 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_222 : ∀ t : ℝ, (2108557473709 / 12800000000000 : ℝ) < t → t ≤ (21142354772361 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-4176875380804155441445233 / 2000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (21142354772361 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_223
  have hV : (12356186136556491991018061938389701 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2108557473709 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_222 (Vfield_monotoneOn (show (2108557473709 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2108557473709 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_223 : (12373830549093012592105571680937633 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (21142354772361 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (21142354772361 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (40641683855257 / 100000000000000 : ℝ) ≤ Real.sqrt (21142354772361 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (21142354772361 / 128000000000000 : ℝ) ≤ (20320841927629 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20320841927629 / 50000000000000 : ℝ) = (50000000000000 / 20320841927629 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (40641683855257 / 100000000000000 : ℝ) = (7500000000000 / 40641683855257 : ℝ) := by norm_num
  have hL1 : (7643549353871 / 50000000000000 : ℝ) ≤ Real.log (1 + (21142354772361 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((21142354772361 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-176726406559077 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20320841927629 / 50000000000000 : ℝ) ≤ (386025865322789 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118477046147210761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 20320841927629 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 20320841927629 : ℝ) = (20320841927629 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 40641683855257 : ℝ) ≤ (182486563395543 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118477046147210761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20320841927629 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (40641683855257 / 100000000000000 : ℝ)) ≤ (182486563395543 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_223 : ∀ t : ℝ, (21142354772361 / 128000000000000 : ℝ) < t → t ≤ (1324945925477 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-104340250780586797772128521 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1324945925477 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_224
  have hV : (12373830549093012592105571680937633 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (21142354772361 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_223 (Vfield_monotoneOn (show (21142354772361 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (21142354772361 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_224 : (1239145657171921829591350403155641 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (1324945925477 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1324945925477 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (4069622103889 / 10000000000000 : ℝ) ≤ Real.sqrt (1324945925477 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1324945925477 / 8000000000000 : ℝ) ≤ (40696221038891 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (40696221038891 / 100000000000000 : ℝ) = (100000000000000 / 40696221038891 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4069622103889 / 10000000000000 : ℝ) = (750000000000 / 4069622103889 : ℝ) := by norm_num
  have hL1 : (3831290623919 / 25000000000000 : ℝ) ≤ Real.log (1 + (1324945925477 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1324945925477 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-22058378403671 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (40696221038891 / 100000000000000 : ℝ) ≤ (19324691821587 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118430249036315661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 40696221038891 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 40696221038891 : ℝ) = (40696221038891 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (750000000000 / 4069622103889 : ℝ) ≤ (182247395010371 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118430249036315661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (40696221038891 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4069622103889 / 10000000000000 : ℝ)) ≤ (182247395010371 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_224 : ∀ t : ℝ, (1324945925477 / 8000000000000 : ℝ) < t → t ≤ (10656347439087 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-104178641504486459502587443 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10656347439087 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_225
  have hV : (1239145657171921829591350403155641 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1324945925477 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_224 (Vfield_monotoneOn (show (1324945925477 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1324945925477 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_225 : (12426653665160881929844904624106131 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (10656347439087 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10656347439087 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (40805076735099 / 100000000000000 : ℝ) ≤ Real.sqrt (10656347439087 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10656347439087 / 64000000000000 : ℝ) ≤ (408050767351 / 1000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (408050767351 / 1000000000000 : ℝ) = (1000000000000 / 408050767351 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (40805076735099 / 100000000000000 : ℝ) = (2500000000000 / 13601692245033 : ℝ) := by norm_num
  have hL1 : (15401246633541 / 100000000000000 : ℝ) ≤ Real.log (1 + (10656347439087 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10656347439087 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-43987569553873 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (408050767351 / 1000000000000 : ℝ) ≤ (387427369428503 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118336895736639361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1000000000000 / 408050767351 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (1000000000000 / 408050767351 : ℝ) = (408050767351 / 1000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 13601692245033 : ℝ) ≤ (3635437322663 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118336895736639361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (408050767351 / 1000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (40805076735099 / 100000000000000 : ℝ)) ≤ (3635437322663 / 20000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_225 : ∀ t : ℝ, (10656347439087 / 64000000000000 : ℝ) < t → t ≤ (5356563737179 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-8321532962847013789204297 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5356563737179 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_226
  have hV : (12426653665160881929844904624106131 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10656347439087 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_225 (Vfield_monotoneOn (show (10656347439087 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10656347439087 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_226 : (1557722231265906573543739851280137 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (5356563737179 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5356563737179 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (5114205351073 / 12500000000000 : ℝ) ≤ Real.sqrt (5356563737179 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5356563737179 / 32000000000000 : ℝ) ≤ (8182728561717 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8182728561717 / 20000000000000 : ℝ) = (20000000000000 / 8182728561717 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5114205351073 / 12500000000000 : ℝ) = (937500000000 / 5114205351073 : ℝ) := by norm_num
  have hL1 : (3869318231863 / 25000000000000 : ℝ) ≤ Real.log (1 + (5356563737179 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5356563737179 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-175436185775113 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8182728561717 / 20000000000000 : ℝ) ≤ (48544713851671 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118243861598152861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 8182728561717 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 8182728561717 : ℝ) = (8182728561717 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (937500000000 / 5114205351073 : ℝ) ≤ (181300040618339 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118243861598152861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8182728561717 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5114205351073 / 12500000000000 : ℝ)) ≤ (181300040618339 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_226 : ∀ t : ℝ, (5356563737179 / 32000000000000 : ℝ) < t → t ≤ (10769907509629 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-207723444661073015218533983 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10769907509629 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_227
  have hV : (1557722231265906573543739851280137 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5356563737179 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_226 (Vfield_monotoneOn (show (5356563737179 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5356563737179 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_227 : (6248414777875505358106013230388211 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (10769907509629 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10769907509629 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (20510960779419 / 50000000000000 : ℝ) ≤ Real.sqrt (10769907509629 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10769907509629 / 64000000000000 : ℝ) ≤ (41021921558839 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (41021921558839 / 100000000000000 : ℝ) = (100000000000000 / 41021921558839 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (20510960779419 / 50000000000000 : ℝ) = (1250000000000 / 6836986926473 : ℝ) := by norm_num
  have hL1 : (15553241465297 / 100000000000000 : ℝ) ≤ Real.log (1 + (10769907509629 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10769907509629 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-10932795170833 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (41021921558839 / 100000000000000 : ℝ) ≤ (389284885125797 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118151144166909961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 41021921558839 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 41021921558839 : ℝ) = (41021921558839 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 6836986926473 : ℝ) ≤ (45207967660149 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118151144166909961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (41021921558839 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (20510960779419 / 50000000000000 : ℝ)) ≤ (45207967660149 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_227 : ∀ t : ℝ, (10769907509629 / 64000000000000 : ℝ) < t → t ≤ (108266875449 / 640000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2592655994190710621112521 / 1250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (108266875449 / 640000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_228
  have hV : (6248414777875505358106013230388211 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10769907509629 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_227 (Vfield_monotoneOn (show (10769907509629 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10769907509629 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_228 : (6265904603551029077660995536835567 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (108266875449 / 640000000000 : ℝ) := by
  have hp : (0 : ℝ) < (108266875449 / 640000000000 : ℝ) := by norm_num
  have hs1 : (20564957627543 / 50000000000000 : ℝ) ≤ Real.sqrt (108266875449 / 640000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (108266875449 / 640000000000 : ℝ) ≤ (41129915255087 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (41129915255087 / 100000000000000 : ℝ) = (100000000000000 / 41129915255087 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (20564957627543 / 50000000000000 : ℝ) = (3750000000000 / 20564957627543 : ℝ) := by norm_num
  have hL1 : (7814576167381 / 50000000000000 : ℝ) ≤ Real.log (1 + (108266875449 / 640000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((108266875449 / 640000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-87207931165043 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (41129915255087 / 100000000000000 : ℝ) ≤ (24388057286899 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (118058741020451261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 41129915255087 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 41129915255087 : ℝ) = (41129915255087 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 20564957627543 : ℝ) ≤ (180367309234883 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (118058741020451261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (41129915255087 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (20564957627543 / 50000000000000 : ℝ)) ≤ (180367309234883 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_228 : ∀ t : ℝ, (108266875449 / 640000000000 : ℝ) < t → t ≤ (10883467580171 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-207105276514751158740067111 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10883467580171 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_229
  have hV : (6265904603551029077660995536835567 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (108266875449 / 640000000000 : ℝ) := by norm_num
    refine le_trans V_pt_228 (Vfield_monotoneOn (show (108266875449 / 640000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (108266875449 / 640000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_229 : (12566717225237399609494428107844191 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (10883467580171 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10883467580171 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (41237626136839 / 100000000000000 : ℝ) ≤ Real.sqrt (10883467580171 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10883467580171 / 64000000000000 : ℝ) ≤ (1030940653421 / 2500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1030940653421 / 2500000000000 : ℝ) = (2500000000000 / 1030940653421 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41237626136839 / 100000000000000 : ℝ) = (7500000000000 / 41237626136839 : ℝ) := by norm_num
  have hL1 : (15705005623333 / 100000000000000 : ℝ) ≤ Real.log (1 + (10883467580171 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10883467580171 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-8695478910589 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1030940653421 / 2500000000000 : ℝ) ≤ (7822596582451 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (117966649767234661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (2500000000000 / 1030940653421 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (2500000000000 / 1030940653421 : ℝ) = (1030940653421 / 2500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 41237626136839 : ℝ) ≤ (2811036098073 / 15625000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (117966649767234661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1030940653421 / 2500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41237626136839 / 100000000000000 : ℝ)) ≤ (2811036098073 / 15625000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_229 : ∀ t : ℝ, (10883467580171 / 64000000000000 : ℝ) < t → t ≤ (5470123807721 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-4136033899538578786983101 / 2000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5470123807721 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_230
  have hV : (12566717225237399609494428107844191 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10883467580171 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_229 (Vfield_monotoneOn (show (10883467580171 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10883467580171 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_230 : (6300777013625131643717500817694873 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (5470123807721 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5470123807721 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (20672528207217 / 50000000000000 : ℝ) ≤ Real.sqrt (5470123807721 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5470123807721 / 32000000000000 : ℝ) ≤ (8269011282887 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8269011282887 / 20000000000000 : ℝ) = (20000000000000 / 8269011282887 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (20672528207217 / 50000000000000 : ℝ) = (1250000000000 / 6890842735739 : ℝ) := by norm_num
  have hL1 : (7890400709149 / 50000000000000 : ℝ) ≤ Real.log (1 + (5470123807721 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5470123807721 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-34681168884613 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8269011282887 / 20000000000000 : ℝ) ≤ (196023823167043 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (117874868046081061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 8269011282887 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 8269011282887 : ℝ) = (8269011282887 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 6890842735739 : ℝ) ≤ (179448828462711 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (117874868046081061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8269011282887 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (20672528207217 / 50000000000000 : ℝ)) ≤ (179448828462711 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_230 : ∀ t : ℝ, (5470123807721 / 32000000000000 : ℝ) < t → t ≤ (10997027650713 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-206501604569157024683953889 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10997027650713 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_231
  have hV : (6300777013625131643717500817694873 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5470123807721 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_230 (Vfield_monotoneOn (show (5470123807721 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5470123807721 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_231 : (12636320026321939004991565330335099 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (10997027650713 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10997027650713 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (41452208269571 / 100000000000000 : ℝ) ≤ Real.sqrt (10997027650713 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10997027650713 / 64000000000000 : ℝ) ≤ (10363052067393 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (10363052067393 / 25000000000000 : ℝ) = (25000000000000 / 10363052067393 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41452208269571 / 100000000000000 : ℝ) = (7500000000000 / 41452208269571 : ℝ) := by norm_num
  have hL1 : (15856539806747 / 100000000000000 : ℝ) ≤ Real.log (1 + (10997027650713 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10997027650713 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-172904635398869 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (10363052067393 / 25000000000000 : ℝ) ≤ (196481195769333 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (117783393525623061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 10363052067393 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 10363052067393 : ℝ) = (10363052067393 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 41452208269571 : ℝ) ≤ (178994819292283 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (117783393525623061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (10363052067393 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41452208269571 / 100000000000000 : ℝ)) ≤ (178994819292283 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_231 : ∀ t : ℝ, (10997027650713 / 64000000000000 : ℝ) < t → t ≤ (345431490187 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-103102442052647882722856451 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (345431490187 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_232
  have hV : (12636320026321939004991565330335099 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10997027650713 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_231 (Vfield_monotoneOn (show (10997027650713 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10997027650713 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_232 : (12671015631765736318120600715139811 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (345431490187 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (345431490187 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (41559083855819 / 100000000000000 : ℝ) ≤ Real.sqrt (345431490187 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (345431490187 / 2000000000000 : ℝ) ≤ (2077954192791 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2077954192791 / 5000000000000 : ℝ) = (5000000000000 / 2077954192791 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41559083855819 / 100000000000000 : ℝ) = (7500000000000 / 41559083855819 : ℝ) := by norm_num
  have hL1 : (15932220875571 / 100000000000000 : ℝ) ≤ Real.log (1 + (345431490187 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((345431490187 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-168365162067 / 97656250000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2077954192791 / 5000000000000 : ℝ) ≤ (393874087757057 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (117692223903783961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 2077954192791 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 2077954192791 : ℝ) = (2077954192791 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 41559083855819 : ℝ) ≤ (178544239049061 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (117692223903783961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2077954192791 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41559083855819 / 100000000000000 : ℝ)) ≤ (178544239049061 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_232 : ∀ t : ℝ, (345431490187 / 2000000000000 : ℝ) < t → t ≤ (5583683878263 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-10281055425697299345135817 / 5000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5583683878263 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_233
  have hV : (12671015631765736318120600715139811 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (345431490187 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_232 (Vfield_monotoneOn (show (345431490187 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (345431490187 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_233 : (6370098639991592737749875796861347 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (5583683878263 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5583683878263 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (20886007349163 / 50000000000000 : ℝ) ≤ Real.sqrt (5583683878263 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5583683878263 / 32000000000000 : ℝ) ≤ (41772014698327 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (41772014698327 / 100000000000000 : ℝ) = (100000000000000 / 41772014698327 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (20886007349163 / 50000000000000 : ℝ) = (1250000000000 / 6962002449721 : ℝ) := by norm_num
  have hL1 : (16083411400927 / 100000000000000 : ℝ) ≤ Real.log (1 + (5583683878263 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5583683878263 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-171415906954639 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (41772014698327 / 100000000000000 : ℝ) ≤ (989221059713 / 2500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (117510790290969661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 41772014698327 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 41772014698327 : ℝ) = (41772014698327 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 6962002449721 : ℝ) ≤ (177653194295089 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (117510790290969661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (41772014698327 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (20886007349163 / 50000000000000 : ℝ)) ≤ (177653194295089 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_233 : ∀ t : ℝ, (5583683878263 / 32000000000000 : ℝ) < t → t ≤ (2820231956767 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-51262387223025281599994959 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2820231956767 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_234
  have hV : (6370098639991592737749875796861347 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5583683878263 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_233 (Vfield_monotoneOn (show (5583683878263 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5583683878263 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_234 : (12809102170893018636807796549487249 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2820231956767 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2820231956767 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (41983865626921 / 100000000000000 : ℝ) ≤ Real.sqrt (2820231956767 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2820231956767 / 16000000000000 : ℝ) ≤ (20991932813461 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20991932813461 / 50000000000000 : ℝ) = (50000000000000 / 20991932813461 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41983865626921 / 100000000000000 : ℝ) = (7500000000000 / 41983865626921 : ℝ) := by norm_num
  have hL1 : (253662088837 / 1562500000000 : ℝ) ≤ Real.log (1 + (2820231956767 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2820231956767 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-85217796661201 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20991932813461 / 50000000000000 : ℝ) ≤ (99372708305513 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (117330549357284461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 20991932813461 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 20991932813461 : ℝ) = (20991932813461 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 41983865626921 : ℝ) ≤ (22096919937167 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (117330549357284461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20991932813461 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41983865626921 / 100000000000000 : ℝ)) ≤ (22096919937167 / 125000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_234 : ∀ t : ℝ, (2820231956767 / 16000000000000 : ℝ) < t → t ≤ (1139448789761 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-40897896647698833558574123 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1139448789761 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_235
  have hV : (12809102170893018636807796549487249 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2820231956767 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_234 (Vfield_monotoneOn (show (2820231956767 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2820231956767 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_235 : (12877733444609488552780715091778607 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1139448789761 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1139448789761 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (42194652907703 / 100000000000000 : ℝ) ≤ Real.sqrt (1139448789761 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1139448789761 / 6400000000000 : ℝ) ≤ (5274331613463 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5274331613463 / 12500000000000 : ℝ) = (12500000000000 / 5274331613463 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (42194652907703 / 100000000000000 : ℝ) = (7500000000000 / 42194652907703 : ℝ) := by norm_num
  have hL1 : (16385108417571 / 100000000000000 : ℝ) ≤ Real.log (1 + (1139448789761 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1139448789761 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6778591864723 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5274331613463 / 12500000000000 : ℝ) ≤ (399281489905623 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (117151483688927361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 5274331613463 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 5274331613463 : ℝ) = (5274331613463 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 42194652907703 : ℝ) ≤ (43977602854829 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (117151483688927361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5274331613463 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (42194652907703 / 100000000000000 : ℝ)) ≤ (43977602854829 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_235 : ∀ t : ℝ, (1139448789761 / 6400000000000 : ℝ) < t → t ≤ (1438505996019 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-8157610803405578184574451 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1438505996019 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_236
  have hV : (12877733444609488552780715091778607 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1139448789761 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_235 (Vfield_monotoneOn (show (1139448789761 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1139448789761 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_236 : (6473047091900501767565799283639329 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1438505996019 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1438505996019 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (21202196201241 / 50000000000000 : ℝ) ≤ Real.sqrt (1438505996019 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1438505996019 / 8000000000000 : ℝ) ≤ (42404392402483 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (42404392402483 / 100000000000000 : ℝ) = (100000000000000 / 42404392402483 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21202196201241 / 50000000000000 : ℝ) = (1250000000000 / 7067398733747 : ℝ) := by norm_num
  have hL1 : (8267808140953 / 50000000000000 : ℝ) ≤ Real.log (1 + (1438505996019 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1438505996019 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-42125833458839 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (42404392402483 / 100000000000000 : ℝ) ≤ (401060563858331 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (116973576293656561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 42404392402483 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 42404392402483 : ℝ) = (42404392402483 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 7067398733747 : ℝ) ≤ (87529018895627 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (116973576293656561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (42404392402483 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21202196201241 / 50000000000000 : ℝ)) ≤ (87529018895627 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_236 : ∀ t : ℝ, (1438505996019 / 8000000000000 : ℝ) < t → t ≤ (2933792027309 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-50718040518540460220098691 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2933792027309 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_237
  have hV : (6473047091900501767565799283639329 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1438505996019 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_236 (Vfield_monotoneOn (show (1438505996019 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1438505996019 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_237 : (1635252013794054879970117577365881 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (2933792027309 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2933792027309 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (5352598692849 / 12500000000000 : ℝ) ≤ Real.sqrt (2933792027309 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2933792027309 / 16000000000000 : ℝ) ≤ (42820789542793 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (42820789542793 / 100000000000000 : ℝ) = (100000000000000 / 42820789542793 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5352598692849 / 12500000000000 : ℝ) = (312500000000 / 1784199564283 : ℝ) := by norm_num
  have hL1 : (2104494266503 / 12500000000000 : ℝ) ≤ Real.log (1 + (2933792027309 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2933792027309 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-166607703954573 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (42820789542793 / 100000000000000 : ℝ) ≤ (404584623036541 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (116621170375835561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 42820789542793 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 42820789542793 : ℝ) = (42820789542793 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (312500000000 / 1784199564283 : ℝ) ≤ (86694908410621 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (116621170375835561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (42820789542793 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5352598692849 / 12500000000000 : ℝ)) ≤ (86694908410621 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_237 : ∀ t : ℝ, (2933792027309 / 16000000000000 : ℝ) < t → t ≤ (149528603129 / 800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-100920634001617065928699099 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (149528603129 / 800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_238
  have hV : (1635252013794054879970117577365881 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2933792027309 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_237 (Vfield_monotoneOn (show (2933792027309 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2933792027309 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_238 : (13216891514816800083595430633733267 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (149528603129 / 800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (149528603129 / 800000000000 : ℝ) := by norm_num
  have hs1 : (43233176370843 / 100000000000000 : ℝ) ≤ Real.sqrt (149528603129 / 800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (149528603129 / 800000000000 : ℝ) ≤ (10808294092711 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (10808294092711 / 25000000000000 : ℝ) = (25000000000000 / 10808294092711 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (43233176370843 / 100000000000000 : ℝ) = (2500000000000 / 14411058790281 : ℝ) := by norm_num
  have hL1 : (17135392654247 / 100000000000000 : ℝ) ≤ Real.log (1 + (149528603129 / 800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((149528603129 / 800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-16474734071171 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (10808294092711 / 25000000000000 : ℝ) ≤ (102016072779189 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (116273203567814061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 10808294092711 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 10808294092711 : ℝ) = (10808294092711 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 14411058790281 : ℝ) ≤ (34353680073061 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (116273203567814061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (10808294092711 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (43233176370843 / 100000000000000 : ℝ)) ≤ (34353680073061 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_238 : ∀ t : ℝ, (149528603129 / 800000000000 : ℝ) < t → t ≤ (3047352097851 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-25105538860761735098803393 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3047352097851 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_239
  have hV : (13216891514816800083595430633733267 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (149528603129 / 800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_238 (Vfield_monotoneOn (show (149528603129 / 800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (149528603129 / 800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_239 : (3337685781829802191696978442077401 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (3047352097851 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3047352097851 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (10910416642929 / 25000000000000 : ℝ) ≤ Real.sqrt (3047352097851 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3047352097851 / 16000000000000 : ℝ) ≤ (43641666571717 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (43641666571717 / 100000000000000 : ℝ) = (100000000000000 / 43641666571717 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10910416642929 / 25000000000000 : ℝ) = (625000000000 / 3636805547643 : ℝ) := by norm_num
  have hL1 : (8716968609187 / 50000000000000 : ℝ) ≤ Real.log (1 + (3047352097851 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3047352097851 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-81460477912017 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (43641666571717 / 100000000000000 : ℝ) ≤ (205750394780467 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (115929553723396261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 43641666571717 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 43641666571717 : ℝ) = (43641666571717 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (625000000000 / 3636805547643 : ℝ) ≤ (10636977486997 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (115929553723396261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (43641666571717 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10910416642929 / 25000000000000 : ℝ)) ≤ (10636977486997 / 62500000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_239 : ∀ t : ℝ, (3047352097851 / 16000000000000 : ℝ) < t → t ≤ (1552066066561 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-19987852716704454767690833 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1552066066561 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_240
  have hV : (3337685781829802191696978442077401 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3047352097851 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_239 (Vfield_monotoneOn (show (3047352097851 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3047352097851 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
