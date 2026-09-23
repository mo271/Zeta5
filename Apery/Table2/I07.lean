import Apery.Table2.U07
import Apery.Table2.U08

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_280 : (2969838166659334395476620660975577 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (7424867802851 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7424867802851 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (9633838670833 / 20000000000000 : ℝ) ≤ Real.sqrt (7424867802851 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7424867802851 / 32000000000000 : ℝ) ≤ (24084596677083 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (24084596677083 / 50000000000000 : ℝ) = (50000000000000 / 24084596677083 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (9633838670833 / 20000000000000 : ℝ) = (1500000000000 / 9633838670833 : ℝ) := by norm_num
  have hL1 : (10433043845689 / 50000000000000 : ℝ) ≤ Real.log (1 + (7424867802851 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7424867802851 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-143694735938529 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (24084596677083 / 50000000000000 : ℝ) ≤ (219186609269 / 488281250000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112190215101198461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 24084596677083 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 24084596677083 : ℝ) = (24084596677083 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 9633838670833 : ℝ) ≤ (154460951760891 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112190215101198461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (24084596677083 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (9633838670833 / 20000000000000 : ℝ)) ≤ (154460951760891 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_280 : ∀ t : ℝ, (7424867802851 / 32000000000000 : ℝ) < t → t ≤ (3729493959969 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-183912999735040664982041287 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3729493959969 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_281
  have hV : (2969838166659334395476620660975577 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7424867802851 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_280 (Vfield_monotoneOn (show (7424867802851 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7424867802851 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_281 : (7443042668530936023711377010558247 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (3729493959969 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3729493959969 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (24139872229263 / 50000000000000 : ℝ) ≤ Real.sqrt (3729493959969 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3729493959969 / 16000000000000 : ℝ) ≤ (48279744458527 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (48279744458527 / 100000000000000 : ℝ) = (100000000000000 / 48279744458527 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (24139872229263 / 50000000000000 : ℝ) = (1250000000000 / 8046624076421 : ℝ) := by norm_num
  have hL1 : (4190518984257 / 20000000000000 : ℝ) ≤ Real.log (1 + (3729493959969 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3729493959969 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-35811769470721 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (48279744458527 / 100000000000000 : ℝ) ≤ (5622388731359 / 12500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112100522828617661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 48279744458527 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 48279744458527 : ℝ) = (48279744458527 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 8046624076421 : ℝ) ≤ (154112846497661 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112100522828617661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (48279744458527 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (24139872229263 / 50000000000000 : ℝ)) ≤ (154112846497661 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_281 : ∀ t : ℝ, (3729493959969 / 16000000000000 : ℝ) < t → t ≤ (299724321481 / 1280000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-183588228329707939810548413 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (299724321481 / 1280000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_282
  have hV : (7443042668530936023711377010558247 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3729493959969 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_281 (Vfield_monotoneOn (show (3729493959969 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3729493959969 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_282 : (7461454317390164298305559164108043 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (299724321481 / 1280000000000 : ℝ) := by
  have hp : (0 : ℝ) < (299724321481 / 1280000000000 : ℝ) := by norm_num
  have hs1 : (24195021500147 / 50000000000000 : ℝ) ≤ Real.sqrt (299724321481 / 1280000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (299724321481 / 1280000000000 : ℝ) ≤ (9678008600059 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (9678008600059 / 20000000000000 : ℝ) = (20000000000000 / 9678008600059 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (24195021500147 / 50000000000000 : ℝ) = (3750000000000 / 24195021500147 : ℝ) := by norm_num
  have hL1 : (21039027380861 / 100000000000000 : ℝ) ≤ Real.log (1 + (299724321481 / 1280000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((299724321481 / 1280000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-17850176859613 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (9678008600059 / 20000000000000 : ℝ) ≤ (90137039736537 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112011112811221161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 9678008600059 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 9678008600059 : ℝ) = (9678008600059 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 24195021500147 : ℝ) ≤ (75081584153 / 488281250000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112011112811221161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (9678008600059 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (24195021500147 / 50000000000000 : ℝ)) ≤ (75081584153 / 488281250000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_282 : ∀ t : ℝ, (299724321481 / 1280000000000 : ℝ) < t → t ≤ (29403234977 / 125000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-18326677950261876661299623 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (29403234977 / 125000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_283
  have hV : (7461454317390164298305559164108043 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (299724321481 / 1280000000000 : ℝ) := by norm_num
    refine le_trans V_pt_282 (Vfield_monotoneOn (show (299724321481 / 1280000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (299724321481 / 1280000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_283 : (2991932223824580435032855184674111 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (29403234977 / 125000000000 : ℝ) := by
  have hp : (0 : ℝ) < (29403234977 / 125000000000 : ℝ) := by norm_num
  have hs1 : (9700018140519 / 20000000000000 : ℝ) ≤ Real.sqrt (29403234977 / 125000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (29403234977 / 125000000000 : ℝ) ≤ (12125022675649 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (12125022675649 / 25000000000000 : ℝ) = (25000000000000 / 12125022675649 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (9700018140519 / 20000000000000 : ℝ) = (500000000000 / 3233339380173 : ℝ) := by norm_num
  have hL1 : (10562692599623 / 50000000000000 : ℝ) ≤ Real.log (1 + (29403234977 / 125000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((29403234977 / 125000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-142357729217031 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (12125022675649 / 25000000000000 : ℝ) ≤ (11289412378393 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (111921983165917661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 12125022675649 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 12125022675649 : ℝ) = (12125022675649 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (500000000000 / 3233339380173 : ℝ) ≤ (153423639134079 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (111921983165917661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (12125022675649 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (9700018140519 / 20000000000000 : ℝ)) ≤ (153423639134079 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_283 : ∀ t : ℝ, (29403234977 / 125000000000 : ℝ) < t → t ≤ (7561348271199 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-182948545136055035667982847 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7561348271199 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_284
  have hV : (2991932223824580435032855184674111 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (29403234977 / 125000000000 : ℝ) := by norm_num
    refine le_trans V_pt_283 (Vfield_monotoneOn (show (29403234977 / 125000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (29403234977 / 125000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_284 : (14996343179197938328901045837506757 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (7561348271199 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7561348271199 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (48609889269053 / 100000000000000 : ℝ) ≤ Real.sqrt (7561348271199 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7561348271199 / 32000000000000 : ℝ) ≤ (24304944634527 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (24304944634527 / 50000000000000 : ℝ) = (50000000000000 / 24304944634527 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (48609889269053 / 100000000000000 : ℝ) = (7500000000000 / 48609889269053 : ℝ) := by norm_num
  have hL1 : (4242333701049 / 20000000000000 : ℝ) ≤ Real.log (1 + (7561348271199 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7561348271199 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-141916003434313 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (24304944634527 / 50000000000000 : ℝ) ≤ (226232503246089 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (111833132030271861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 24304944634527 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 24304944634527 : ℝ) = (24304944634527 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 48609889269053 : ℝ) ≤ (153082485101399 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (111833132030271861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (24304944634527 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (48609889269053 / 100000000000000 : ℝ)) ≤ (153082485101399 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_284 : ∀ t : ℝ, (7561348271199 / 32000000000000 : ℝ) < t → t ≤ (3797734194143 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-91316712094642956676891583 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3797734194143 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_285
  have hV : (14996343179197938328901045837506757 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7561348271199 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_284 (Vfield_monotoneOn (show (7561348271199 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7561348271199 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_285 : (7516477600297217675327059722679143 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (3797734194143 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3797734194143 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (24359720192047 / 50000000000000 : ℝ) ≤ Real.sqrt (3797734194143 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3797734194143 / 16000000000000 : ℝ) ≤ (9743888076819 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (9743888076819 / 20000000000000 : ℝ) = (20000000000000 / 9743888076819 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (24359720192047 / 50000000000000 : ℝ) = (3750000000000 / 24359720192047 : ℝ) := by norm_num
  have hL1 : (5324469356833 / 25000000000000 : ℝ) ≤ Real.log (1 + (3797734194143 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3797734194143 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-5659048811611 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (9743888076819 / 20000000000000 : ℝ) ≤ (453350751173027 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (111744557562186961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 9743888076819 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 9743888076819 : ℝ) = (9743888076819 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 24359720192047 : ℝ) ≤ (76371798442061 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (111744557562186961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (9743888076819 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (24359720192047 / 50000000000000 : ℝ)) ≤ (76371798442061 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_285 : ∀ t : ℝ, (3797734194143 / 16000000000000 : ℝ) < t → t ≤ (383185431123 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-36402429944000541702274727 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (383185431123 / 1600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_286
  have hV : (7516477600297217675327059722679143 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3797734194143 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_285 (Vfield_monotoneOn (show (3797734194143 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3797734194143 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_286 : (15105970652372174430878984971502667 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (383185431123 / 1600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (383185431123 / 1600000000000 : ℝ) := by norm_num
  have hs1 : (48937806903443 / 100000000000000 : ℝ) ≤ Real.sqrt (383185431123 / 1600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (383185431123 / 1600000000000 : ℝ) ≤ (12234451725861 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (12234451725861 / 25000000000000 : ℝ) = (25000000000000 / 12234451725861 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (48937806903443 / 100000000000000 : ℝ) = (7500000000000 / 48937806903443 : ℝ) := by norm_num
  have hL1 : (21470072631999 / 100000000000000 : ℝ) ≤ Real.log (1 + (383185431123 / 1600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((383185431123 / 1600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-35150603523149 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (12234451725861 / 25000000000000 : ℝ) ≤ (113778503298397 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (111568231360130861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 12234451725861 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 12234451725861 : ℝ) = (12234451725861 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 48937806903443 : ℝ) ≤ (152072518392149 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (111568231360130861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (12234451725861 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (48937806903443 / 100000000000000 : ℝ)) ≤ (152072518392149 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_286 : ∀ t : ℝ, (383185431123 / 1600000000000 : ℝ) < t → t ≤ (3865974428317 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-181402265131217835769418963 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3865974428317 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_287
  have hV : (15105970652372174430878984971502667 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (383185431123 / 1600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_286 (Vfield_monotoneOn (show (383185431123 / 1600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (383185431123 / 1600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_287 : (15178710490429165037526217054926521 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3865974428317 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3865974428317 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (49155203363409 / 100000000000000 : ℝ) ≤ Real.sqrt (3865974428317 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3865974428317 / 16000000000000 : ℝ) ≤ (4915520336341 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4915520336341 / 10000000000000 : ℝ) = (10000000000000 / 4915520336341 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (49155203363409 / 100000000000000 : ℝ) = (2500000000000 / 16385067787803 : ℝ) := by norm_num
  have hL1 : (2164197183441 / 10000000000000 : ℝ) ≤ Real.log (1 + (3865974428317 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3865974428317 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-69868088587269 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4915520336341 / 10000000000000 : ℝ) ≤ (228433212307557 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (111392990217978261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 4915520336341 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 4915520336341 : ℝ) = (4915520336341 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 16385067787803 : ℝ) ≤ (75705104221061 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (111392990217978261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4915520336341 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (49155203363409 / 100000000000000 : ℝ)) ≤ (75705104221061 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_287 : ∀ t : ℝ, (3865974428317 / 16000000000000 : ℝ) < t → t ≤ (975023636351 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-180803156453039324490040369 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (975023636351 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_288
  have hV : (15178710490429165037526217054926521 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3865974428317 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_287 (Vfield_monotoneOn (show (3865974428317 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3865974428317 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_288 : (381279441929072235460944112512433 / 125000000000000000000000000000000 : ℝ) ≤ Vfield (975023636351 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (975023636351 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (1234291064457 / 2500000000000 : ℝ) ≤ Real.sqrt (975023636351 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (975023636351 / 4000000000000 : ℝ) ≤ (49371642578281 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (49371642578281 / 100000000000000 : ℝ) = (100000000000000 / 49371642578281 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1234291064457 / 2500000000000 : ℝ) = (62500000000 / 411430354819 : ℝ) := by norm_num
  have hL1 : (2181357605047 / 10000000000000 : ℝ) ≤ Real.log (1 + (975023636351 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((975023636351 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-34719344881223 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (49371642578281 / 100000000000000 : ℝ) ≤ (11465203144889 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (111218820099933661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 49371642578281 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 49371642578281 : ℝ) = (49371642578281 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (62500000000 / 411430354819 : ℝ) ≤ (150756477718981 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (111218820099933661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (49371642578281 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1234291064457 / 2500000000000 : ℝ)) ≤ (150756477718981 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_288 : ∀ t : ℝ, (975023636351 / 4000000000000 : ℝ) < t → t ≤ (3934214662491 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-180214274115948519129188793 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3934214662491 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_289
  have hV : (381279441929072235460944112512433 / 125000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (975023636351 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_288 (Vfield_monotoneOn (show (975023636351 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (975023636351 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_289 : (15323375123287753237689687412438227 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3934214662491 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3934214662491 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (49587137082683 / 100000000000000 : ℝ) ≤ Real.sqrt (3934214662491 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3934214662491 / 16000000000000 : ℝ) ≤ (12396784270671 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (12396784270671 / 25000000000000 : ℝ) = (25000000000000 / 12396784270671 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (49587137082683 / 100000000000000 : ℝ) = (7500000000000 / 49587137082683 : ℝ) := by norm_num
  have hL1 : (21984886290863 / 100000000000000 : ℝ) ≤ Real.log (1 + (3934214662491 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3934214662491 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-69012947239791 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (12396784270671 / 25000000000000 : ℝ) ≤ (92067850824987 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (111045707266996161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 12396784270671 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 12396784270671 : ℝ) = (12396784270671 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 49587137082683 : ℝ) ≤ (146592912677 / 976562500000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (111045707266996161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (12396784270671 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (49587137082683 / 100000000000000 : ℝ)) ≤ (146592912677 / 976562500000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_289 : ∀ t : ℝ, (3934214662491 / 16000000000000 : ℝ) < t → t ≤ (1984167389789 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-22454390370207443440328291 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1984167389789 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_290
  have hV : (15323375123287753237689687412438227 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3934214662491 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_289 (Vfield_monotoneOn (show (3934214662491 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3934214662491 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_290 : (15395305686760530430398263914334219 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1984167389789 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1984167389789 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (49801699140051 / 100000000000000 : ℝ) ≤ Real.sqrt (1984167389789 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1984167389789 / 8000000000000 : ℝ) ≤ (12450424785013 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (12450424785013 / 25000000000000 : ℝ) = (25000000000000 / 12450424785013 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (49801699140051 / 100000000000000 : ℝ) = (2500000000000 / 16600566380017 : ℝ) := by norm_num
  have hL1 : (22155903561087 / 100000000000000 : ℝ) ≤ Real.log (1 + (1984167389789 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1984167389789 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-68590799252761 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (12450424785013 / 25000000000000 : ℝ) ≤ (924119888227 / 2000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (110873638268139661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 12450424785013 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 12450424785013 : ℝ) = (12450424785013 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 16600566380017 : ℝ) ≤ (149474024844271 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (110873638268139661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (12450424785013 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (49801699140051 / 100000000000000 : ℝ)) ≤ (149474024844271 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_290 : ∀ t : ℝ, (1984167389789 / 8000000000000 : ℝ) < t → t ≤ (504571876719 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-178504259156482432289081781 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (504571876719 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_291
  have hV : (15395305686760530430398263914334219 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1984167389789 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_290 (Vfield_monotoneOn (show (1984167389789 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1984167389789 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_291 : (7769188678168039274594837574427307 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (504571876719 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (504571876719 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (25114036830003 / 50000000000000 : ℝ) ≤ Real.sqrt (504571876719 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (504571876719 / 2000000000000 : ℝ) ≤ (50228073660007 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (50228073660007 / 100000000000000 : ℝ) = (100000000000000 / 50228073660007 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (25114036830003 / 50000000000000 : ℝ) = (1250000000000 / 8371345610001 : ℝ) := by norm_num
  have hL1 : (1406066449207 / 6250000000000 : ℝ) ≤ Real.log (1 + (504571876719 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((504571876719 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-135514095329289 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (50228073660007 / 211905582450542 : ℝ) ≤ (116367633303951 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (50228073660007 / 100000000000000 : ℝ) ≤ (116367633303951 / 250000000000000 : ℝ) := by
    have hw : (55952791225271 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (50228073660007 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (50228073660007 / 100000000000000 : ℝ) / (1 + (55952791225271 / 50000000000000 : ℝ)) = (50228073660007 / 211905582450542 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (110532579357909261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 50228073660007 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 50228073660007 : ℝ) = (50228073660007 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 8371345610001 : ℝ) ≤ (74111877443601 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (110532579357909261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (50228073660007 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (25114036830003 / 50000000000000 : ℝ)) ≤ (74111877443601 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_291 : ∀ t : ℝ, (504571876719 / 2000000000000 : ℝ) < t → t ≤ (2052407623963 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2771990985438190526473797 / 1562500000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2052407623963 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_292
  have hV : (7769188678168039274594837574427307 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (504571876719 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_291 (Vfield_monotoneOn (show (504571876719 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (504571876719 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_292 : (313608291703812425117034566855199 / 100000000000000000000000000000000 : ℝ) ≤ Vfield (2052407623963 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2052407623963 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (1013017182471 / 2000000000000 : ℝ) ≤ Real.sqrt (2052407623963 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2052407623963 / 8000000000000 : ℝ) ≤ (50650859123551 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (50650859123551 / 100000000000000 : ℝ) = (100000000000000 / 50650859123551 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1013017182471 / 2000000000000 : ℝ) = (50000000000 / 337672394157 : ℝ) := by norm_num
  have hL1 : (22837062870767 / 100000000000000 : ℝ) ≤ Real.log (1 + (2052407623963 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2052407623963 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-66936971189469 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (50650859123551 / 212095983558528 : ℝ) ≤ (14651278585529 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (50650859123551 / 100000000000000 : ℝ) ≤ (14651278585529 / 31250000000000 : ℝ) := by
    have hw : (875749871551 / 781250000000 : ℝ) ≤ Real.sqrt (1 + (50650859123551 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (50650859123551 / 100000000000000 : ℝ) / (1 + (875749871551 / 781250000000 : ℝ)) = (50650859123551 / 212095983558528 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (110195541205796861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 50650859123551 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 50650859123551 : ℝ) = (50650859123551 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (50000000000 / 337672394157 : ℝ) ≤ (73502171942273 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (110195541205796861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (50650859123551 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1013017182471 / 2000000000000 : ℝ)) ≤ (73502171942273 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_292 : ∀ t : ℝ, (2052407623963 / 8000000000000 : ℝ) < t → t ≤ (41730554821 / 160000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-88170980790712923376884091 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (41730554821 / 160000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_293
  have hV : (313608291703812425117034566855199 / 100000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2052407623963 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_292 (Vfield_monotoneOn (show (2052407623963 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2052407623963 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_293 : (15821438530885961284513977255939529 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (41730554821 / 160000000000 : ℝ) := by
  have hp : (0 : ℝ) < (41730554821 / 160000000000 : ℝ) := by norm_num
  have hs1 : (51070144667041 / 100000000000000 : ℝ) ≤ Real.sqrt (41730554821 / 160000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (41730554821 / 160000000000 : ℝ) ≤ (25535072333521 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (25535072333521 / 50000000000000 : ℝ) = (50000000000000 / 25535072333521 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (51070144667041 / 100000000000000 : ℝ) = (7500000000000 / 51070144667041 : ℝ) := by norm_num
  have hL1 : (11587955236171 / 50000000000000 : ℝ) ≤ Real.log (1 + (41730554821 / 160000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((41730554821 / 160000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-33065064230493 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (51070144667042 / 212286061807833 : ℝ) ≤ (118043017335869 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (25535072333521 / 50000000000000 : ℝ) ≤ (118043017335869 / 250000000000000 : ℝ) := by
    have hw : (112286061807833 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (25535072333521 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (25535072333521 / 50000000000000 : ℝ) / (1 + (112286061807833 / 100000000000000 : ℝ)) = (51070144667042 / 212286061807833 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (109862425745142061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 25535072333521 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 25535072333521 : ℝ) = (25535072333521 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 51070144667041 : ℝ) ≤ (9113408930943 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (109862425745142061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (25535072333521 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (51070144667041 / 100000000000000 : ℝ)) ≤ (9113408930943 / 62500000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_293 : ∀ t : ℝ, (41730554821 / 160000000000 : ℝ) < t → t ≤ (269345996903 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-174296363471096566929460169 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (269345996903 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_294
  have hV : (15821438530885961284513977255939529 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (41730554821 / 160000000000 : ℝ) := by norm_num
    refine le_trans V_pt_293 (Vfield_monotoneOn (show (41730554821 / 160000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (41730554821 / 160000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_294 : (3220105540229125173445234427266009 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (269345996903 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (269345996903 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (10379710918961 / 20000000000000 : ℝ) ≤ Real.sqrt (269345996903 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (269345996903 / 1000000000000 : ℝ) ≤ (25949277297403 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (25949277297403 / 50000000000000 : ℝ) = (50000000000000 / 25949277297403 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10379710918961 / 20000000000000 : ℝ) = (1500000000000 / 10379710918961 : ℝ) := by norm_num
  have hL1 : (23850180476297 / 100000000000000 : ℝ) ≤ Real.log (1 + (269345996903 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((269345996903 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-25821793043297 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (51898554594806 / 212665256263987 : ℝ) ≤ (239360214616769 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (25949277297403 / 50000000000000 : ℝ) ≤ (239360214616769 / 500000000000000 : ℝ) := by
    have hw : (112665256263987 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (25949277297403 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (25949277297403 / 50000000000000 : ℝ) / (1 + (112665256263987 / 100000000000000 : ℝ)) = (51898554594806 / 212665256263987 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (109207589756135861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 25949277297403 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 25949277297403 : ℝ) = (25949277297403 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 10379710918961 : ℝ) ≤ (143519118491667 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (109207589756135861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (25949277297403 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10379710918961 / 20000000000000 : ℝ)) ≤ (143519118491667 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_294 : ∀ t : ℝ, (269345996903 / 1000000000000 : ℝ) < t → t ≤ (8696815458149 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-21507203699118222510173283 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (8696815458149 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_295
  have hV : (3220105540229125173445234427266009 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (269345996903 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_294 (Vfield_monotoneOn (show (269345996903 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (269345996903 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_295 : (16179311875325374613151301895918923 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (8696815458149 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (8696815458149 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (52132090219667 / 100000000000000 : ℝ) ≤ Real.sqrt (8696815458149 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (8696815458149 / 32000000000000 : ℝ) ≤ (13033022554917 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13033022554917 / 25000000000000 : ℝ) = (25000000000000 / 13033022554917 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (52132090219667 / 100000000000000 : ℝ) = (7500000000000 / 52132090219667 : ℝ) := by norm_num
  have hL1 : (4808278846321 / 20000000000000 : ℝ) ≤ Real.log (1 + (8696815458149 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((8696815458149 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-25645860583459 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (17377363406556 / 70924341168647 : ℝ) ≤ (240279241373003 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13033022554917 / 25000000000000 : ℝ) ≤ (240279241373003 / 500000000000000 : ℝ) := by
    have hw : (112773023505941 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (13033022554917 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (13033022554917 / 25000000000000 : ℝ) / (1 + (112773023505941 / 100000000000000 : ℝ)) = (17377363406556 / 70924341168647 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (109023784404889061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 13033022554917 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 13033022554917 : ℝ) = (13033022554917 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 52132090219667 : ℝ) ≤ (71442465712027 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (109023784404889061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13033022554917 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (52132090219667 / 100000000000000 : ℝ)) ≤ (71442465712027 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_295 : ∀ t : ℝ, (8696815458149 / 32000000000000 : ℝ) < t → t ≤ (4387279507701 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-85405865978970995023417201 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4387279507701 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_296
  have hV : (16179311875325374613151301895918923 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (8696815458149 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_295 (Vfield_monotoneOn (show (8696815458149 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (8696815458149 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_296 : (16257789977722063506720455777919813 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (4387279507701 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4387279507701 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (52364584332477 / 100000000000000 : ℝ) ≤ Real.sqrt (4387279507701 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4387279507701 / 16000000000000 : ℝ) ≤ (26182292166239 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (26182292166239 / 50000000000000 : ℝ) = (50000000000000 / 26182292166239 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (52364584332477 / 100000000000000 : ℝ) = (2500000000000 / 17454861444159 : ℝ) := by norm_num
  have hL1 : (4846448611519 / 20000000000000 : ℝ) ≤ Real.log (1 + (4387279507701 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4387279507701 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-127357311249093 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (52364584332478 / 212880687862509 : ℝ) ≤ (30149052919551 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (26182292166239 / 50000000000000 : ℝ) ≤ (30149052919551 / 62500000000000 : ℝ) := by
    have hw : (112880687862509 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (26182292166239 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (26182292166239 / 50000000000000 : ℝ) / (1 + (112880687862509 / 100000000000000 : ℝ)) = (52364584332478 / 212880687862509 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (108841148008208061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 26182292166239 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 26182292166239 : ℝ) = (26182292166239 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 17454861444159 : ℝ) ≤ (71129539071711 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (108841148008208061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (26182292166239 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (52364584332477 / 100000000000000 : ℝ)) ≤ (71129539071711 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_296 : ∀ t : ℝ, (4387279507701 / 16000000000000 : ℝ) < t → t ≤ (1770460514531 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-42434129162702378348755059 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1770460514531 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_297
  have hV : (16257789977722063506720455777919813 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4387279507701 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_296 (Vfield_monotoneOn (show (4387279507701 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4387279507701 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_297 : (1020997836962037101469790521029257 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (1770460514531 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1770460514531 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (3287253171553 / 6250000000000 : ℝ) ≤ Real.sqrt (1770460514531 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1770460514531 / 6400000000000 : ℝ) ≤ (52596050744849 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (52596050744849 / 100000000000000 : ℝ) = (100000000000000 / 52596050744849 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3287253171553 / 6250000000000 : ℝ) = (468750000000 / 3287253171553 : ℝ) := by norm_num
  have hL1 : (24422728344541 / 100000000000000 : ℝ) ≤ Real.log (1 + (1770460514531 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1770460514531 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-126492857592107 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (52596050744849 / 212988249627803 : ℝ) ≤ (121049918489733 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (52596050744849 / 100000000000000 : ℝ) ≤ (121049918489733 / 250000000000000 : ℝ) := by
    have hw : (112988249627803 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (52596050744849 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (52596050744849 / 100000000000000 : ℝ) / (1 + (112988249627803 / 100000000000000 : ℝ)) = (52596050744849 / 212988249627803 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (108659665283596461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 52596050744849 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 52596050744849 : ℝ) = (52596050744849 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (468750000000 / 3287253171553 : ℝ) ≤ (7082068885267 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (108659665283596461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (52596050744849 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3287253171553 / 6250000000000 : ℝ)) ≤ (7082068885267 / 50000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_297 : ∀ t : ℝ, (1770460514531 / 6400000000000 : ℝ) < t → t ≤ (17782348702563 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-33847179728468718267844027 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (17782348702563 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_298
  have hV : (1020997836962037101469790521029257 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1770460514531 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_297 (Vfield_monotoneOn (show (1770460514531 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1770460514531 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_298 : (3274988126059582574358939899787469 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (17782348702563 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (17782348702563 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (10542280559301 / 20000000000000 : ℝ) ≤ Real.sqrt (17782348702563 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (17782348702563 / 64000000000000 : ℝ) ≤ (26355701398253 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (26355701398253 / 50000000000000 : ℝ) = (50000000000000 / 26355701398253 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10542280559301 / 20000000000000 : ℝ) = (500000000000 / 3514093519767 : ℝ) := by norm_num
  have hL1 : (24517835093163 / 100000000000000 : ℝ) ≤ Real.log (1 + (17782348702563 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((17782348702563 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-126063417009737 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (52711402796506 / 213041992130249 : ℝ) ≤ (121275702045259 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (26355701398253 / 50000000000000 : ℝ) ≤ (121275702045259 / 250000000000000 : ℝ) := by
    have hw : (113041992130249 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (26355701398253 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (26355701398253 / 50000000000000 : ℝ) / (1 + (113041992130249 / 100000000000000 : ℝ)) = (52711402796506 / 213041992130249 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (108569351861386061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 26355701398253 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 26355701398253 : ℝ) = (26355701398253 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 3514093519767 : ℝ) ≤ (141335529753977 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (108569351861386061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (26355701398253 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10542280559301 / 20000000000000 : ℝ)) ≤ (141335529753977 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_298 : ∀ t : ℝ, (17782348702563 / 64000000000000 : ℝ) < t → t ≤ (2232511532477 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-6750138339528976194077729 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2232511532477 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_299
  have hV : (3274988126059582574358939899787469 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (17782348702563 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_298 (Vfield_monotoneOn (show (17782348702563 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (17782348702563 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_299 : (3282768287575914558230944905125809 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (2232511532477 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2232511532477 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (10565300593161 / 20000000000000 : ℝ) ≤ Real.sqrt (2232511532477 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2232511532477 / 8000000000000 : ℝ) ≤ (26413251482903 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (26413251482903 / 50000000000000 : ℝ) = (50000000000000 / 26413251482903 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10565300593161 / 20000000000000 : ℝ) = (500000000000 / 3521766864387 : ℝ) := by norm_num
  have hL1 : (24612851474787 / 100000000000000 : ℝ) ≤ Real.log (1 + (2232511532477 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2232511532477 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-62817906368229 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (52826502965806 / 213095709094537 : ℝ) ≤ (7593798657339 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (26413251482903 / 50000000000000 : ℝ) ≤ (7593798657339 / 15625000000000 : ℝ) := by
    have hw : (113095709094537 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (26413251482903 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (26413251482903 / 50000000000000 : ℝ) / (1 + (113095709094537 / 100000000000000 : ℝ)) = (52826502965806 / 213095709094537 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (108479321272520061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 26413251482903 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 26413251482903 : ℝ) = (26413251482903 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 3521766864387 : ℝ) ≤ (28206330923679 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (108479321272520061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (26413251482903 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10565300593161 / 20000000000000 : ℝ)) ≤ (28206330923679 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_299 : ∀ t : ℝ, (2232511532477 / 8000000000000 : ℝ) < t → t ≤ (17937835817069 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-42071550893381604626061657 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (17937835817069 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_300
  have hV : (3282768287575914558230944905125809 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2232511532477 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_299 (Vfield_monotoneOn (show (2232511532477 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2232511532477 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_300 : (3290533643994347788160380731929049 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (17937835817069 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (17937835817069 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (10588270579121 / 20000000000000 : ℝ) ≤ Real.sqrt (17937835817069 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (17937835817069 / 64000000000000 : ℝ) ≤ (26470676447803 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (26470676447803 / 50000000000000 : ℝ) = (50000000000000 / 26470676447803 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10588270579121 / 20000000000000 : ℝ) = (1500000000000 / 10588270579121 : ℝ) := by norm_num
  have hL1 : (24707777660977 / 100000000000000 : ℝ) ≤ Real.log (1 + (17937835817069 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((17937835817069 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-62605014567409 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (26470676447803 / 106574700278519 : ℝ) ≤ (243450304916351 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (26470676447803 / 50000000000000 : ℝ) ≤ (243450304916351 / 500000000000000 : ℝ) := by
    have hw : (56574700278519 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (26470676447803 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (26470676447803 / 50000000000000 : ℝ) / (1 + (56574700278519 / 50000000000000 : ℝ)) = (26470676447803 / 106574700278519 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (108389571696219461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 26470676447803 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 26470676447803 : ℝ) = (26470676447803 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 10588270579121 : ℝ) ≤ (140729731179839 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (108389571696219461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (26470676447803 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10588270579121 / 20000000000000 : ℝ)) ≤ (140729731179839 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_300 : ∀ t : ℝ, (17937835817069 / 64000000000000 : ℝ) < t → t ≤ (9007789687161 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-33566389198908860819532481 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9007789687161 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_301
  have hV : (3290533643994347788160380731929049 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (17937835817069 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_300 (Vfield_monotoneOn (show (17937835817069 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (17937835817069 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_301 : (16491421378754489374167744181529389 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9007789687161 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9007789687161 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (53055954210981 / 100000000000000 : ℝ) ≤ Real.sqrt (9007789687161 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9007789687161 / 32000000000000 : ℝ) ≤ (26527977105491 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (26527977105491 / 50000000000000 : ℝ) = (50000000000000 / 26527977105491 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (53055954210981 / 100000000000000 : ℝ) = (2500000000000 / 17685318070327 : ℝ) := by norm_num
  have hL1 : (24802613822809 / 100000000000000 : ℝ) ≤ Real.log (1 + (9007789687161 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9007789687161 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-124786050766261 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (53055954210982 / 213203066554037 : ℝ) ≤ (243897656743613 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (26527977105491 / 50000000000000 : ℝ) ≤ (243897656743613 / 500000000000000 : ℝ) := by
    have hw : (113203066554037 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (26527977105491 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (26527977105491 / 50000000000000 : ℝ) / (1 + (113203066554037 / 100000000000000 : ℝ)) = (53055954210982 / 213203066554037 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (108300101330767061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 26527977105491 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 26527977105491 : ℝ) = (26527977105491 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 17685318070327 : ℝ) ≤ (70214869317357 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (108300101330767061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (26527977105491 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (53055954210981 / 100000000000000 : ℝ)) ≤ (70214869317357 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_301 : ∀ t : ℝ, (9007789687161 / 32000000000000 : ℝ) < t → t ≤ (723732917263 / 2560000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-83694513232574176619934441 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (723732917263 / 2560000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_302
  have hV : (16491421378754489374167744181529389 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9007789687161 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_301 (Vfield_monotoneOn (show (9007789687161 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9007789687161 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_302 : (16530101312799606180474621965238193 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (723732917263 / 2560000000000 : ℝ) := by
  have hp : (0 : ℝ) < (723732917263 / 2560000000000 : ℝ) := by norm_num
  have hs1 : (53170308519497 / 100000000000000 : ℝ) ≤ Real.sqrt (723732917263 / 2560000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (723732917263 / 2560000000000 : ℝ) ≤ (26585154259749 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (26585154259749 / 50000000000000 : ℝ) = (50000000000000 / 26585154259749 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (53170308519497 / 100000000000000 : ℝ) = (7500000000000 / 53170308519497 : ℝ) := by norm_num
  have hL1 : (3112170016359 / 12500000000000 : ℝ) ≤ Real.log (1 + (723732917263 / 2560000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((723732917263 / 2560000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-124363862387773 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (53170308519498 / 213256707121735 : ℝ) ≤ (122171810715659 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (26585154259749 / 50000000000000 : ℝ) ≤ (122171810715659 / 250000000000000 : ℝ) := by
    have hw : (22651341424347 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (26585154259749 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (26585154259749 / 50000000000000 : ℝ) / (1 + (22651341424347 / 20000000000000 : ℝ)) = (53170308519498 / 213256707121735 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (108210908393226061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 26585154259749 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 26585154259749 : ℝ) = (26585154259749 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 53170308519497 : ℝ) ≤ (17516457061071 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (108210908393226061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (26585154259749 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (53170308519497 / 100000000000000 : ℝ)) ≤ (17516457061071 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_302 : ∀ t : ℝ, (723732917263 / 2560000000000 : ℝ) < t → t ≤ (4542766622207 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-6678245974807611595309121 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4542766622207 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_303
  have hV : (16530101312799606180474621965238193 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (723732917263 / 2560000000000 : ℝ) := by norm_num
    refine le_trans V_pt_302 (Vfield_monotoneOn (show (723732917263 / 2560000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (723732917263 / 2560000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_303 : (8284354208557444193757232809513677 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (4542766622207 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4542766622207 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (26642208705733 / 50000000000000 : ℝ) ≤ Real.sqrt (4542766622207 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4542766622207 / 16000000000000 : ℝ) ≤ (53284417411467 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (53284417411467 / 100000000000000 : ℝ) = (100000000000000 / 53284417411467 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (26642208705733 / 50000000000000 : ℝ) = (3750000000000 / 26642208705733 : ℝ) := by norm_num
  have hL1 : (3124002094409 / 12500000000000 : ℝ) ≤ Real.log (1 + (4542766622207 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4542766622207 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-123943448948593 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (4844037946497 / 19391847481477 : ℝ) ≤ (244788207801621 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (53284417411467 / 100000000000000 : ℝ) ≤ (244788207801621 / 500000000000000 : ℝ) := by
    have hw : (113310322296247 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (53284417411467 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (53284417411467 / 100000000000000 : ℝ) / (1 + (113310322296247 / 100000000000000 : ℝ)) = (4844037946497 / 19391847481477 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (108121991119165461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 53284417411467 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 53284417411467 : ℝ) = (53284417411467 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 26642208705733 : ℝ) ≤ (34958866137553 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (108121991119165461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (53284417411467 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (26642208705733 / 50000000000000 : ℝ)) ≤ (34958866137553 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_303 : ∀ t : ℝ, (4542766622207 / 16000000000000 : ℝ) < t → t ≤ (36419876534909 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-166743144894917460535578629 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (36419876534909 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_304
  have hV : (8284354208557444193757232809513677 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4542766622207 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_303 (Vfield_monotoneOn (show (4542766622207 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4542766622207 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_304 : (4146996195149927481965853061428929 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (36419876534909 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (36419876534909 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (13335345079641 / 25000000000000 : ℝ) ≤ Real.sqrt (36419876534909 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (36419876534909 / 128000000000000 : ℝ) ≤ (10668276063713 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (10668276063713 / 20000000000000 : ℝ) = (20000000000000 / 10668276063713 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13335345079641 / 25000000000000 : ℝ) = (625000000000 / 4445115026547 : ℝ) := by norm_num
  have hL1 : (25039311489123 / 100000000000000 : ℝ) ≤ Real.log (1 + (36419876534909 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((36419876534909 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24746780635931 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (10668276063713 / 42667424074464 : ℝ) ≤ (122504993424851 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (10668276063713 / 20000000000000 : ℝ) ≤ (122504993424851 / 250000000000000 : ℝ) := by
    have hw : (708357002327 / 625000000000 : ℝ) ≤ Real.sqrt (1 + (10668276063713 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (10668276063713 / 20000000000000 : ℝ) / (1 + (708357002327 / 625000000000 : ℝ)) = (10668276063713 / 42667424074464 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (108077635309549261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 10668276063713 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 10668276063713 : ℝ) = (10668276063713 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (625000000000 / 4445115026547 : ℝ) ≤ (69844035590359 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (108077635309549261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (10668276063713 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13335345079641 / 25000000000000 : ℝ)) ≤ (69844035590359 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_304 : ∀ t : ℝ, (36419876534909 / 128000000000000 : ℝ) < t → t ≤ (18248810046081 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-166532278717223165790144349 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (18248810046081 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_305
  have hV : (4146996195149927481965853061428929 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (36419876534909 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_304 (Vfield_monotoneOn (show (36419876534909 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (36419876534909 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_305 : (16607243083187596036868003058594183 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (18248810046081 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (18248810046081 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (53398282460207 / 100000000000000 : ℝ) ≤ Real.sqrt (18248810046081 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (18248810046081 / 64000000000000 : ℝ) ≤ (3337392653763 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3337392653763 / 6250000000000 : ℝ) = (6250000000000 / 3337392653763 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (53398282460207 / 100000000000000 : ℝ) = (7500000000000 / 53398282460207 : ℝ) := by norm_num
  have hL1 : (2508658386563 / 10000000000000 : ℝ) ≤ Real.log (1 + (18248810046081 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((18248810046081 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-12352479558699 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (3337392653763 / 13335244507100 : ℝ) ≤ (7663482018297 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3337392653763 / 6250000000000 : ℝ) ≤ (7663482018297 / 15625000000000 : ℝ) := by
    have hw : (70852445071 / 62500000000 : ℝ) ≤ Real.sqrt (1 + (3337392653763 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3337392653763 / 6250000000000 : ℝ) / (1 + (70852445071 / 62500000000 : ℝ)) = (3337392653763 / 13335244507100 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (108033347762388861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 3337392653763 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 3337392653763 : ℝ) = (3337392653763 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 53398282460207 : ℝ) ≤ (69770571462989 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (108033347762388861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3337392653763 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (53398282460207 / 100000000000000 : ℝ)) ≤ (69770571462989 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_305 : ∀ t : ℝ, (18248810046081 / 64000000000000 : ℝ) < t → t ≤ (7315072729883 / 25600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-33264690137158769659829233 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7315072729883 / 25600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_306
  have hV : (16607243083187596036868003058594183 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (18248810046081 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_305 (Vfield_monotoneOn (show (18248810046081 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (18248810046081 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_306 : (16626483373271759399483853138908743 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (7315072729883 / 25600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7315072729883 / 25600000000000 : ℝ) := by norm_num
  have hs1 : (53455124030447 / 100000000000000 : ℝ) ≤ Real.sqrt (7315072729883 / 25600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7315072729883 / 25600000000000 : ℝ) ≤ (3340945251903 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3340945251903 / 6250000000000 : ℝ) = (6250000000000 / 3340945251903 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (53455124030447 / 100000000000000 : ℝ) = (7500000000000 / 53455124030447 : ℝ) := by norm_num
  have hL1 : (25133833905919 / 100000000000000 : ℝ) ≤ Real.log (1 + (7315072729883 / 25600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7315072729883 / 25600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1233161243419 / 1000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (17818374676816 / 71130232508193 : ℝ) ≤ (61363130521593 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3340945251903 / 6250000000000 : ℝ) ≤ (61363130521593 / 125000000000000 : ℝ) := by
    have hw : (113390697524579 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (3340945251903 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3340945251903 / 6250000000000 : ℝ) / (1 + (113390697524579 / 100000000000000 : ℝ)) = (17818374676816 / 71130232508193 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107989128262215261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 3340945251903 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 3340945251903 : ℝ) = (3340945251903 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 53455124030447 : ℝ) ≤ (2787893546897 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107989128262215261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3340945251903 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (53455124030447 / 100000000000000 : ℝ)) ≤ (2787893546897 / 20000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_306 : ∀ t : ℝ, (7315072729883 / 25600000000000 : ℝ) < t → t ≤ (9163276801667 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-166116569554841651963678523 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9163276801667 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_307
  have hV : (16626483373271759399483853138908743 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7315072729883 / 25600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_306 (Vfield_monotoneOn (show (7315072729883 / 25600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7315072729883 / 25600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_307 : (520178303094705961281682468818493 / 156250000000000000000000000000000 : ℝ) ≤ Vfield (9163276801667 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9163276801667 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (1672247038197 / 3125000000000 : ℝ) ≤ Real.sqrt (9163276801667 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9163276801667 / 32000000000000 : ℝ) ≤ (10702381044461 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (10702381044461 / 20000000000000 : ℝ) = (20000000000000 / 10702381044461 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1672247038197 / 3125000000000 : ℝ) = (78125000000 / 557415679399 : ℝ) := by norm_num
  have hL1 : (25181061631089 / 100000000000000 : ℝ) ≤ Real.log (1 + (9163276801667 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9163276801667 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-61553943813557 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (10702381044461 / 42683495321948 : ℝ) ≤ (122836640212059 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (10702381044461 / 20000000000000 : ℝ) ≤ (122836640212059 / 250000000000000 : ℝ) := by
    have hw : (5670873830487 / 5000000000000 : ℝ) ≤ Real.sqrt (1 + (10702381044461 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (10702381044461 / 20000000000000 : ℝ) / (1 + (5670873830487 / 5000000000000 : ℝ)) = (10702381044461 / 42683495321948 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107944976594666061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 10702381044461 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 10702381044461 : ℝ) = (10702381044461 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (78125000000 / 557415679399 : ℝ) ≤ (34812168003523 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107944976594666061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (10702381044461 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1672247038197 / 3125000000000 : ℝ)) ≤ (34812168003523 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_307 : ∀ t : ℝ, (9163276801667 / 32000000000000 : ℝ) < t → t ≤ (36730850763921 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-33182310377578370546474239 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (36730850763921 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_308
  have hV : (520178303094705961281682468818493 / 156250000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9163276801667 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_307 (Vfield_monotoneOn (show (9163276801667 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9163276801667 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_308 : (16664910108429736415892429064905513 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (36730850763921 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (36730850763921 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (53568626227777 / 100000000000000 : ℝ) ≤ Real.sqrt (36730850763921 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (36730850763921 / 128000000000000 : ℝ) ≤ (26784313113889 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (26784313113889 / 50000000000000 : ℝ) = (50000000000000 / 26784313113889 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (53568626227777 / 100000000000000 : ℝ) = (7500000000000 / 53568626227777 : ℝ) := by norm_num
  have hL1 : (25228267062207 / 100000000000000 : ℝ) ≤ Real.log (1 + (36730850763921 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((36730850763921 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-61450041818343 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (26784313113889 / 106722124686782 : ℝ) ≤ (245893700665063 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (26784313113889 / 50000000000000 : ℝ) ≤ (245893700665063 / 500000000000000 : ℝ) := by
    have hw : (28361062343391 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (26784313113889 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (26784313113889 / 50000000000000 : ℝ) / (1 + (28361062343391 / 25000000000000 : ℝ)) = (26784313113889 / 106722124686782 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107900892546477061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 26784313113889 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 26784313113889 : ℝ) = (26784313113889 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 53568626227777 : ℝ) ≤ (2173486320753 / 15625000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107900892546477061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (26784313113889 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (53568626227777 / 100000000000000 : ℝ)) ≤ (2173486320753 / 15625000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_308 : ∀ t : ℝ, (36730850763921 / 128000000000000 : ℝ) < t → t ≤ (18404297160587 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-165708321128580294925811389 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (18404297160587 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_309
  have hV : (16664910108429736415892429064905513 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (36730850763921 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_308 (Vfield_monotoneOn (show (36730850763921 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (36730850763921 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_309 : (2085512081152808302671648564373139 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (18404297160587 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (18404297160587 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (6703160904731 / 12500000000000 : ℝ) ≤ Real.sqrt (18404297160587 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (18404297160587 / 64000000000000 : ℝ) ≤ (53625287237849 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (53625287237849 / 100000000000000 : ℝ) = (100000000000000 / 53625287237849 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6703160904731 / 12500000000000 : ℝ) = (937500000000 / 6703160904731 : ℝ) := by norm_num
  have hL1 : (25275450220311 / 100000000000000 : ℝ) ≤ Real.log (1 + (18404297160587 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((18404297160587 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-122692710575909 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (53625287237849 / 213471015820524 : ℝ) ≤ (30764222983759 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (53625287237849 / 100000000000000 : ℝ) ≤ (30764222983759 / 62500000000000 : ℝ) := by
    have hw : (28367753955131 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (53625287237849 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (53625287237849 / 100000000000000 : ℝ) / (1 + (28367753955131 / 25000000000000 : ℝ)) = (53625287237849 / 213471015820524 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107856875905475261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 53625287237849 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 53625287237849 : ℝ) = (53625287237849 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (937500000000 / 6703160904731 : ℝ) ≤ (27791606499841 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107856875905475261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (53625287237849 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6703160904731 / 12500000000000 : ℝ)) ≤ (27791606499841 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_309 : ∀ t : ℝ, (18404297160587 / 64000000000000 : ℝ) < t → t ≤ (36886337878427 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-517208771279826258019011 / 312500000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (36886337878427 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_310
  have hV : (2085512081152808302671648564373139 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (18404297160587 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_309 (Vfield_monotoneOn (show (18404297160587 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (18404297160587 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_310 : (16703265368951341045797613196510579 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (36886337878427 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (36886337878427 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (53681888442491 / 100000000000000 : ℝ) ≤ Real.sqrt (36886337878427 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (36886337878427 / 128000000000000 : ℝ) ≤ (13420472110623 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13420472110623 / 25000000000000 : ℝ) = (25000000000000 / 13420472110623 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (53681888442491 / 100000000000000 : ℝ) = (7500000000000 / 53681888442491 : ℝ) := by norm_num
  have hL1 : (2532261112641 / 10000000000000 : ℝ) ≤ Real.log (1 + (36886337878427 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((36886337878427 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24497153332243 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (53681888442492 / 213497775955091 : ℝ) ≤ (246333531094593 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13420472110623 / 25000000000000 : ℝ) ≤ (246333531094593 / 500000000000000 : ℝ) := by
    have hw : (113497775955091 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (13420472110623 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (13420472110623 / 25000000000000 : ℝ) / (1 + (113497775955091 / 100000000000000 : ℝ)) = (53681888442492 / 213497775955091 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107812926460571061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 13420472110623 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 13420472110623 : ℝ) = (13420472110623 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 53681888442491 : ℝ) ≤ (34703348389147 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107812926460571061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13420472110623 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (53681888442491 / 100000000000000 : ℝ)) ≤ (34703348389147 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_310 : ∀ t : ℝ, (36886337878427 / 128000000000000 : ℝ) < t → t ≤ (231025508973 / 800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-165306943875108949604086273 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (231025508973 / 800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_311
  have hV : (16703265368951341045797613196510579 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (36886337878427 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_310 (Vfield_monotoneOn (show (36886337878427 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (36886337878427 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_311 : (16722416314950065495947494045178689 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (231025508973 / 800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (231025508973 / 800000000000 : ℝ) := by norm_num
  have hs1 : (53738430030681 / 100000000000000 : ℝ) ≤ Real.sqrt (231025508973 / 800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (231025508973 / 800000000000 : ℝ) ≤ (26869215015341 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (26869215015341 / 50000000000000 : ℝ) = (50000000000000 / 26869215015341 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (53738430030681 / 100000000000000 : ℝ) = (2500000000000 / 17912810010227 : ℝ) := by norm_num
  have hL1 : (12684874900741 / 50000000000000 : ℝ) ≤ Real.log (1 + (231025508973 / 800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((231025508973 / 800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-15284906265011 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (26869215015341 / 106762264890864 : ℝ) ≤ (246552943388707 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (26869215015341 / 50000000000000 : ℝ) ≤ (246552943388707 / 500000000000000 : ℝ) := by
    have hw : (3547641555679 / 3125000000000 : ℝ) ≤ Real.sqrt (1 + (26869215015341 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (26869215015341 / 50000000000000 : ℝ) / (1 + (3547641555679 / 3125000000000 : ℝ)) = (26869215015341 / 106762264890864 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107769044001748261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 26869215015341 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 26869215015341 : ℝ) = (26869215015341 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 17912810010227 : ℝ) ≤ (138669205347033 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107769044001748261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (26869215015341 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (53738430030681 / 100000000000000 : ℝ)) ≤ (138669205347033 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_311 : ∀ t : ℝ, (231025508973 / 800000000000 : ℝ) < t → t ≤ (37041824992933 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-41277168024588697632100169 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (37041824992933 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_312
  have hV : (16722416314950065495947494045178689 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (231025508973 / 800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_311 (Vfield_monotoneOn (show (231025508973 / 800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (231025508973 / 800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_312 : (10463468458965286874007808686511 / 3125000000000000000000000000000 : ℝ) ≤ Vfield (37041824992933 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (37041824992933 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (33621820119 / 62500000000 : ℝ) ≤ Real.sqrt (37041824992933 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (37041824992933 / 128000000000000 : ℝ) ≤ (53794912190401 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (53794912190401 / 100000000000000 : ℝ) = (100000000000000 / 53794912190401 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33621820119 / 62500000000 : ℝ) = (1562500000 / 11207273373 : ℝ) := by norm_num
  have hL1 : (25416866266477 / 100000000000000 : ℝ) ≤ Real.log (1 + (37041824992933 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((37041824992933 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-12207315919097 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (53794912190401 / 213551277304894 : ℝ) ≤ (123386010898579 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (53794912190401 / 100000000000000 : ℝ) ≤ (123386010898579 / 250000000000000 : ℝ) := by
    have hw : (56775638652447 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (53794912190401 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (53794912190401 / 100000000000000 : ℝ) / (1 + (56775638652447 / 50000000000000 : ℝ)) = (53794912190401 / 213551277304894 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107725228320058061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 53794912190401 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 53794912190401 : ℝ) = (53794912190401 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1562500000 / 11207273373 : ℝ) ≤ (138525465534307 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107725228320058061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (53794912190401 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33621820119 / 62500000000 : ℝ)) ≤ (138525465534307 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_312 : ∀ t : ℝ, (37041824992933 / 128000000000000 : ℝ) < t → t ≤ (18559784275093 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-20613991947119796525926391 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (18559784275093 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_313
  have hV : (10463468458965286874007808686511 / 3125000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (37041824992933 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_312 (Vfield_monotoneOn (show (37041824992933 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (37041824992933 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_313 : (8380332537026275859385235492857849 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (18559784275093 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (18559784275093 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (26925667554321 / 50000000000000 : ℝ) ≤ Real.sqrt (18559784275093 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (18559784275093 / 64000000000000 : ℝ) ≤ (53851335108643 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (53851335108643 / 100000000000000 : ℝ) = (100000000000000 / 53851335108643 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (26925667554321 / 50000000000000 : ℝ) = (1250000000000 / 8975222518107 : ℝ) := by norm_num
  have hL1 : (25463960542313 / 100000000000000 : ℝ) ≤ Real.log (1 + (18559784275093 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((18559784275093 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-121867492123173 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (53851335108643 / 213578018529041 : ℝ) ≤ (30873845919923 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (53851335108643 / 100000000000000 : ℝ) ≤ (30873845919923 / 62500000000000 : ℝ) := by
    have hw : (113578018529041 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (53851335108643 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (53851335108643 / 100000000000000 : ℝ) / (1 + (113578018529041 / 100000000000000 : ℝ)) = (53851335108643 / 213578018529041 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107681479207612861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 53851335108643 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 53851335108643 : ℝ) = (53851335108643 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 8975222518107 : ℝ) ≤ (138382171799103 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107681479207612861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (53851335108643 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (26925667554321 / 50000000000000 : ℝ)) ≤ (138382171799103 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_313 : ∀ t : ℝ, (18559784275093 / 64000000000000 : ℝ) < t → t ≤ (37197312107439 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-20589585286894319996321021 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (37197312107439 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_314
  have hV : (8380332537026275859385235492857849 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (18559784275093 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_313 (Vfield_monotoneOn (show (18559784275093 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (18559784275093 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_314 : (524367593149613359934886464652033 / 156250000000000000000000000000000 : ℝ) ≤ Vfield (37197312107439 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (37197312107439 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (1684615592857 / 3125000000000 : ℝ) ≤ Real.sqrt (37197312107439 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (37197312107439 / 128000000000000 : ℝ) ≤ (2156307958857 / 4000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2156307958857 / 4000000000000 : ℝ) = (4000000000000 / 2156307958857 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1684615592857 / 3125000000000 : ℝ) = (234375000000 / 1684615592857 : ℝ) := by norm_num
  have hL1 : (25511032649881 / 100000000000000 : ℝ) ≤ Real.log (1 + (37197312107439 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((37197312107439 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-30415561794197 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (53907698971425 / 213604753458619 : ℝ) ≤ (247209181109569 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2156307958857 / 4000000000000 : ℝ) ≤ (247209181109569 / 500000000000000 : ℝ) := by
    have hw : (113604753458619 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (2156307958857 / 4000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (2156307958857 / 4000000000000 : ℝ) / (1 + (113604753458619 / 100000000000000 : ℝ)) = (53907698971425 / 213604753458619 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107637796457575861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (4000000000000 / 2156307958857 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (4000000000000 / 2156307958857 : ℝ) = (2156307958857 / 4000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (234375000000 / 1684615592857 : ℝ) ≤ (138239321838869 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107637796457575861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2156307958857 / 4000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1684615592857 / 3125000000000 : ℝ)) ≤ (138239321838869 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_314 : ∀ t : ℝ, (37197312107439 / 128000000000000 : ℝ) < t → t ≤ (9318763916173 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-20565357967689192423676439 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9318763916173 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_315
  have hV : (524367593149613359934886464652033 / 156250000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (37197312107439 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_314 (Vfield_monotoneOn (show (37197312107439 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (37197312107439 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_315 : (16798843301058309650584353907490279 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9318763916173 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9318763916173 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (53964003963791 / 100000000000000 : ℝ) ≤ Real.sqrt (9318763916173 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9318763916173 / 32000000000000 : ℝ) ≤ (3372750247737 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3372750247737 / 6250000000000 : ℝ) = (6250000000000 / 3372750247737 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (53964003963791 / 100000000000000 : ℝ) = (7500000000000 / 53964003963791 : ℝ) := by norm_num
  have hL1 : (638952065251 / 2500000000000 : ℝ) ≤ Real.log (1 + (9318763916173 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9318763916173 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-30364355655649 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (8994000660632 / 35605247016345 : ℝ) ≤ (247427264076671 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3372750247737 / 6250000000000 : ℝ) ≤ (247427264076671 / 500000000000000 : ℝ) := by
    have hw : (11363148209807 / 10000000000000 : ℝ) ≤ Real.sqrt (1 + (3372750247737 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3372750247737 / 6250000000000 : ℝ) / (1 + (11363148209807 / 10000000000000 : ℝ)) = (8994000660632 / 35605247016345 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107594179864155461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 3372750247737 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 3372750247737 : ℝ) = (3372750247737 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 53964003963791 : ℝ) ≤ (138096913367661 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107594179864155461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3372750247737 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (53964003963791 / 100000000000000 : ℝ)) ≤ (138096913367661 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_315 : ∀ t : ℝ, (9318763916173 / 32000000000000 : ℝ) < t → t ≤ (7470559844389 / 25600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-82165217287028243406624847 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7470559844389 / 25600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_316
  have hV : (16798843301058309650584353907490279 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9318763916173 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_315 (Vfield_monotoneOn (show (9318763916173 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9318763916173 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_316 : (131389891259144223422857728329177 / 39062500000000000000000000000000 : ℝ) ≤ Vfield (7470559844389 / 25600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7470559844389 / 25600000000000 : ℝ) := by norm_num
  have hs1 : (422033205233 / 781250000000 : ℝ) ≤ Real.sqrt (7470559844389 / 25600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7470559844389 / 25600000000000 : ℝ) ≤ (2160810010793 / 4000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2160810010793 / 4000000000000 : ℝ) = (4000000000000 / 2160810010793 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (422033205233 / 781250000000 : ℝ) = (58593750000 / 422033205233 : ℝ) := by norm_num
  have hL1 : (12802555221811 / 50000000000000 : ℝ) ≤ Real.log (1 + (7470559844389 / 25600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7470559844389 / 25600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3789156773187 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7717178609975 / 30522600635976 : ℝ) ≤ (247645017284467 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2160810010793 / 4000000000000 : ℝ) ≤ (247645017284467 / 500000000000000 : ℝ) := by
    have hw : (14207275556479 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (2160810010793 / 4000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (2160810010793 / 4000000000000 : ℝ) / (1 + (14207275556479 / 12500000000000 : ℝ)) = (7717178609975 / 30522600635976 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107550629222596261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (4000000000000 / 2160810010793 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (4000000000000 / 2160810010793 : ℝ) = (2160810010793 / 4000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (58593750000 / 422033205233 : ℝ) ≤ (68977472057993 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107550629222596261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2160810010793 / 4000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (422033205233 / 781250000000 : ℝ)) ≤ (68977472057993 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_316 : ∀ t : ℝ, (7470559844389 / 25600000000000 : ℝ) < t → t ≤ (18715271389599 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-82069676162867708416710287 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (18715271389599 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_317
  have hV : (131389891259144223422857728329177 / 39062500000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7470559844389 / 25600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_316 (Vfield_monotoneOn (show (7470559844389 / 25600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7470559844389 / 25600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_317 : (16836951367228171249965035272760543 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (18715271389599 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (18715271389599 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (54076438072647 / 100000000000000 : ℝ) ≤ Real.sqrt (18715271389599 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (18715271389599 / 64000000000000 : ℝ) ≤ (6759554759081 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6759554759081 / 12500000000000 : ℝ) = (12500000000000 / 6759554759081 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (54076438072647 / 100000000000000 : ℝ) = (2500000000000 / 18025479357549 : ℝ) := by norm_num
  have hL1 : (6413029042857 / 25000000000000 : ℝ) ≤ Real.log (1 + (18715271389599 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((18715271389599 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24209805565371 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (54076438072648 / 213684920524337 : ℝ) ≤ (123931220875793 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6759554759081 / 12500000000000 : ℝ) ≤ (123931220875793 / 250000000000000 : ℝ) := by
    have hw : (113684920524337 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (6759554759081 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (6759554759081 / 12500000000000 : ℝ) / (1 + (113684920524337 / 100000000000000 : ℝ)) = (54076438072648 / 213684920524337 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107507144329172461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 6759554759081 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 6759554759081 : ℝ) = (6759554759081 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 18025479357549 : ℝ) ≤ (2756268236613 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107507144329172461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6759554759081 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (54076438072647 / 100000000000000 : ℝ)) ≤ (2756268236613 / 20000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_317 : ∀ t : ℝ, (18715271389599 / 64000000000000 : ℝ) < t → t ≤ (37508286336451 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-163949577144467352996573009 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (37508286336451 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_318
  have hV : (16836951367228171249965035272760543 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (18715271389599 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_317 (Vfield_monotoneOn (show (18715271389599 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (18715271389599 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_318 : (131687337540112341859626130325611 / 39062500000000000000000000000000 : ℝ) ≤ Vfield (37508286336451 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (37508286336451 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (422910684019 / 781250000000 : ℝ) ≤ Real.sqrt (37508286336451 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (37508286336451 / 128000000000000 : ℝ) ≤ (54132567554433 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (54132567554433 / 100000000000000 : ℝ) = (100000000000000 / 54132567554433 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (422910684019 / 781250000000 : ℝ) = (58593750000 / 422910684019 : ℝ) := by norm_num
  have hL1 : (2569909981423 / 10000000000000 : ℝ) ≤ Real.log (1 + (37508286336451 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((37508286336451 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24169090835909 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (54132567554433 / 213711630320012 : ℝ) ≤ (248079538491539 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (54132567554433 / 100000000000000 : ℝ) ≤ (248079538491539 / 500000000000000 : ℝ) := by
    have hw : (28427907580003 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (54132567554433 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (54132567554433 / 100000000000000 : ℝ) / (1 + (28427907580003 / 25000000000000 : ℝ)) = (54132567554433 / 213711630320012 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107463724981181861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 54132567554433 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 54132567554433 : ℝ) = (54132567554433 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (58593750000 / 422910684019 : ℝ) ≤ (137672314274613 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107463724981181861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (54132567554433 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (422910684019 / 781250000000 : ℝ)) ≤ (137672314274613 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_318 : ∀ t : ℝ, (37508286336451 / 128000000000000 : ℝ) < t → t ≤ (4698253736713 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-32752214312577220406029053 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4698253736713 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_319
  have hV : (131687337540112341859626130325611 / 39062500000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (37508286336451 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_318 (Vfield_monotoneOn (show (37508286336451 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (37508286336451 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_319 : (1687498964059366551909477468118929 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (4698253736713 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4698253736713 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (5418863889641 / 10000000000000 : ℝ) ≤ Real.sqrt (4698253736713 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4698253736713 / 16000000000000 : ℝ) ≤ (54188638896411 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (54188638896411 / 100000000000000 : ℝ) = (100000000000000 / 54188638896411 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5418863889641 / 10000000000000 : ℝ) = (750000000000 / 5418863889641 : ℝ) := by norm_num
  have hL1 : (6436515348193 / 25000000000000 : ℝ) ≤ Real.log (1 + (4698253736713 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4698253736713 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24128458822547 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (54188638896411 / 213738333843280 : ℝ) ≤ (24829630851277 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (54188638896411 / 100000000000000 : ℝ) ≤ (24829630851277 / 50000000000000 : ℝ) := by
    have hw : (1421729173041 / 1250000000000 : ℝ) ≤ Real.sqrt (1 + (54188638896411 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (54188638896411 / 100000000000000 : ℝ) / (1 + (1421729173041 / 1250000000000 : ℝ)) = (54188638896411 / 213738333843280 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107420370976935661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 54188638896411 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 54188638896411 : ℝ) = (54188638896411 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 5418863889641 : ℝ) ≤ (137531649226829 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107420370976935661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (54188638896411 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5418863889641 / 10000000000000 : ℝ)) ≤ (137531649226829 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_319 : ∀ t : ℝ, (4698253736713 / 16000000000000 : ℝ) < t → t ≤ (37663773450957 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-32714760058751584533961761 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (37663773450957 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_320
  have hV : (1687498964059366551909477468118929 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4698253736713 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_319 (Vfield_monotoneOn (show (4698253736713 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4698253736713 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
