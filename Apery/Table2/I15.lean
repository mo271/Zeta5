import Apery.Table2.U15
import Apery.Table2.U16

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_600 : (268937816759738916207198546866431 / 50000000000000000000000000000000 : ℝ) ≤ Vfield (44328620319927 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (44328620319927 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (832246773799 / 1000000000000 : ℝ) ≤ Real.sqrt (44328620319927 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (44328620319927 / 64000000000000 : ℝ) ≤ (83224677379901 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (83224677379901 / 100000000000000 : ℝ) = (100000000000000 / 83224677379901 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (832246773799 / 1000000000000 : ℝ) = (75000000000 / 832246773799 : ℝ) := by norm_num
  have hL1 : (10525726092329 / 20000000000000 : ℝ) ≤ Real.log (1 + (44328620319927 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((44328620319927 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-8979104821587 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (83224677379901 / 230101294862843 : ℝ) ≤ (173524171296417 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (83224677379901 / 100000000000000 : ℝ) ≤ (173524171296417 / 250000000000000 : ℝ) := by
    have hw : (130101294862843 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (83224677379901 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (83224677379901 / 100000000000000 : ℝ) / (1 + (130101294862843 / 100000000000000 : ℝ)) = (83224677379901 / 230101294862843 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87669964160922861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 83224677379901 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 83224677379901 : ℝ) = (83224677379901 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (75000000000 / 832246773799 : ℝ) ≤ (17974946097509 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87669964160922861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (83224677379901 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (832246773799 / 1000000000000 : ℝ)) ≤ (17974946097509 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_600 : ∀ t : ℝ, (44328620319927 / 64000000000000 : ℝ) < t → t ≤ (11095134878389 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-63455602183216743753285187 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11095134878389 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_601
  have hV : (268937816759738916207198546866431 / 50000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (44328620319927 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_600 (Vfield_monotoneOn (show (44328620319927 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (44328620319927 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_601 : (6727683217326686002219884676708697 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (11095134878389 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11095134878389 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (20818350227313 / 25000000000000 : ℝ) ≤ Real.sqrt (11095134878389 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11095134878389 / 16000000000000 : ℝ) ≤ (83273400909253 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (83273400909253 / 100000000000000 : ℝ) = (100000000000000 / 83273400909253 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (20818350227313 / 25000000000000 : ℝ) = (625000000000 / 6939450075771 : ℝ) := by norm_num
  have hL1 : (52676546474667 / 100000000000000 : ℝ) ≤ Real.log (1 + (11095134878389 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11095134878389 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-2237519176543 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (83273400909253 / 230132468273652 : ℝ) ≤ (69438447237597 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (83273400909253 / 100000000000000 : ℝ) ≤ (69438447237597 / 100000000000000 : ℝ) := by
    have hw : (32533117068413 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (83273400909253 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (83273400909253 / 100000000000000 : ℝ) / (1 + (32533117068413 / 25000000000000 : ℝ)) = (83273400909253 / 230132468273652 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87641185441892661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 83273400909253 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 83273400909253 : ℝ) = (83273400909253 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (625000000000 / 6939450075771 : ℝ) ≤ (11227803371281 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87641185441892661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (83273400909253 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (20818350227313 / 25000000000000 : ℝ)) ≤ (11227803371281 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_601 : ∀ t : ℝ, (11095134878389 / 16000000000000 : ℝ) < t → t ≤ (8886491741437 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-15823723274103155536550479 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (8886491741437 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_602
  have hV : (6727683217326686002219884676708697 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11095134878389 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_601 (Vfield_monotoneOn (show (11095134878389 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11095134878389 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_602 : (26927674276425523415283465010941851 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (8886491741437 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (8886491741437 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (83322095946979 / 100000000000000 : ℝ) ≤ Real.sqrt (8886491741437 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (8886491741437 / 12800000000000 : ℝ) ≤ (4166104797349 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4166104797349 / 5000000000000 : ℝ) = (5000000000000 / 4166104797349 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (83322095946979 / 100000000000000 : ℝ) = (7500000000000 / 83322095946979 : ℝ) := by norm_num
  have hL1 : (52724439539241 / 100000000000000 : ℝ) ≤ Real.log (1 + (8886491741437 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((8886491741437 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-17842164513859 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (20830523986745 / 57540908554654 : ℝ) ≤ (173667988382499 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4166104797349 / 5000000000000 : ℝ) ≤ (173667988382499 / 250000000000000 : ℝ) := by
    have hw : (16270454277327 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (4166104797349 / 5000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (4166104797349 / 5000000000000 : ℝ) / (1 + (16270454277327 / 12500000000000 : ℝ)) = (20830523986745 / 57540908554654 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87612437326490061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 4166104797349 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 4166104797349 : ℝ) = (4166104797349 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 83322095946979 : ℝ) ≤ (89770214663023 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87612437326490061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4166104797349 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (83322095946979 / 100000000000000 : ℝ)) ≤ (89770214663023 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_602 : ∀ t : ℝ, (8886491741437 / 12800000000000 : ℝ) < t → t ≤ (22242188950407 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-7891852475256631956150613 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (22242188950407 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_603
  have hV : (26927674276425523415283465010941851 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (8886491741437 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_602 (Vfield_monotoneOn (show (8886491741437 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (8886491741437 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_603 : (5388921182676057406653143297699169 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (22242188950407 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (22242188950407 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (16674152508601 / 20000000000000 : ℝ) ≤ Real.sqrt (22242188950407 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (22242188950407 / 32000000000000 : ℝ) ≤ (41685381271503 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (41685381271503 / 50000000000000 : ℝ) = (50000000000000 / 41685381271503 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16674152508601 / 20000000000000 : ℝ) = (1500000000000 / 16674152508601 : ℝ) := by norm_num
  have hL1 : (52772309677339 / 100000000000000 : ℝ) ≤ Real.log (1 + (22242188950407 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((22242188950407 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-17784242791719 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (41685381271503 / 115097396351548 : ℝ) ≤ (34747956461767 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (41685381271503 / 50000000000000 : ℝ) ≤ (34747956461767 / 50000000000000 : ℝ) := by
    have hw : (16274349087887 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (41685381271503 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (41685381271503 / 50000000000000 : ℝ) / (1 + (16274349087887 / 12500000000000 : ℝ)) = (41685381271503 / 115097396351548 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87583719755955661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 41685381271503 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 41685381271503 : ℝ) = (41685381271503 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 16674152508601 : ℝ) ≤ (89718093301079 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87583719755955661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (41685381271503 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16674152508601 / 20000000000000 : ℝ)) ≤ (89718093301079 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_603 : ∀ t : ℝ, (22242188950407 / 32000000000000 : ℝ) < t → t ≤ (5573527036009 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-15704129903902918709296317 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5573527036009 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_604
  have hV : (5388921182676057406653143297699169 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (22242188950407 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_603 (Vfield_monotoneOn (show (22242188950407 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (22242188950407 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_604 : (13489219970390146660443848239415509 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (5573527036009 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5573527036009 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (41734005304461 / 50000000000000 : ℝ) ≤ Real.sqrt (5573527036009 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5573527036009 / 8000000000000 : ℝ) ≤ (83468010608923 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (83468010608923 / 100000000000000 : ℝ) = (100000000000000 / 83468010608923 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (41734005304461 / 50000000000000 : ℝ) = (1250000000000 / 13911335101487 : ℝ) := by norm_num
  have hL1 : (5286798126183 / 10000000000000 : ℝ) ≤ Real.log (1 + (5573527036009 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5573527036009 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-7067440102071 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (83468010608923 / 230257087312020 : ℝ) ≤ (10867696353779 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (83468010608923 / 100000000000000 : ℝ) ≤ (10867696353779 / 15625000000000 : ℝ) := by
    have hw : (6512854365601 / 5000000000000 : ℝ) ≤ Real.sqrt (1 + (83468010608923 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (83468010608923 / 100000000000000 : ℝ) / (1 + (6512854365601 / 5000000000000 : ℝ)) = (83468010608923 / 230257087312020 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87526376015304061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 83468010608923 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 83468010608923 : ℝ) = (83468010608923 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 13911335101487 : ℝ) ≤ (89614122359247 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87526376015304061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (83468010608923 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (41734005304461 / 50000000000000 : ℝ)) ≤ (89614122359247 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_604 : ∀ t : ℝ, (5573527036009 / 8000000000000 : ℝ) < t → t ≤ (4469205467533 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-62500588152921768688767653 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4469205467533 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_605
  have hV : (13489219970390146660443848239415509 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5573527036009 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_604 (Vfield_monotoneOn (show (5573527036009 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5573527036009 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_605 : (5402447015808460528597052994152531 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (4469205467533 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4469205467533 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (16713029100699 / 20000000000000 : ℝ) ≤ Real.sqrt (4469205467533 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4469205467533 / 6400000000000 : ℝ) ≤ (10445643187937 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (10445643187937 / 12500000000000 : ℝ) = (12500000000000 / 10445643187937 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16713029100699 / 20000000000000 : ℝ) = (500000000000 / 5571009700233 : ℝ) := by norm_num
  have hL1 : (26481780701639 / 50000000000000 : ℝ) ≤ Real.log (1 + (4469205467533 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4469205467533 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-17553224565503 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (20891286375874 / 57579838035797 : ℝ) ≤ (174026197315593 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (10445643187937 / 12500000000000 : ℝ) ≤ (174026197315593 / 250000000000000 : ℝ) := by
    have hw : (32579838035797 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (10445643187937 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (10445643187937 / 12500000000000 : ℝ) / (1 + (32579838035797 / 25000000000000 : ℝ)) = (20891286375874 / 57579838035797 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87469153753252461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 10445643187937 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 10445643187937 : ℝ) = (10445643187937 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 5571009700233 : ℝ) ≤ (8951051204783 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87469153753252461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (10445643187937 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16713029100699 / 20000000000000 : ℝ)) ≤ (8951051204783 / 100000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_605 : ∀ t : ℝ, (4469205467533 / 6400000000000 : ℝ) < t → t ≤ (11198973265647 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-12437384797123175490872043 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11198973265647 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_606
  have hV : (5402447015808460528597052994152531 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4469205467533 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_605 (Vfield_monotoneOn (show (4469205467533 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4469205467533 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_606 : (2704599145501444047483726011882979 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (11198973265647 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11198973265647 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (8366216762091 / 10000000000000 : ℝ) ≤ Real.sqrt (11198973265647 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11198973265647 / 16000000000000 : ℝ) ≤ (83662167620911 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (83662167620911 / 100000000000000 : ℝ) = (100000000000000 / 83662167620911 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8366216762091 / 10000000000000 : ℝ) = (250000000000 / 2788738920697 : ℝ) := by norm_num
  have hL1 : (331619064227 / 625000000000 : ℝ) ≤ Real.log (1 + (11198973265647 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11198973265647 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-2179764311753 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (83662167620911 / 230381587239262 : ℝ) ≤ (87084475217099 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (83662167620911 / 100000000000000 : ℝ) ≤ (87084475217099 / 125000000000000 : ℝ) := by
    have hw : (65190793619631 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (83662167620911 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (83662167620911 / 100000000000000 : ℝ) / (1 + (65190793619631 / 50000000000000 : ℝ)) = (83662167620911 / 230381587239262 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87412052505810461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 83662167620911 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 83662167620911 : ℝ) = (83662167620911 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (250000000000 / 2788738920697 : ℝ) ≤ (89407260286841 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87412052505810461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (83662167620911 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8366216762091 / 10000000000000 : ℝ)) ≤ (89407260286841 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_606 : ∀ t : ℝ, (11198973265647 / 16000000000000 : ℝ) < t → t ≤ (22449865724923 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-15468858969577255085770557 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (22449865724923 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_607
  have hV : (2704599145501444047483726011882979 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11198973265647 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_606 (Vfield_monotoneOn (show (11198973265647 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11198973265647 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_607 : (1083188367794615269754628419335587 / 200000000000000000000000000000000 : ℝ) ≤ Vfield (22449865724923 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (22449865724923 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (3350363094123 / 4000000000000 : ℝ) ≤ Real.sqrt (22449865724923 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (22449865724923 / 32000000000000 : ℝ) ≤ (20939769338269 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20939769338269 / 25000000000000 : ℝ) = (25000000000000 / 20939769338269 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3350363094123 / 4000000000000 : ℝ) = (100000000000 / 1116787698041 : ℝ) := by norm_num
  have hL1 : (5315444805509 / 10000000000000 : ℝ) ≤ Real.log (1 + (22449865724923 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((22449865724923 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3464653764107 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (41879538676538 / 115221896321401 : ℝ) ≤ (348622804339177 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20939769338269 / 25000000000000 : ℝ) ≤ (348622804339177 / 500000000000000 : ℝ) := by
    have hw : (65221896321401 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (20939769338269 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (20939769338269 / 25000000000000 : ℝ) / (1 + (65221896321401 / 50000000000000 : ℝ)) = (41879538676538 / 115221896321401 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87355071811654261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 20939769338269 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 20939769338269 : ℝ) = (20939769338269 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (100000000000 / 1116787698041 : ℝ) ≤ (17860873002609 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87355071811654261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20939769338269 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3350363094123 / 4000000000000 : ℝ)) ≤ (17860873002609 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_607 : ∀ t : ℝ, (22449865724923 / 32000000000000 : ℝ) < t → t ≤ (2812723114819 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-61566041294775261119503473 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2812723114819 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_608
  have hV : (1083188367794615269754628419335587 / 200000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (22449865724923 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_607 (Vfield_monotoneOn (show (22449865724923 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (22449865724923 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_608 : (27113388424086581263315795428089701 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2812723114819 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2812723114819 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (83855875089629 / 100000000000000 : ℝ) ≤ Real.sqrt (2812723114819 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2812723114819 / 4000000000000 : ℝ) ≤ (8385587508963 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8385587508963 / 10000000000000 : ℝ) = (10000000000000 / 8385587508963 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (83855875089629 / 100000000000000 : ℝ) = (7500000000000 / 83855875089629 : ℝ) := by norm_num
  have hL1 : (53249754913229 / 100000000000000 : ℝ) ≤ Real.log (1 + (2812723114819 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2812723114819 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-34417372666439 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (83855875089630 / 230505968396267 : ℝ) ≤ (348907107336887 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8385587508963 / 10000000000000 : ℝ) ≤ (348907107336887 / 500000000000000 : ℝ) := by
    have hw : (130505968396267 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (8385587508963 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (8385587508963 / 10000000000000 : ℝ) / (1 + (130505968396267 / 100000000000000 : ℝ)) = (83855875089630 / 230505968396267 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87298211212112261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 8385587508963 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 8385587508963 : ℝ) = (8385587508963 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 83855875089629 : ℝ) ≤ (89201824179797 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87298211212112261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8385587508963 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (83855875089629 / 100000000000000 : ℝ)) ≤ (89201824179797 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_608 : ∀ t : ℝ, (2812723114819 / 4000000000000 : ℝ) < t → t ≤ (22553704112181 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-15314666294827722644585879 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (22553704112181 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_609
  have hV : (27113388424086581263315795428089701 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2812723114819 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_608 (Vfield_monotoneOn (show (2812723114819 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2812723114819 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_609 : (27147029267499409423987850801511623 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (22553704112181 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (22553704112181 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (83952561217967 / 100000000000000 : ℝ) ≤ Real.sqrt (22553704112181 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (22553704112181 / 32000000000000 : ℝ) ≤ (5247035076123 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5247035076123 / 6250000000000 : ℝ) = (6250000000000 / 5247035076123 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (83952561217967 / 100000000000000 : ℝ) = (7500000000000 / 83952561217967 : ℝ) := by norm_num
  have hL1 : (53344971023877 / 100000000000000 : ℝ) ≤ Real.log (1 + (22553704112181 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((22553704112181 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-34188731657149 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (41976280608984 / 115284057271007 : ℝ) ≤ (349190812141749 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5247035076123 / 6250000000000 : ℝ) ≤ (349190812141749 / 500000000000000 : ℝ) := by
    have hw : (65284057271007 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (5247035076123 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (5247035076123 / 6250000000000 : ℝ) / (1 + (65284057271007 / 50000000000000 : ℝ)) = (41976280608984 / 115284057271007 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87241470251139861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 5247035076123 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 5247035076123 : ℝ) = (5247035076123 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 83952561217967 : ℝ) ≤ (4454981787843 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87241470251139861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5247035076123 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (83952561217967 / 100000000000000 : ℝ)) ≤ (4454981787843 / 50000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_609 : ∀ t : ℝ, (22553704112181 / 32000000000000 : ℝ) < t → t ≤ (2260562330581 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-60953238953446217826303043 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2260562330581 / 3200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_610
  have hV : (27147029267499409423987850801511623 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (22553704112181 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_609 (Vfield_monotoneOn (show (22553704112181 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (22553704112181 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_610 : (3397578981157433215538735679542983 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (2260562330581 / 3200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2260562330581 / 3200000000000 : ℝ) := by norm_num
  have hs1 : (10506142015407 / 12500000000000 : ℝ) ≤ Real.sqrt (2260562330581 / 3200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2260562330581 / 3200000000000 : ℝ) ≤ (84049136123257 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (84049136123257 / 100000000000000 : ℝ) = (100000000000000 / 84049136123257 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10506142015407 / 12500000000000 : ℝ) = (312500000000 / 3502047338469 : ℝ) := by norm_num
  have hL1 : (26720048279841 / 50000000000000 : ℝ) ≤ Real.log (1 + (2260562330581 / 3200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2260562330581 / 3200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-33960612222663 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (84049136123257 / 230630231122301 : ℝ) ≤ (349473921020947 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (84049136123257 / 100000000000000 : ℝ) ≤ (349473921020947 / 500000000000000 : ℝ) := by
    have hw : (130630231122301 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (84049136123257 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (84049136123257 / 100000000000000 : ℝ) / (1 + (130630231122301 / 100000000000000 : ℝ)) = (84049136123257 / 230630231122301 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87184848475300261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 84049136123257 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 84049136123257 : ℝ) = (84049136123257 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (312500000000 / 3502047338469 : ℝ) ≤ (44498898865121 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87184848475300261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (84049136123257 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10506142015407 / 12500000000000 : ℝ)) ≤ (44498898865121 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_610 : ∀ t : ℝ, (2260562330581 / 3200000000000 : ℝ) < t → t ≤ (22657542499439 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-94765155754649593160749 / 156250000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (22657542499439 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_611
  have hV : (3397578981157433215538735679542983 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2260562330581 / 3200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_610 (Vfield_monotoneOn (show (2260562330581 / 3200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2260562330581 / 3200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_611 : (27214196292861031197462427065353819 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (22657542499439 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (22657542499439 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (84145600188451 / 100000000000000 : ℝ) ≤ Real.sqrt (22657542499439 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (22657542499439 / 32000000000000 : ℝ) ≤ (21036400047113 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (21036400047113 / 25000000000000 : ℝ) = (25000000000000 / 21036400047113 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (84145600188451 / 100000000000000 : ℝ) = (7500000000000 / 84145600188451 : ℝ) := by norm_num
  have hL1 : (53535131692801 / 100000000000000 : ℝ) ≤ Real.log (1 + (22657542499439 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((22657542499439 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-33733011988767 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (42072800094226 / 115346159089641 : ℝ) ≤ (13990257449149 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (21036400047113 / 25000000000000 : ℝ) ≤ (13990257449149 / 20000000000000 : ℝ) := by
    have hw : (65346159089641 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (21036400047113 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (21036400047113 / 25000000000000 : ℝ) / (1 + (65346159089641 / 50000000000000 : ℝ)) = (42072800094226 / 115346159089641 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87128345433744661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 21036400047113 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 21036400047113 : ℝ) = (21036400047113 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 84145600188451 : ℝ) ≤ (22224077025507 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87128345433744661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (21036400047113 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (84145600188451 / 100000000000000 : ℝ)) ≤ (22224077025507 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_611 : ∀ t : ℝ, (22657542499439 / 32000000000000 : ℝ) < t → t ≤ (5677365423267 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-6034798938103663218817481 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5677365423267 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_612
  have hV : (27214196292861031197462427065353819 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (22657542499439 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_611 (Vfield_monotoneOn (show (22657542499439 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (22657542499439 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_612 : (6811930680285760674441976490472251 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (5677365423267 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5677365423267 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (21060488448579 / 25000000000000 : ℝ) ≤ Real.sqrt (5677365423267 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5677365423267 / 8000000000000 : ℝ) ≤ (84241953794317 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (84241953794317 / 100000000000000 : ℝ) = (100000000000000 / 84241953794317 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21060488448579 / 25000000000000 : ℝ) = (625000000000 / 7020162816193 : ℝ) := by norm_num
  have hL1 : (536300765949 / 1000000000000 : ℝ) ≤ Real.log (1 + (5677365423267 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5677365423267 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-2094120537339 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (84241953794317 / 230754375755015 : ℝ) ≤ (350038360006491 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (84241953794317 / 100000000000000 : ℝ) ≤ (350038360006491 / 500000000000000 : ℝ) := by
    have hw : (26150875151003 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (84241953794317 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (84241953794317 / 100000000000000 : ℝ) / (1 + (26150875151003 / 20000000000000 : ℝ)) = (84241953794317 / 230754375755015 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87071960678191461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 84241953794317 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 84241953794317 : ℝ) = (84241953794317 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (625000000000 / 7020162816193 : ℝ) ≤ (17759032978043 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87071960678191461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (84241953794317 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21060488448579 / 25000000000000 : ℝ)) ≤ (17759032978043 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_612 : ∀ t : ℝ, (5677365423267 / 8000000000000 : ℝ) < t → t ≤ (22761380886697 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-12009610884165597771909209 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (22761380886697 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_613
  have hV : (6811930680285760674441976490472251 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5677365423267 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_612 (Vfield_monotoneOn (show (5677365423267 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5677365423267 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_613 : (341015140703663693197903243538117 / 62500000000000000000000000000000 : ℝ) ≤ Vfield (22761380886697 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (22761380886697 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (1054227466493 / 1250000000000 : ℝ) ≤ Real.sqrt (22761380886697 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (22761380886697 / 32000000000000 : ℝ) ≤ (84338197319441 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (84338197319441 / 100000000000000 : ℝ) = (100000000000000 / 84338197319441 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1054227466493 / 1250000000000 : ℝ) = (93750000000 / 1054227466493 : ℝ) := by norm_num
  have hL1 : (26862465718577 / 50000000000000 : ℝ) ≤ Real.log (1 + (22761380886697 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((22761380886697 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-33279359706623 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (84338197319441 / 230816403891457 : ℝ) ≤ (8757992364573 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (84338197319441 / 100000000000000 : ℝ) ≤ (8757992364573 / 12500000000000 : ℝ) := by
    have hw : (130816403891457 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (84338197319441 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (84338197319441 / 100000000000000 : ℝ) / (1 + (130816403891457 / 100000000000000 : ℝ)) = (84338197319441 / 230816403891457 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (87015693762905661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 84338197319441 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 84338197319441 : ℝ) = (84338197319441 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (93750000000 / 1054227466493 : ℝ) ≤ (88694366128551 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (87015693762905661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (84338197319441 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1054227466493 / 1250000000000 : ℝ)) ≤ (88694366128551 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_613 : ∀ t : ℝ, (22761380886697 / 32000000000000 : ℝ) < t → t ≤ (11406650040163 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-14937461259361062871959671 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11406650040163 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_614
  have hV : (341015140703663693197903243538117 / 62500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (22761380886697 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_613 (Vfield_monotoneOn (show (22761380886697 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (22761380886697 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_614 : (6828665504963001647328771091568447 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (11406650040163 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11406650040163 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (21108582785063 / 25000000000000 : ℝ) ≤ Real.sqrt (11406650040163 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11406650040163 / 16000000000000 : ℝ) ≤ (84434331140253 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (84434331140253 / 100000000000000 : ℝ) = (100000000000000 / 84434331140253 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21108582785063 / 25000000000000 : ℝ) = (1875000000000 / 21108582785063 : ℝ) := by norm_num
  have hL1 : (10763939278051 / 20000000000000 : ℝ) ≤ Real.log (1 + (11406650040163 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11406650040163 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6610660598047 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (28144777046751 / 76959467543488 : ℝ) ≤ (350600442174043 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (84434331140253 / 100000000000000 : ℝ) ≤ (350600442174043 / 500000000000000 : ℝ) := by
    have hw : (2044975041101 / 1562500000000 : ℝ) ≤ Real.sqrt (1 + (84434331140253 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (84434331140253 / 100000000000000 : ℝ) / (1 + (2044975041101 / 1562500000000 : ℝ)) = (28144777046751 / 76959467543488 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86959544244681061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 84434331140253 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 84434331140253 : ℝ) = (84434331140253 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 21108582785063 : ℝ) ≤ (88593909866373 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86959544244681061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (84434331140253 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21108582785063 / 25000000000000 : ℝ)) ≤ (88593909866373 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_614 : ∀ t : ℝ, (11406650040163 / 16000000000000 : ℝ) < t → t ≤ (89520072139 / 125000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-59158420760117650590183117 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (89520072139 / 125000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_615
  have hV : (6828665504963001647328771091568447 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11406650040163 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_614 (Vfield_monotoneOn (show (11406650040163 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11406650040163 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_615 : (27381450715160848600471049936757927 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (89520072139 / 125000000000 : ℝ) := by
  have hp : (0 : ℝ) < (89520072139 / 125000000000 : ℝ) := by norm_num
  have hs1 : (84626271163983 / 100000000000000 : ℝ) ≤ Real.sqrt (89520072139 / 125000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (89520072139 / 125000000000 : ℝ) ≤ (5289141947749 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5289141947749 / 6250000000000 : ℝ) = (6250000000000 / 5289141947749 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (84626271163983 / 100000000000000 : ℝ) = (2500000000000 / 28208757054661 : ℝ) := by norm_num
  have hL1 : (6751119663667 / 12500000000000 : ℝ) ≤ Real.log (1 + (89520072139 / 125000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((89520072139 / 125000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-4075339606843 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (21156567790996 / 57750578020777 : ℝ) ≤ (35116018520193 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5289141947749 / 6250000000000 : ℝ) ≤ (35116018520193 / 50000000000000 : ℝ) := by
    have hw : (32750578020777 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (5289141947749 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (5289141947749 / 6250000000000 : ℝ) / (1 + (32750578020777 / 25000000000000 : ℝ)) = (21156567790996 / 57750578020777 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86847595639103661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 5289141947749 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 5289141947749 : ℝ) = (5289141947749 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 28208757054661 : ℝ) ≤ (22098504278703 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86847595639103661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5289141947749 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (84626271163983 / 100000000000000 : ℝ)) ≤ (22098504278703 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_615 : ∀ t : ℝ, (89520072139 / 125000000000 : ℝ) < t → t ≤ (11489045952349 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-58500159672633298754498831 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11489045952349 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_616
  have hV : (27381450715160848600471049936757927 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (89520072139 / 125000000000 : ℝ) := by norm_num
    refine le_trans V_pt_615 (Vfield_monotoneOn (show (89520072139 / 125000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (89520072139 / 125000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_616 : (1096823444453893056999228311067947 / 200000000000000000000000000000000 : ℝ) ≤ Vfield (11489045952349 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11489045952349 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (3389549520563 / 4000000000000 : ℝ) ≤ Real.sqrt (11489045952349 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11489045952349 / 16000000000000 : ℝ) ≤ (21184684503519 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (21184684503519 / 25000000000000 : ℝ) = (25000000000000 / 21184684503519 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3389549520563 / 4000000000000 : ℝ) = (300000000000 / 3389549520563 : ℝ) := by norm_num
  have hL1 : (54119887407317 / 100000000000000 : ℝ) ≤ Real.log (1 + (11489045952349 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11489045952349 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6467832815273 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7061561501173 / 19256249394500 : ℝ) ≤ (351487673483419 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (21184684503519 / 25000000000000 : ℝ) ≤ (351487673483419 / 500000000000000 : ℝ) := by
    have hw : (65537496367 / 50000000000 : ℝ) ≤ Real.sqrt (1 + (21184684503519 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (21184684503519 / 25000000000000 : ℝ) / (1 + (65537496367 / 50000000000 : ℝ)) = (7061561501173 / 19256249394500 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86782097982805861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 21184684503519 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 21184684503519 : ℝ) = (21184684503519 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (300000000000 / 3389549520563 : ℝ) ≤ (88277307859223 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86782097982805861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (21184684503519 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3389549520563 / 4000000000000 : ℝ)) ≤ (88277307859223 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_616 : ∀ t : ℝ, (11489045952349 / 16000000000000 : ℝ) < t → t ≤ (4601713724651 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-58258373594371835546345837 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4601713724651 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_617
  have hV : (1096823444453893056999228311067947 / 200000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11489045952349 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_616 (Vfield_monotoneOn (show (11489045952349 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11489045952349 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_617 : (13720067266765411286257451489325691 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (4601713724651 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4601713724651 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (42397457750339 / 50000000000000 : ℝ) ≤ Real.sqrt (4601713724651 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4601713724651 / 6400000000000 : ℝ) ≤ (84794915500679 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (84794915500679 / 100000000000000 : ℝ) = (100000000000000 / 84794915500679 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (42397457750339 / 50000000000000 : ℝ) = (3750000000000 / 42397457750339 : ℝ) := by norm_num
  have hL1 : (54175306344833 / 100000000000000 : ℝ) ≤ Real.log (1 + (4601713724651 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4601713724651 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-16103823852797 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (84794915500679 / 231111317950691 : ℝ) ≤ (175825559364421 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (84794915500679 / 100000000000000 : ℝ) ≤ (175825559364421 / 250000000000000 : ℝ) := by
    have hw : (131111317950691 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (84794915500679 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (84794915500679 / 100000000000000 : ℝ) / (1 + (131111317950691 / 100000000000000 : ℝ)) = (84794915500679 / 231111317950691 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86749408933721261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 84794915500679 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 84794915500679 : ℝ) = (84794915500679 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 42397457750339 : ℝ) ≤ (17643825264457 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86749408933721261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (84794915500679 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (42397457750339 / 50000000000000 : ℝ)) ≤ (17643825264457 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_617 : ∀ t : ℝ, (4601713724651 / 6400000000000 : ℝ) < t → t ≤ (5759761335453 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-11605644135575527296666809 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5759761335453 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_618
  have hV : (13720067266765411286257451489325691 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4601713724651 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_617 (Vfield_monotoneOn (show (4601713724651 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4601713724651 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_618 : (13729835068531608032109630889686489 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (5759761335453 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5759761335453 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (42425527896881 / 50000000000000 : ℝ) ≤ Real.sqrt (5759761335453 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5759761335453 / 8000000000000 : ℝ) ≤ (84851055793763 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (84851055793763 / 100000000000000 : ℝ) = (100000000000000 / 84851055793763 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (42425527896881 / 50000000000000 : ℝ) = (3750000000000 / 42425527896881 : ℝ) := by norm_num
  have hL1 : (54230694586773 / 100000000000000 : ℝ) ≤ Real.log (1 + (5759761335453 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5759761335453 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-32076304073227 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (84851055793763 / 231147633106039 : ℝ) ≤ (70362873058457 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (84851055793763 / 100000000000000 : ℝ) ≤ (70362873058457 / 100000000000000 : ℝ) := by
    have hw : (131147633106039 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (84851055793763 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (84851055793763 / 100000000000000 : ℝ) / (1 + (131147633106039 / 100000000000000 : ℝ)) = (84851055793763 / 231147633106039 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86716759621032661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 84851055793763 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 84851055793763 : ℝ) = (84851055793763 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 42425527896881 : ℝ) ≤ (88161059672863 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86716759621032661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (84851055793763 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (42425527896881 / 50000000000000 : ℝ)) ≤ (88161059672863 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_618 : ∀ t : ℝ, (5759761335453 / 8000000000000 : ℝ) < t → t ≤ (23069522060369 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-11561137998979399089383473 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23069522060369 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_619
  have hV : (13729835068531608032109630889686489 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5759761335453 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_618 (Vfield_monotoneOn (show (5759761335453 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5759761335453 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_619 : (5495838589163940881134279840825749 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (23069522060369 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23069522060369 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (16981431793421 / 20000000000000 : ℝ) ≤ Real.sqrt (23069522060369 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23069522060369 / 32000000000000 : ℝ) ≤ (42453579483553 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (42453579483553 / 50000000000000 : ℝ) = (50000000000000 / 42453579483553 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16981431793421 / 20000000000000 : ℝ) = (1500000000000 / 16981431793421 : ℝ) := by norm_num
  have hL1 : (27143026083561 / 50000000000000 : ℝ) ≤ Real.log (1 + (23069522060369 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23069522060369 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-31945132726097 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (42453579483553 / 115591969104200 : ℝ) ≤ (43997176701017 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (42453579483553 / 50000000000000 : ℝ) ≤ (43997176701017 / 62500000000000 : ℝ) := by
    have hw : (327959845521 / 250000000000 : ℝ) ≤ Real.sqrt (1 + (42453579483553 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (42453579483553 / 50000000000000 : ℝ) / (1 + (327959845521 / 250000000000 : ℝ)) = (42453579483553 / 115591969104200 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86684149957862461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 42453579483553 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 42453579483553 : ℝ) = (42453579483553 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 16981431793421 : ℝ) ≤ (22025776883337 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86684149957862461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (42453579483553 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16981431793421 / 20000000000000 : ℝ)) ≤ (22025776883337 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_619 : ∀ t : ℝ, (23069522060369 / 32000000000000 : ℝ) < t → t ≤ (11549999389463 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-28794360417848551123167047 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11549999389463 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_620
  have hV : (5495838589163940881134279840825749 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23069522060369 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_619 (Vfield_monotoneOn (show (23069522060369 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23069522060369 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_620 : (27498702983601388604718403069284791 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (11549999389463 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11549999389463 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (84963225094239 / 100000000000000 : ℝ) ≤ Real.sqrt (11549999389463 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11549999389463 / 16000000000000 : ℝ) ≤ (531020156839 / 625000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (531020156839 / 625000000000 : ℝ) = (625000000000 / 531020156839 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (84963225094239 / 100000000000000 : ℝ) = (2500000000000 / 28321075031413 : ℝ) := by norm_num
  have hL1 : (849084048747 / 1562500000000 : ℝ) ≤ Real.log (1 + (11549999389463 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11549999389463 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-31814133212817 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (42481612547120 / 115610116633059 : ℝ) ≤ (70428052821869 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (531020156839 / 625000000000 : ℝ) ≤ (70428052821869 / 100000000000000 : ℝ) := by
    have hw : (65610116633059 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (531020156839 / 625000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (531020156839 / 625000000000 : ℝ) / (1 + (65610116633059 / 50000000000000 : ℝ)) = (42481612547120 / 115610116633059 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86651579857620661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (625000000000 / 531020156839 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (625000000000 / 531020156839 : ℝ) = (531020156839 / 625000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 28321075031413 : ℝ) ≤ (88045269527869 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86651579857620661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (531020156839 / 625000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (84963225094239 / 100000000000000 : ℝ)) ≤ (88045269527869 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_620 : ∀ t : ℝ, (11549999389463 / 16000000000000 : ℝ) < t → t ≤ (23130475497483 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-14344021558441055585102933 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23130475497483 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_621
  have hV : (27498702983601388604718403069284791 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11549999389463 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_620 (Vfield_monotoneOn (show (11549999389463 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11549999389463 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_621 : (5503640054827389365974502450047379 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (23130475497483 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23130475497483 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (17003850849691 / 20000000000000 : ℝ) ≤ Real.sqrt (23130475497483 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23130475497483 / 32000000000000 : ℝ) ≤ (10627406781057 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (10627406781057 / 12500000000000 : ℝ) = (12500000000000 / 10627406781057 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17003850849691 / 20000000000000 : ℝ) = (1500000000000 / 17003850849691 : ℝ) := by norm_num
  have hL1 : (54396675478703 / 100000000000000 : ℝ) ≤ Real.log (1 + (23130475497483 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23130475497483 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-15841652541887 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (85019254248456 / 231256518287525 : ℝ) ≤ (70460583445489 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (10627406781057 / 12500000000000 : ℝ) ≤ (70460583445489 / 100000000000000 : ℝ) := by
    have hw : (5250260731501 / 4000000000000 : ℝ) ≤ Real.sqrt (1 + (10627406781057 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (10627406781057 / 12500000000000 : ℝ) / (1 + (5250260731501 / 4000000000000 : ℝ)) = (85019254248456 / 231256518287525 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86619049234000661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 10627406781057 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 10627406781057 : ℝ) = (10627406781057 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 17003850849691 : ℝ) ≤ (2199688632057 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86619049234000661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (10627406781057 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17003850849691 / 20000000000000 : ℝ)) ≤ (2199688632057 / 25000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_621 : ∀ t : ℝ, (23130475497483 / 32000000000000 : ℝ) < t → t ≤ (579023805401 / 800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-28583492248328765007807251 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (579023805401 / 800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_622
  have hV : (5503640054827389365974502450047379 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23130475497483 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_621 (Vfield_monotoneOn (show (23130475497483 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23130475497483 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_622 : (27537684841081979456136489048838969 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (579023805401 / 800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (579023805401 / 800000000000 : ℝ) := by norm_num
  have hs1 : (85075246502801 / 100000000000000 : ℝ) ≤ Real.sqrt (579023805401 / 800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (579023805401 / 800000000000 : ℝ) ≤ (42537623251401 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (42537623251401 / 50000000000000 : ℝ) = (50000000000000 / 42537623251401 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (85075246502801 / 100000000000000 : ℝ) = (7500000000000 / 85075246502801 : ℝ) := by norm_num
  have hL1 : (27225970638811 / 50000000000000 : ℝ) ≤ Real.log (1 + (579023805401 / 800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((579023805401 / 800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-31552647891117 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (85075246502802 / 231292793280943 : ℝ) ≤ (352465373392547 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (42537623251401 / 50000000000000 : ℝ) ≤ (352465373392547 / 500000000000000 : ℝ) := by
    have hw : (131292793280943 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (42537623251401 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (42537623251401 / 50000000000000 : ℝ) / (1 + (131292793280943 / 100000000000000 : ℝ)) = (85075246502802 / 231292793280943 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86586558000980261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 42537623251401 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 42537623251401 : ℝ) = (42537623251401 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 85075246502801 : ℝ) ≤ (87929934424149 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86586558000980261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (42537623251401 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (85075246502801 / 100000000000000 : ℝ)) ≤ (87929934424149 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_622 : ∀ t : ℝ, (579023805401 / 800000000000 : ℝ) < t → t ≤ (23191428934597 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-56960856902472263952707153 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23191428934597 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_623
  have hV : (27537684841081979456136489048838969 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (579023805401 / 800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_622 (Vfield_monotoneOn (show (579023805401 / 800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (579023805401 / 800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_623 : (3444644588502601683274645290214709 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (23191428934597 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23191428934597 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (10641400241261 / 12500000000000 : ℝ) ≤ Real.sqrt (23191428934597 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23191428934597 / 32000000000000 : ℝ) ≤ (85131201930089 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (85131201930089 / 100000000000000 : ℝ) = (100000000000000 / 85131201930089 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10641400241261 / 12500000000000 : ℝ) = (937500000000 / 10641400241261 : ℝ) := by norm_num
  have hL1 : (27253588275163 / 50000000000000 : ℝ) ≤ Real.log (1 + (23191428934597 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23191428934597 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6284432237749 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (85131201930089 / 231329058254681 : ℝ) ≤ (176313816516683 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (85131201930089 / 100000000000000 : ℝ) ≤ (176313816516683 / 250000000000000 : ℝ) := by
    have hw : (131329058254681 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (85131201930089 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (85131201930089 / 100000000000000 : ℝ) / (1 + (131329058254681 / 100000000000000 : ℝ)) = (85131201930089 / 231329058254681 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86554106072816461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 85131201930089 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 85131201930089 : ℝ) = (85131201930089 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (937500000000 / 10641400241261 : ℝ) ≤ (87872436582747 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86554106072816461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (85131201930089 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10641400241261 / 12500000000000 : ℝ)) ≤ (87872436582747 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_623 : ∀ t : ℝ, (23191428934597 / 32000000000000 : ℝ) < t → t ≤ (11610952826577 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-1773665471115637267154723 / 3125000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11610952826577 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_624
  have hV : (3444644588502601683274645290214709 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23191428934597 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_623 (Vfield_monotoneOn (show (23191428934597 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23191428934597 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_624 : (5515323179692966449357078271068713 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (11610952826577 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11610952826577 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (17037424120577 / 20000000000000 : ℝ) ≤ Real.sqrt (11610952826577 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11610952826577 / 16000000000000 : ℝ) ≤ (42593560301443 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (42593560301443 / 50000000000000 : ℝ) = (50000000000000 / 42593560301443 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17037424120577 / 20000000000000 : ℝ) = (1500000000000 / 17037424120577 : ℝ) := by norm_num
  have hL1 : (27281190665259 / 50000000000000 : ℝ) ≤ Real.log (1 + (11610952826577 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11610952826577 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6258368906461 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (42593560301443 / 115682656608519 : ℝ) ≤ (352789696577201 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (42593560301443 / 50000000000000 : ℝ) ≤ (352789696577201 / 500000000000000 : ℝ) := by
    have hw : (65682656608519 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (42593560301443 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (42593560301443 / 50000000000000 : ℝ) / (1 + (65682656608519 / 50000000000000 : ℝ)) = (42593560301443 / 115682656608519 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86521693364049461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 42593560301443 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 42593560301443 : ℝ) = (42593560301443 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 17037424120577 : ℝ) ≤ (87815051389043 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86521693364049461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (42593560301443 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17037424120577 / 20000000000000 : ℝ)) ≤ (87815051389043 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_624 : ∀ t : ℝ, (11610952826577 / 16000000000000 : ℝ) < t → t ≤ (23252382371711 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-5655598937658600532036831 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23252382371711 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_625
  have hV : (5515323179692966449357078271068713 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11610952826577 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_624 (Vfield_monotoneOn (show (11610952826577 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11610952826577 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_625 : (6899015608963532410224077230689989 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (23252382371711 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23252382371711 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (21310750648381 / 25000000000000 : ℝ) ≤ Real.sqrt (23252382371711 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23252382371711 / 32000000000000 : ℝ) ≤ (3409720103741 / 4000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3409720103741 / 4000000000000 : ℝ) = (4000000000000 / 3409720103741 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21310750648381 / 25000000000000 : ℝ) = (1875000000000 / 21310750648381 : ℝ) := by norm_num
  have hL1 : (27308777825923 / 50000000000000 : ℝ) ≤ Real.log (1 + (23252382371711 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23252382371711 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-15580848739589 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (3409720103741 / 9256062327052 : ℝ) ≤ (176475782224981 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3409720103741 / 4000000000000 : ℝ) ≤ (176475782224981 / 250000000000000 : ℝ) := by
    have hw : (1314015581763 / 1000000000000 : ℝ) ≤ Real.sqrt (1 + (3409720103741 / 4000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3409720103741 / 4000000000000 : ℝ) / (1 + (1314015581763 / 1000000000000 : ℝ)) = (3409720103741 / 9256062327052 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86489319789497261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (4000000000000 / 3409720103741 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (4000000000000 / 3409720103741 : ℝ) = (3409720103741 / 4000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 21310750648381 : ℝ) ≤ (10969722309461 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86489319789497261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3409720103741 / 4000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21310750648381 / 25000000000000 : ℝ)) ≤ (10969722309461 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_625 : ∀ t : ℝ, (23252382371711 / 32000000000000 : ℝ) < t → t ≤ (5820714772567 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-880573407409953334853947 / 1562500000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5820714772567 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_626
  have hV : (6899015608963532410224077230689989 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23252382371711 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_625 (Vfield_monotoneOn (show (23252382371711 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23252382371711 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_626 : (276154963435573595722334226605829 / 50000000000000000000000000000000 : ℝ) ≤ Vfield (5820714772567 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5820714772567 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (852988479741 / 1000000000000 : ℝ) ≤ Real.sqrt (5820714772567 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5820714772567 / 8000000000000 : ℝ) ≤ (85298847974101 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (85298847974101 / 100000000000000 : ℝ) = (100000000000000 / 85298847974101 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (852988479741 / 1000000000000 : ℝ) = (25000000000 / 284329493247 : ℝ) := by norm_num
  have hL1 : (213565232609 / 390625000000 : ℝ) ≤ Real.log (1 + (5820714772567 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5820714772567 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-7757929897117 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (85298847974101 / 231437793140743 : ℝ) ≤ (353113237076163 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (85298847974101 / 100000000000000 : ℝ) ≤ (353113237076163 / 500000000000000 : ℝ) := by
    have hw : (131437793140743 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (85298847974101 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (85298847974101 / 100000000000000 : ℝ) / (1 + (131437793140743 / 100000000000000 : ℝ)) = (85298847974101 / 231437793140743 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86456985264257061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 85298847974101 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 85298847974101 : ℝ) = (85298847974101 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (25000000000 / 284329493247 : ℝ) ≤ (87700617477011 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86456985264257061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (85298847974101 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (852988479741 / 1000000000000 : ℝ)) ≤ (87700617477011 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_626 : ∀ t : ℝ, (5820714772567 / 8000000000000 : ℝ) < t → t ≤ (932533432353 / 1280000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-28079613952443028362040271 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (932533432353 / 1280000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_627
  have hV : (276154963435573595722334226605829 / 50000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5820714772567 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_626 (Vfield_monotoneOn (show (5820714772567 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5820714772567 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_627 : (3454364705609007507450925551998371 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (932533432353 / 1280000000000 : ℝ) := by
  have hp : (0 : ℝ) < (932533432353 / 1280000000000 : ℝ) := by norm_num
  have hs1 : (10669332102059 / 12500000000000 : ℝ) ≤ Real.sqrt (932533432353 / 1280000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (932533432353 / 1280000000000 : ℝ) ≤ (85354656816473 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (85354656816473 / 100000000000000 : ℝ) = (100000000000000 / 85354656816473 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10669332102059 / 12500000000000 : ℝ) = (937500000000 / 10669332102059 : ℝ) := by norm_num
  have hL1 : (54727813052227 / 100000000000000 : ℝ) ≤ Real.log (1 + (932533432353 / 1280000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((932533432353 / 1280000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-30901910421 / 100000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (85354656816473 / 231474018118630 : ℝ) ≤ (176637357439469 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (85354656816473 / 100000000000000 : ℝ) ≤ (176637357439469 / 250000000000000 : ℝ) := by
    have hw : (13147401811863 / 10000000000000 : ℝ) ≤ Real.sqrt (1 + (85354656816473 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (85354656816473 / 100000000000000 : ℝ) / (1 + (13147401811863 / 10000000000000 : ℝ)) = (85354656816473 / 231474018118630 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86424689703702061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 85354656816473 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 85354656816473 : ℝ) = (85354656816473 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (937500000000 / 10669332102059 : ℝ) ≤ (87643568029003 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86424689703702061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (85354656816473 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10669332102059 / 12500000000000 : ℝ)) ≤ (87643568029003 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_627 : ∀ t : ℝ, (932533432353 / 1280000000000 : ℝ) < t → t ≤ (11671906263691 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-55963421261441869978447057 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11671906263691 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_628
  have hV : (3454364705609007507450925551998371 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (932533432353 / 1280000000000 : ℝ) := by norm_num
    refine le_trans V_pt_627 (Vfield_monotoneOn (show (932533432353 / 1280000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (932533432353 / 1280000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_628 : (3456790795378120532951207806011377 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (11671906263691 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11671906263691 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (10676303649033 / 12500000000000 : ℝ) ≤ Real.sqrt (11671906263691 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11671906263691 / 16000000000000 : ℝ) ≤ (17082085838453 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17082085838453 / 20000000000000 : ℝ) = (20000000000000 / 17082085838453 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10676303649033 / 12500000000000 : ℝ) = (312500000000 / 3558767883011 : ℝ) := by norm_num
  have hL1 : (54782896198297 / 100000000000000 : ℝ) ≤ Real.log (1 + (11671906263691 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11671906263691 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6154453907861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (85410429192265 / 231510233118213 : ℝ) ≤ (8835899957001 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17082085838453 / 20000000000000 : ℝ) ≤ (8835899957001 / 12500000000000 : ℝ) := by
    have hw : (131510233118213 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (17082085838453 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (17082085838453 / 20000000000000 : ℝ) / (1 + (131510233118213 / 100000000000000 : ℝ)) = (85410429192265 / 231510233118213 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86392433023481661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 17082085838453 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 17082085838453 : ℝ) = (17082085838453 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (312500000000 / 3558767883011 : ℝ) ≤ (2737082180291 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86392433023481661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17082085838453 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10676303649033 / 12500000000000 : ℝ)) ≤ (2737082180291 / 31250000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_628 : ∀ t : ℝ, (11671906263691 / 16000000000000 : ℝ) < t → t ≤ (23374289245939 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-11153829488451115452340579 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23374289245939 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_629
  have hV : (3456790795378120532951207806011377 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11671906263691 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_628 (Vfield_monotoneOn (show (11671906263691 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11671906263691 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_629 : (27673722521172600547853859571529723 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (23374289245939 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23374289245939 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (85466165172867 / 100000000000000 : ℝ) ≤ Real.sqrt (23374289245939 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23374289245939 / 32000000000000 : ℝ) ≤ (21366541293217 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (21366541293217 / 25000000000000 : ℝ) = (25000000000000 / 21366541293217 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (85466165172867 / 100000000000000 : ℝ) = (2500000000000 / 28488721724289 : ℝ) := by norm_num
  have hL1 : (54837949019541 / 100000000000000 : ℝ) ≤ Real.log (1 + (23374289245939 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23374289245939 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-15321398253807 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (85466165172868 / 231546438147735 : ℝ) ≤ (7071941753997 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (21366541293217 / 25000000000000 : ℝ) ≤ (7071941753997 / 10000000000000 : ℝ) := by
    have hw : (26309287629547 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (21366541293217 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (21366541293217 / 25000000000000 : ℝ) / (1 + (26309287629547 / 20000000000000 : ℝ)) = (85466165172868 / 231546438147735 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86360215139519661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 21366541293217 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 21366541293217 : ℝ) = (21366541293217 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 28488721724289 : ℝ) ≤ (5470612646077 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86360215139519661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (21366541293217 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (85466165172867 / 100000000000000 : ℝ)) ≤ (5470612646077 / 62500000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_629 : ∀ t : ℝ, (23374289245939 / 32000000000000 : ℝ) < t → t ≤ (1462797872781 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-1736759265283330033803939 / 3125000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1462797872781 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_630
  have hV : (27673722521172600547853859571529723 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23374289245939 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_629 (Vfield_monotoneOn (show (23374289245939 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23374289245939 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_630 : (27693106142400945422825798388453591 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1462797872781 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1462797872781 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (85521864829439 / 100000000000000 : ℝ) ≤ Real.sqrt (1462797872781 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1462797872781 / 2000000000000 : ℝ) ≤ (33406978449 / 39062500000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (33406978449 / 39062500000 : ℝ) = (39062500000 / 33406978449 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (85521864829439 / 100000000000000 : ℝ) = (7500000000000 / 85521864829439 : ℝ) := by norm_num
  have hL1 : (3430810721833 / 6250000000000 : ℝ) ≤ Real.log (1 + (1462797872781 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1462797872781 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-15256745445923 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (445426379320 / 1206159547997 : ℝ) ≤ (353757983557387 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (33406978449 / 39062500000 : ℝ) ≤ (353757983557387 / 500000000000000 : ℝ) := by
    have hw : (2055978643991 / 1562500000000 : ℝ) ≤ Real.sqrt (1 + (33406978449 / 39062500000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (33406978449 / 39062500000 : ℝ) / (1 + (2055978643991 / 1562500000000 : ℝ)) = (445426379320 / 1206159547997 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86328035968012261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (39062500000 / 33406978449 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (39062500000 / 33406978449 : ℝ) = (33406978449 / 39062500000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 85521864829439 : ℝ) ≤ (87473085373693 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86328035968012261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (33406978449 / 39062500000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (85521864829439 / 100000000000000 : ℝ)) ≤ (87473085373693 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_630 : ∀ t : ℝ, (1462797872781 / 2000000000000 : ℝ) < t → t ≤ (23435242683053 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-5538477473469993437093791 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23435242683053 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_631
  have hV : (27693106142400945422825798388453591 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1462797872781 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_630 (Vfield_monotoneOn (show (1462797872781 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1462797872781 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_631 : (27712477249726773358615045523500483 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (23435242683053 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23435242683053 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (85577528232907 / 100000000000000 : ℝ) ≤ Real.sqrt (23435242683053 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23435242683053 / 32000000000000 : ℝ) ≤ (21394382058227 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (21394382058227 / 25000000000000 : ℝ) = (25000000000000 / 21394382058227 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (85577528232907 / 100000000000000 : ℝ) = (7500000000000 / 85577528232907 : ℝ) := by norm_num
  have hL1 : (3434247738811 / 6250000000000 : ℝ) ≤ Real.log (1 + (23435242683053 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23435242683053 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-15192176129803 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (21394382058227 / 57904704582375 : ℝ) ≤ (88479671567577 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (21394382058227 / 25000000000000 : ℝ) ≤ (88479671567577 / 125000000000000 : ℝ) := by
    have hw : (263237636659 / 200000000000 : ℝ) ≤ Real.sqrt (1 + (21394382058227 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (21394382058227 / 25000000000000 : ℝ) / (1 + (263237636659 / 200000000000 : ℝ)) = (21394382058227 / 57904704582375 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86295895425428061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 21394382058227 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 21394382058227 : ℝ) = (21394382058227 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 85577528232907 : ℝ) ≤ (87416478521249 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86295895425428061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (21394382058227 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (85577528232907 / 100000000000000 : ℝ)) ≤ (87416478521249 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_631 : ∀ t : ℝ, (23435242683053 / 32000000000000 : ℝ) < t → t ≤ (2346571940161 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-3449656344611225544432909 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2346571940161 / 3200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_632
  have hV : (27712477249726773358615045523500483 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23435242683053 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_631 (Vfield_monotoneOn (show (23435242683053 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23435242683053 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_632 : (13865917933048207185728409256704927 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (2346571940161 / 3200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2346571940161 / 3200000000000 : ℝ) := by norm_num
  have hs1 : (42816577726983 / 50000000000000 : ℝ) ≤ Real.sqrt (2346571940161 / 3200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2346571940161 / 3200000000000 : ℝ) ≤ (85633155453967 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (85633155453967 / 100000000000000 : ℝ) = (100000000000000 / 85633155453967 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (42816577726983 / 50000000000000 : ℝ) = (1250000000000 / 14272192575661 : ℝ) := by norm_num
  have hL1 : (11000585173549 / 20000000000000 : ℝ) ≤ Real.log (1 + (2346571940161 / 3200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2346571940161 / 3200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3781922522521 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7784832313997 / 21059544863470 : ℝ) ≤ (354079196254911 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (85633155453967 / 100000000000000 : ℝ) ≤ (354079196254911 / 500000000000000 : ℝ) := by
    have hw : (13165499349817 / 10000000000000 : ℝ) ≤ Real.sqrt (1 + (85633155453967 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (85633155453967 / 100000000000000 : ℝ) / (1 + (13165499349817 / 10000000000000 : ℝ)) = (7784832313997 / 21059544863470 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86263793428507461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 85633155453967 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 85633155453967 : ℝ) = (85633155453967 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 14272192575661 : ℝ) ≤ (3494399256963 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86263793428507461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (85633155453967 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (42816577726983 / 50000000000000 : ℝ)) ≤ (3494399256963 / 40000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_632 : ∀ t : ℝ, (2346571940161 / 3200000000000 : ℝ) < t → t ≤ (23496196120167 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-55005406685067459169941857 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23496196120167 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_633
  have hV : (13865917933048207185728409256704927 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2346571940161 / 3200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_632 (Vfield_monotoneOn (show (2346571940161 / 3200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2346571940161 / 3200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_633 : (13875591007193564088258546860990029 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (23496196120167 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23496196120167 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (42844373281541 / 50000000000000 : ℝ) ≤ Real.sqrt (23496196120167 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23496196120167 / 32000000000000 : ℝ) ≤ (85688746563083 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (85688746563083 / 100000000000000 : ℝ) = (100000000000000 / 85688746563083 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (42844373281541 / 50000000000000 : ℝ) = (3750000000000 / 42844373281541 : ℝ) := by norm_num
  have hL1 : (27528928861421 / 50000000000000 : ℝ) ≤ Real.log (1 + (23496196120167 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23496196120167 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3765821778059 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (85688746563083 / 231691158729628 : ℝ) ≤ (354239513926153 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (85688746563083 / 100000000000000 : ℝ) ≤ (354239513926153 / 500000000000000 : ℝ) := by
    have hw : (32922789682407 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (85688746563083 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (85688746563083 / 100000000000000 : ℝ) / (1 + (32922789682407 / 25000000000000 : ℝ)) = (85688746563083 / 231691158729628 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86231729894259061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 85688746563083 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 85688746563083 : ℝ) = (85688746563083 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 42844373281541 : ℝ) ≤ (87303593727953 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86231729894259061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (85688746563083 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (42844373281541 / 50000000000000 : ℝ)) ≤ (87303593727953 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_633 : ∀ t : ℝ, (23496196120167 / 32000000000000 : ℝ) < t → t ≤ (5881668209681 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-13704357183265459057324369 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5881668209681 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_634
  have hV : (13875591007193564088258546860990029 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23496196120167 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_633 (Vfield_monotoneOn (show (23496196120167 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23496196120167 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_634 : (13885257858703911000964762346819943 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (5881668209681 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5881668209681 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (42872150815247 / 50000000000000 : ℝ) ≤ Real.sqrt (5881668209681 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5881668209681 / 8000000000000 : ℝ) ≤ (17148860326099 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17148860326099 / 20000000000000 : ℝ) = (20000000000000 / 17148860326099 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (42872150815247 / 50000000000000 : ℝ) = (3750000000000 / 42872150815247 : ℝ) := by norm_num
  have hL1 : (55112759419417 / 100000000000000 : ℝ) ≤ Real.log (1 + (5881668209681 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5881668209681 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-5999586793023 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (85744301630495 / 231727314032061 : ℝ) ≤ (177199819848823 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17148860326099 / 20000000000000 : ℝ) ≤ (177199819848823 / 250000000000000 : ℝ) := by
    have hw : (131727314032061 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (17148860326099 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (17148860326099 / 20000000000000 : ℝ) / (1 + (131727314032061 / 100000000000000 : ℝ)) = (85744301630495 / 231727314032061 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86199704739960461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 17148860326099 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 17148860326099 : ℝ) = (17148860326099 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 42872150815247 : ℝ) ≤ (4362365754013 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86199704739960461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17148860326099 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (42872150815247 / 50000000000000 : ℝ)) ≤ (4362365754013 / 50000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_634 : ∀ t : ℝ, (5881668209681 / 8000000000000 : ℝ) < t → t ≤ (23557149557281 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-13657628322813983055572573 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23557149557281 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_635
  have hV : (13885257858703911000964762346819943 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5881668209681 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_634 (Vfield_monotoneOn (show (5881668209681 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5881668209681 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_635 : (27789836997898269365342246260262797 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (23557149557281 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23557149557281 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (85799820726213 / 100000000000000 : ℝ) ≤ Real.sqrt (23557149557281 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23557149557281 / 32000000000000 : ℝ) ≤ (42899910363107 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (42899910363107 / 50000000000000 : ℝ) = (50000000000000 / 42899910363107 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (85799820726213 / 100000000000000 : ℝ) = (2500000000000 / 28599940242071 : ℝ) := by norm_num
  have hL1 : (6895953873821 / 12500000000000 : ℝ) ≤ Real.log (1 + (23557149557281 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23557149557281 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-29869458976339 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (85799820726214 / 231763459413641 : ℝ) ≤ (44319946747709 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (42899910363107 / 50000000000000 : ℝ) ≤ (44319946747709 / 62500000000000 : ℝ) := by
    have hw : (131763459413641 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (42899910363107 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (42899910363107 / 50000000000000 : ℝ) / (1 + (131763459413641 / 100000000000000 : ℝ)) = (85799820726214 / 231763459413641 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86167717883155261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 42899910363107 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 42899910363107 : ℝ) = (42899910363107 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 28599940242071 : ℝ) ≤ (43595572564983 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86167717883155261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (42899910363107 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (85799820726213 / 100000000000000 : ℝ)) ≤ (43595572564983 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_635 : ∀ t : ℝ, (23557149557281 / 32000000000000 : ℝ) < t → t ≤ (11793813137919 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-54444611978562598603514779 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11793813137919 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_636
  have hV : (27789836997898269365342246260262797 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23557149557281 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_635 (Vfield_monotoneOn (show (23557149557281 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23557149557281 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_636 : (13904572939264760752578605645683459 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (11793813137919 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11793813137919 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (42927651960011 / 50000000000000 : ℝ) ≤ Real.sqrt (11793813137919 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11793813137919 / 16000000000000 : ℝ) ≤ (85855303920023 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (85855303920023 / 100000000000000 : ℝ) = (100000000000000 / 85855303920023 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (42927651960011 / 50000000000000 : ℝ) = (3750000000000 / 42927651960011 : ℝ) := by norm_num
  have hL1 : (27611236234669 / 50000000000000 : ℝ) ≤ Real.log (1 + (11793813137919 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11793813137919 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-29741148834027 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (85855303920023 / 231799594882531 : ℝ) ≤ (88679829297293 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (85855303920023 / 100000000000000 : ℝ) ≤ (88679829297293 / 125000000000000 : ℝ) := by
    have hw : (131799594882531 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (85855303920023 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (85855303920023 / 100000000000000 : ℝ) / (1 + (131799594882531 / 100000000000000 : ℝ)) = (85855303920023 / 231799594882531 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86135769241655261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 85855303920023 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 85855303920023 : ℝ) = (85855303920023 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 42927651960011 : ℝ) ≤ (4356754176381 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86135769241655261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (85855303920023 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (42927651960011 / 50000000000000 : ℝ)) ≤ (4356754176381 / 50000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_636 : ∀ t : ℝ, (11793813137919 / 16000000000000 : ℝ) < t → t ≤ (4723620598879 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-27129840733429715068076001 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4723620598879 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_637
  have hV : (13904572939264760752578605645683459 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11793813137919 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_636 (Vfield_monotoneOn (show (11793813137919 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11793813137919 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_637 : (695711059547619007513628562431453 / 125000000000000000000000000000000 : ℝ) ≤ Vfield (4723620598879 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4723620598879 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (2147768782037 / 2500000000000 : ℝ) ≤ Real.sqrt (4723620598879 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4723620598879 / 6400000000000 : ℝ) ≤ (85910751281481 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (85910751281481 / 100000000000000 : ℝ) = (100000000000000 / 85910751281481 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (2147768782037 / 2500000000000 : ℝ) = (187500000000 / 2147768782037 : ℝ) := by norm_num
  have hL1 : (55277283888713 / 100000000000000 : ℝ) ≤ Real.log (1 + (4723620598879 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4723620598879 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-29613003115691 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (28636917093827 / 77278573482294 : ℝ) ≤ (44359858716221 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (85910751281481 / 100000000000000 : ℝ) ≤ (44359858716221 / 62500000000000 : ℝ) := by
    have hw : (65917860223441 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (85910751281481 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (85910751281481 / 100000000000000 : ℝ) / (1 + (65917860223441 / 50000000000000 : ℝ)) = (28636917093827 / 77278573482294 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86103858733536061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 85910751281481 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 85910751281481 : ℝ) = (85910751281481 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (187500000000 / 2147768782037 : ℝ) ≤ (87079129925341 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86103858733536061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (85910751281481 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (2147768782037 / 2500000000000 : ℝ)) ≤ (87079129925341 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_637 : ∀ t : ℝ, (4723620598879 / 6400000000000 : ℝ) < t → t ≤ (2956072464119 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-27037841368970286610493157 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2956072464119 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_638
  have hV : (695711059547619007513628562431453 / 125000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4723620598879 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_637 (Vfield_monotoneOn (show (4723620598879 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4723620598879 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_638 : (27847726530559842578217651853615787 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2956072464119 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2956072464119 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (85966162879923 / 100000000000000 : ℝ) ≤ Real.sqrt (2956072464119 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2956072464119 / 4000000000000 : ℝ) ≤ (21491540719981 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (21491540719981 / 25000000000000 : ℝ) = (25000000000000 / 21491540719981 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (85966162879923 / 100000000000000 : ℝ) = (2500000000000 / 28655387626641 : ℝ) := by norm_num
  have hL1 : (55332065281629 / 100000000000000 : ℝ) ≤ Real.log (1 + (2956072464119 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2956072464119 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-5897004280093 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (1177618669588 / 3176326522121 : ℝ) ≤ (88759558002943 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (21491540719981 / 25000000000000 : ℝ) ≤ (88759558002943 / 125000000000000 : ℝ) := by
    have hw : (131871836114833 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (21491540719981 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (21491540719981 / 25000000000000 : ℝ) / (1 + (131871836114833 / 100000000000000 : ℝ)) = (1177618669588 / 3176326522121 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86071986277135261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 21491540719981 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 21491540719981 : ℝ) = (21491540719981 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 28655387626641 : ℝ) ≤ (8702328397681 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86071986277135261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (21491540719981 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (85966162879923 / 100000000000000 : ℝ)) ≤ (8702328397681 / 100000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_638 : ∀ t : ℝ, (2956072464119 / 4000000000000 : ℝ) < t → t ≤ (23679056431509 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-53892580461011199411017269 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23679056431509 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_639
  have hV : (27847726530559842578217651853615787 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2956072464119 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_638 (Vfield_monotoneOn (show (2956072464119 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2956072464119 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_639 : (27866998346962327017683454469535509 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (23679056431509 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23679056431509 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (86021538784461 / 100000000000000 : ℝ) ≤ Real.sqrt (23679056431509 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23679056431509 / 32000000000000 : ℝ) ≤ (43010769392231 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (43010769392231 / 50000000000000 : ℝ) = (50000000000000 / 43010769392231 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (86021538784461 / 100000000000000 : ℝ) = (2500000000000 / 28673846261487 : ℝ) := by norm_num
  have hL1 : (11077363336193 / 20000000000000 : ℝ) ≤ Real.log (1 + (23679056431509 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23679056431509 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-29357203269099 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (43010769392231 / 115953970947257 : ℝ) ≤ (355197404442169 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (43010769392231 / 50000000000000 : ℝ) ≤ (355197404442169 / 500000000000000 : ℝ) := by
    have hw : (65953970947257 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (43010769392231 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (43010769392231 / 50000000000000 : ℝ) / (1 + (65953970947257 / 50000000000000 : ℝ)) = (43010769392231 / 115953970947257 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86040151791055861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 43010769392231 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 43010769392231 : ℝ) = (43010769392231 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 28673846261487 : ℝ) ≤ (4348377266863 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86040151791055861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (43010769392231 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (86021538784461 / 100000000000000 : ℝ)) ≤ (4348377266863 / 50000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_639 : ∀ t : ℝ, (23679056431509 / 32000000000000 : ℝ) < t → t ≤ (11854766575033 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-53710342503159047732044301 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11854766575033 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_640
  have hV : (27866998346962327017683454469535509 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23679056431509 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_639 (Vfield_monotoneOn (show (23679056431509 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23679056431509 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
