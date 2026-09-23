import Apery.Table2.U00
import Apery.Table2.U01

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_0 : (1472030248359035494138213513066003 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (7174131 / 200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7174131 / 200000000000 : ℝ) := by norm_num
  have hs1 : (299460577539 / 50000000000000 : ℝ) ≤ Real.sqrt (7174131 / 200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7174131 / 200000000000 : ℝ) ≤ (598921155079 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (598921155079 / 100000000000000 : ℝ) = (100000000000000 / 598921155079 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (299460577539 / 50000000000000 : ℝ) = (1250000000000 / 99820192513 : ℝ) := by norm_num
  have hL1 : (1793500583 / 50000000000000 : ℝ) ≤ Real.log (1 + (7174131 / 200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7174131 / 200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-20696710282183 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (598921155079 / 100000000000000 : ℝ) ≤ (2994569970009 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (156480718685487861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 598921155079 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 598921155079 : ℝ) = (598921155079 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (15937410569823 / 200000000000000 : ℝ) ≤ Real.arctan (99820192513 / 1250000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (1250000000000 / 99820192513 : ℝ) ≤ (298221854789156323847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (1250000000000 / 99820192513 : ℝ) = (99820192513 / 1250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (156480718685487861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (598921155079 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (299460577539 / 50000000000000 : ℝ)) ≤ (298221854789156323847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_0 : ∀ t : ℝ, (0 : ℝ) < t → t ≤ (7174131 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-273856567626306362956419919 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (0 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_0
  have hV : (1472030248359035494138213513066003 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (7174131 / 200000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_0 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (7174131 / 200000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (7174131 / 200000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_1 : (29158778111315329671371111437377 / 25000000000000000000000000000000 : ℝ) ≤ Vfield (21522393 / 400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (21522393 / 400000000000 : ℝ) := by norm_num
  have hs1 : (733525613049 / 100000000000000 : ℝ) ≤ Real.sqrt (21522393 / 400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (21522393 / 400000000000 : ℝ) ≤ (14670512261 / 2000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (14670512261 / 2000000000000 : ℝ) = (2000000000000 / 14670512261 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (733525613049 / 100000000000000 : ℝ) = (2500000000000 / 244508537683 : ℝ) := by norm_num
  have hL1 : (5380453501 / 100000000000000 : ℝ) ≤ Real.log (1 + (21522393 / 400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((21522393 / 400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-517101428061623 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (14670512261 / 2000000000000 : ℝ) ≤ (7335124574527 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (156346120222036961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (2000000000000 / 14670512261 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (2000000000000 / 14670512261 : ℝ) = (14670512261 / 2000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (19498669253367 / 200000000000000 : ℝ) ≤ Real.arctan (244508537683 / 2500000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (2500000000000 / 244508537683 : ℝ) ≤ (294660596105612323847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (2500000000000 / 244508537683 : ℝ) = (244508537683 / 2500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (156346120222036961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (14670512261 / 2000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (733525613049 / 100000000000000 : ℝ)) ≤ (294660596105612323847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_1 : ∀ t : ℝ, (7174131 / 200000000000 : ℝ) < t → t ≤ (21522393 / 400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-17149477848555761531110173 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (7174131 / 200000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_1
  have hV : (29158778111315329671371111437377 / 25000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (21522393 / 400000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_1 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (21522393 / 400000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (21522393 / 400000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_2 : (90395920065239108686687167863833 / 78125000000000000000000000000000 : ℝ) ≤ Vfield (7174131 / 100000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7174131 / 100000000000 : ℝ) := by norm_num
  have hs1 : (847002420303 / 100000000000000 : ℝ) ≤ Real.sqrt (7174131 / 100000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7174131 / 100000000000 : ℝ) ≤ (52937651269 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (52937651269 / 6250000000000 : ℝ) = (6250000000000 / 52937651269 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (847002420303 / 100000000000000 : ℝ) = (2500000000000 / 282334140101 : ℝ) := by norm_num
  have hL1 : (7173873671 / 100000000000000 : ℝ) ≤ Real.log (1 + (7174131 / 100000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7174131 / 100000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-258393048277241 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (52937651269 / 6250000000000 : ℝ) ≤ (2117455415387 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (156232650513334861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 52937651269 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 52937651269 : ℝ) = (52937651269 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (112457177946151 / 1000000000000000 : ℝ) ≤ Real.arctan (282334140101 / 2500000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (2500000000000 / 282334140101 : ℝ) ≤ (291667829769749123847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (2500000000000 / 282334140101 : ℝ) = (282334140101 / 2500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (156232650513334861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (52937651269 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (847002420303 / 100000000000000 : ℝ)) ≤ (291667829769749123847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_2 : ∀ t : ℝ, (21522393 / 400000000000 : ℝ) < t → t ≤ (7174131 / 100000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-274692134568098847503067623 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (21522393 / 400000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_2
  have hV : (90395920065239108686687167863833 / 78125000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (7174131 / 100000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_2 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (7174131 / 100000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (7174131 / 100000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_3 : (72246111017072387417236721077567 / 62500000000000000000000000000000 : ℝ) ≤ Vfield (14825913 / 200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (14825913 / 200000000000 : ℝ) := by norm_num
  have hs1 : (860985278619 / 100000000000000 : ℝ) ≤ Real.sqrt (14825913 / 200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (14825913 / 200000000000 : ℝ) ≤ (43049263931 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (43049263931 / 5000000000000 : ℝ) = (5000000000000 / 43049263931 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (860985278619 / 100000000000000 : ℝ) = (2500000000000 / 286995092873 : ℝ) := by norm_num
  have hL1 : (7412681753 / 100000000000000 : ℝ) ≤ Real.log (1 + (14825913 / 200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((14825913 / 200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-64593022770223 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (43049263931 / 5000000000000 : ℝ) ≤ (8609640047449 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (156218668674744761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 43049263931 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 43049263931 : ℝ) = (43049263931 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (11429769544643 / 100000000000000 : ℝ) ≤ Real.arctan (286995092873 / 2500000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (2500000000000 / 286995092873 : ℝ) ≤ (291299726269693323847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (2500000000000 / 286995092873 : ℝ) = (286995092873 / 2500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (156218668674744761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (43049263931 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (860985278619 / 100000000000000 : ℝ)) ≤ (291299726269693323847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_3 : ∀ t : ℝ, (7174131 / 100000000000 : ℝ) < t → t ≤ (14825913 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-68760456943802754478209389 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (7174131 / 100000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_3
  have hV : (72246111017072387417236721077567 / 62500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (14825913 / 200000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_3 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (14825913 / 200000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (14825913 / 200000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_4 : (360577409943481150931190080759661 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (78667711 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (78667711 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (886948200291 / 100000000000000 : ℝ) ≤ Real.sqrt (78667711 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (78667711 / 1000000000000 : ℝ) ≤ (221737050073 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (221737050073 / 25000000000000 : ℝ) = (25000000000000 / 221737050073 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (886948200291 / 100000000000000 : ℝ) = (2500000000000 / 295649400097 : ℝ) := by norm_num
  have hL1 : (1573292337 / 20000000000000 : ℝ) ≤ Real.log (1 + (78667711 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((78667711 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-516664585092227 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (221737050073 / 25000000000000 : ℝ) ≤ (4434624716641 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (156192707736161461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 221737050073 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 221737050073 : ℝ) = (221737050073 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (117713038222529 / 1000000000000000 : ℝ) ≤ Real.arctan (295649400097 / 2500000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (2500000000000 / 295649400097 : ℝ) ≤ (290616657714473523847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (2500000000000 / 295649400097 : ℝ) = (295649400097 / 2500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (156192707736161461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (221737050073 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (886948200291 / 100000000000000 : ℝ)) ≤ (290616657714473523847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_4 : ∀ t : ℝ, (14825913 / 200000000000 : ℝ) < t → t ≤ (78667711 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-275101278173292200580074647 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (14825913 / 200000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_4
  have hV : (360577409943481150931190080759661 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (78667711 / 1000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_4 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (78667711 / 1000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (78667711 / 1000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_5 : (1438368090309163448107715256240077 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (85815639 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (85815639 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (23159182709 / 2500000000000 : ℝ) ≤ Real.sqrt (85815639 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (85815639 / 1000000000000 : ℝ) ≤ (926367308361 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (926367308361 / 100000000000000 : ℝ) = (100000000000000 / 926367308361 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (23159182709 / 2500000000000 : ℝ) = (187500000000 / 23159182709 : ℝ) := by norm_num
  have hL1 : (1072649463 / 12500000000000 : ℝ) ≤ Real.log (1 + (85815639 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((85815639 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-516539341947791 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (926367308361 / 100000000000000 : ℝ) ≤ (1157926013489 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (156153291868698461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 926367308361 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 926367308361 : ℝ) = (926367308361 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (122893205938343 / 1000000000000000 : ℝ) ≤ Real.arctan (23159182709 / 187500000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (187500000000 / 23159182709 : ℝ) ≤ (289580624171310723847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (187500000000 / 23159182709 : ℝ) = (23159182709 / 187500000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (156153291868698461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (926367308361 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (23159182709 / 2500000000000 : ℝ)) ≤ (289580624171310723847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_5 : ∀ t : ℝ, (78667711 / 1000000000000 : ℝ) < t → t ≤ (85815639 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-68802371773305424971763039 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (78667711 / 1000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_5
  have hV : (1438368090309163448107715256240077 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (85815639 / 1000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_5 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (85815639 / 1000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (85815639 / 1000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_6 : (1432898417128663671932024523105603 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (19269871 / 200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19269871 / 200000000000 : ℝ) := by norm_num
  have hs1 : (490788536439 / 50000000000000 : ℝ) ≤ Real.sqrt (19269871 / 200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19269871 / 200000000000 : ℝ) ≤ (981577072879 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (981577072879 / 100000000000000 : ℝ) = (100000000000000 / 981577072879 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (490788536439 / 50000000000000 : ℝ) = (1250000000000 / 163596178813 : ℝ) := by norm_num
  have hL1 : (9634471369 / 100000000000000 : ℝ) ≤ Real.log (1 + (19269871 / 200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19269871 / 200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-516355059810741 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (981577072879 / 100000000000000 : ℝ) ≤ (9815455499287 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (156098087129560961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 981577072879 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 981577072879 : ℝ) = (981577072879 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (130137276180897 / 1000000000000000 : ℝ) ≤ Real.arctan (163596178813 / 1250000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (1250000000000 / 163596178813 : ℝ) ≤ (288131810122799923847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (1250000000000 / 163596178813 : ℝ) = (163596178813 / 1250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (156098087129560961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (981577072879 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (490788536439 / 50000000000000 : ℝ)) ≤ (288131810122799923847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_6 : ∀ t : ℝ, (85815639 / 1000000000000 : ℝ) < t → t ≤ (19269871 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-27537256492583409517524091 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (85815639 / 1000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_6
  have hV : (1432898417128663671932024523105603 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (19269871 / 200000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_6 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (19269871 / 200000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (19269871 / 200000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_7 : (1425614991378332271484520948977167 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (55761057 / 500000000000 : ℝ) := by
  have hp : (0 : ℝ) < (55761057 / 500000000000 : ℝ) := by norm_num
  have hs1 : (105604031173 / 10000000000000 : ℝ) ≤ Real.sqrt (55761057 / 500000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (55761057 / 500000000000 : ℝ) ≤ (1056040311731 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1056040311731 / 100000000000000 : ℝ) = (100000000000000 / 1056040311731 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (105604031173 / 10000000000000 : ℝ) = (750000000000 / 105604031173 : ℝ) := by norm_num
  have hL1 : (11151589587 / 100000000000000 : ℝ) ≤ Real.log (1 + (55761057 / 500000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((55761057 / 500000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-516090215368911 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1056040311731 / 100000000000000 : ℝ) ≤ (42240042283 / 4000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (156023631622414661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 1056040311731 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 1056040311731 : ℝ) = (1056040311731 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (139885746971811 / 1000000000000000 : ℝ) ≤ Real.arctan (105604031173 / 750000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (750000000000 / 105604031173 : ℝ) ≤ (286182115964617123847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (750000000000 / 105604031173 : ℝ) = (105604031173 / 750000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (156023631622414661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1056040311731 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (105604031173 / 10000000000000 : ℝ)) ≤ (286182115964617123847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_7 : ∀ t : ℝ, (19269871 / 200000000000 : ℝ) < t → t ≤ (55761057 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-137799142219212910191367693 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (19269871 / 200000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_7
  have hV : (1425614991378332271484520948977167 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (55761057 / 500000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_7 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (55761057 / 500000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (55761057 / 500000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_8 : (1416124409220200317846210776568841 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (33336783 / 250000000000 : ℝ) := by
  have hp : (0 : ℝ) < (33336783 / 250000000000 : ℝ) := by norm_num
  have hs1 : (288690071703 / 25000000000000 : ℝ) ≤ Real.sqrt (33336783 / 250000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (33336783 / 250000000000 : ℝ) ≤ (1154760286813 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1154760286813 / 100000000000000 : ℝ) = (100000000000000 / 1154760286813 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (288690071703 / 25000000000000 : ℝ) = (625000000000 / 96230023901 : ℝ) := by norm_num
  have hL1 : (6666912103 / 50000000000000 : ℝ) ≤ Real.log (1 + (33336783 / 250000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((33336783 / 250000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-515710479962459 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1154760286813 / 100000000000000 : ℝ) ≤ (2309417925857 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (155924923716561161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 1154760286813 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 1154760286813 : ℝ) = (1154760286813 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (30553678494567 / 200000000000000 : ℝ) ≤ Real.arctan (96230023901 / 625000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (625000000000 / 96230023901 : ℝ) ≤ (283605586864412323847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (625000000000 / 96230023901 : ℝ) = (96230023901 / 625000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (155924923716561161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1154760286813 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (288690071703 / 25000000000000 : ℝ)) ≤ (283605586864412323847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_8 : ∀ t : ℝ, (55761057 / 500000000000 : ℝ) < t → t ≤ (33336783 / 250000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-34487275926713772248195891 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (55761057 / 500000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_8
  have hV : (1416124409220200317846210776568841 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (33336783 / 250000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_8 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (33336783 / 250000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (33336783 / 250000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_9 : (350975003176475718788377841988277 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (82548843 / 500000000000 : ℝ) := by
  have hp : (0 : ℝ) < (82548843 / 500000000000 : ℝ) := by norm_num
  have hs1 : (1284903443843 / 100000000000000 : ℝ) ≤ Real.sqrt (82548843 / 500000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (82548843 / 500000000000 : ℝ) ≤ (321225860961 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (321225860961 / 25000000000000 : ℝ) = (25000000000000 / 321225860961 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1284903443843 / 100000000000000 : ℝ) = (7500000000000 / 1284903443843 : ℝ) := by norm_num
  have hL1 : (16508405887 / 100000000000000 : ℝ) ≤ Real.log (1 + (82548843 / 500000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((82548843 / 500000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-25758030569787 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (321225860961 / 25000000000000 : ℝ) ≤ (6424163696597 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (155794799940170261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 321225860961 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 321225860961 : ℝ) = (321225860961 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (169673246300091 / 1000000000000000 : ℝ) ≤ Real.arctan (1284903443843 / 7500000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7500000000000 / 1284903443843 : ℝ) ≤ (280224616098961123847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (7500000000000 / 1284903443843 : ℝ) = (1284903443843 / 7500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (155794799940170261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (321225860961 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1284903443843 / 100000000000000 : ℝ)) ≤ (280224616098961123847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_9 : ∀ t : ℝ, (33336783 / 250000000000 : ℝ) < t → t ≤ (82548843 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-69072398821225269741462211 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (33336783 / 250000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_9
  have hV : (350975003176475718788377841988277 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (82548843 / 500000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_9 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (82548843 / 500000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (82548843 / 500000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_10 : (1388257534222632955667025154398403 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (53051547 / 250000000000 : ℝ) := by
  have hp : (0 : ℝ) < (53051547 / 250000000000 : ℝ) := by norm_num
  have hs1 : (728364929139 / 50000000000000 : ℝ) ≤ Real.sqrt (53051547 / 250000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (53051547 / 250000000000 : ℝ) ≤ (1456729858279 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1456729858279 / 100000000000000 : ℝ) = (100000000000000 / 1456729858279 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (728364929139 / 50000000000000 : ℝ) = (1250000000000 / 242788309713 : ℝ) := by norm_num
  have hL1 : (4243673509 / 20000000000000 : ℝ) ≤ Real.log (1 + (53051547 / 250000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((53051547 / 250000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-514350298699437 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1456729858279 / 100000000000000 : ℝ) ≤ (7283134145167 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (155623005850456261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 1456729858279 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 1456729858279 : ℝ) = (1456729858279 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (95921000596157 / 500000000000000 : ℝ) ≤ Real.arctan (242788309713 / 1250000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (1250000000000 / 242788309713 : ℝ) ≤ (275790865120516523847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (1250000000000 / 242788309713 : ℝ) = (242788309713 / 1250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (155623005850456261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1456729858279 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (728364929139 / 50000000000000 : ℝ)) ≤ (275790865120516523847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_10 : ∀ t : ℝ, (82548843 / 500000000000 : ℝ) < t → t ≤ (53051547 / 250000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-55358731180530840136613439 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (82548843 / 500000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_10
  have hV : (1388257534222632955667025154398403 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (53051547 / 250000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_10 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (53051547 / 250000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (53051547 / 250000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_11 : (1377818299180005030213934134854853 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (496117379 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (496117379 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (196873487891 / 12500000000000 : ℝ) ≤ Real.sqrt (496117379 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (496117379 / 2000000000000 : ℝ) ≤ (1574987903129 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1574987903129 / 100000000000000 : ℝ) = (100000000000000 / 1574987903129 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (196873487891 / 12500000000000 : ℝ) = (937500000000 / 196873487891 : ℝ) := by norm_num
  have hL1 : (24802792803 / 100000000000000 : ℝ) ≤ Real.log (1 + (496117379 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((496117379 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-64217246341351 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1574987903129 / 100000000000000 : ℝ) ≤ (15748576926967 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (155504774986792961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 1574987903129 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 1574987903129 : ℝ) = (1574987903129 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (41398129885667 / 200000000000000 : ℝ) ≤ Real.arctan (196873487891 / 937500000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (937500000000 / 196873487891 : ℝ) ≤ (272761135473312323847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (937500000000 / 196873487891 : ℝ) = (196873487891 / 937500000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (155504774986792961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1574987903129 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (196873487891 / 12500000000000 : ℝ)) ≤ (272761135473312323847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_11 : ∀ t : ℝ, (53051547 / 250000000000 : ℝ) < t → t ≤ (496117379 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-277439851503270994348823573 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (53051547 / 250000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_11
  have hV : (1377818299180005030213934134854853 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (496117379 / 2000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_11 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (496117379 / 2000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (496117379 / 2000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_12 : (1368347238643499023177069837193271 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (283911191 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (283911191 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (842483220901 / 50000000000000 : ℝ) ≤ Real.sqrt (283911191 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (283911191 / 1000000000000 : ℝ) ≤ (1684966441803 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1684966441803 / 100000000000000 : ℝ) = (100000000000000 / 1684966441803 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (842483220901 / 50000000000000 : ℝ) = (3750000000000 / 842483220901 : ℝ) := by norm_num
  have hL1 : (1774193099 / 6250000000000 : ℝ) ≤ Real.log (1 + (283911191 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((283911191 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-256564684704929 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1684966441803 / 100000000000000 : ℝ) ≤ (8424035043423 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (155394825670805061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 1684966441803 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 1684966441803 : ℝ) = (1684966441803 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (110496444403721 / 500000000000000 : ℝ) ≤ Real.arctan (842483220901 / 3750000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (3750000000000 / 842483220901 : ℝ) ≤ (269960687597490923847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (3750000000000 / 842483220901 : ℝ) = (842483220901 / 3750000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (155394825670805061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1684966441803 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (842483220901 / 50000000000000 : ℝ)) ≤ (269960687597490923847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_12 : ∀ t : ℝ, (496117379 / 2000000000000 : ℝ) < t → t ≤ (283911191 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-277765956494863571604953411 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (496117379 / 2000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_12
  have hV : (1368347238643499023177069837193271 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (283911191 / 1000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_12 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (283911191 / 1000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (283911191 / 1000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_13 : (1355034442079061053294713876205181 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (170058951 / 500000000000 : ℝ) := by
  have hp : (0 : ℝ) < (170058951 / 500000000000 : ℝ) := by norm_num
  have hs1 : (28816071413 / 1562500000000 : ℝ) ≤ Real.sqrt (170058951 / 500000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (170058951 / 500000000000 : ℝ) ≤ (1844228570433 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1844228570433 / 100000000000000 : ℝ) = (100000000000000 / 1844228570433 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (28816071413 / 1562500000000 : ℝ) = (117187500000 / 28816071413 : ℝ) := by norm_num
  have hL1 : (34006007501 / 100000000000000 : ℝ) ≤ Real.log (1 + (170058951 / 500000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((170058951 / 500000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-512182645591517 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1844228570433 / 100000000000000 : ℝ) ≤ (18440195280401 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (155235613151449561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 1844228570433 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 1844228570433 : ℝ) = (1844228570433 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (9644537528931 / 40000000000000 : ℝ) ≤ Real.arctan (28816071413 / 117187500000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (117187500000 / 28816071413 : ℝ) ≤ (265936577714324323847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (117187500000 / 28816071413 : ℝ) = (28816071413 / 117187500000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (155235613151449561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1844228570433 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (28816071413 / 1562500000000 : ℝ)) ≤ (265936577714324323847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_13 : ∀ t : ℝ, (283911191 / 1000000000000 : ℝ) < t → t ≤ (170058951 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-278262784666310605595581841 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (283911191 / 1000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_13
  have hV : (1355034442079061053294713876205181 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (170058951 / 500000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_13 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (170058951 / 500000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (170058951 / 500000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_14 : (671600214068082065350060043298101 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (396324613 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (396324613 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (398158065597 / 20000000000000 : ℝ) ≤ Real.sqrt (396324613 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (396324613 / 1000000000000 : ℝ) ≤ (995395163993 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (995395163993 / 50000000000000 : ℝ) = (50000000000000 / 995395163993 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (398158065597 / 20000000000000 : ℝ) = (500000000000 / 132719355199 : ℝ) := by norm_num
  have hL1 : (19812304857 / 50000000000000 : ℝ) ≤ Real.log (1 + (396324613 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((396324613 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-511244800640401 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (995395163993 / 50000000000000 : ℝ) ≤ (19905273907729 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (155089105288716761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 995395163993 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 995395163993 : ℝ) = (995395163993 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (259455609460027 / 1000000000000000 : ℝ) ≤ Real.arctan (132719355199 / 500000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (500000000000 / 132719355199 : ℝ) ≤ (262268143466973923847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (500000000000 / 132719355199 : ℝ) = (132719355199 / 500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (155089105288716761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (995395163993 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (398158065597 / 20000000000000 : ℝ)) ≤ (262268143466973923847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_14 : ∀ t : ℝ, (170058951 / 500000000000 : ℝ) < t → t ≤ (396324613 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-139332619353331173773255643 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (170058951 / 500000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_14
  have hV : (671600214068082065350060043298101 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (396324613 / 1000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_14 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (396324613 / 1000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (396324613 / 1000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_15 : (265286871045236928998921758432997 / 250000000000000000000000000000000 : ℝ) ≤ Vfield (974522519 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (974522519 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (551849877401 / 25000000000000 : ℝ) ≤ Real.sqrt (974522519 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (974522519 / 2000000000000 : ℝ) ≤ (441479901921 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (441479901921 / 20000000000000 : ℝ) = (20000000000000 / 441479901921 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (551849877401 / 25000000000000 : ℝ) = (1875000000000 / 551849877401 : ℝ) := by norm_num
  have hL1 : (12178564657 / 25000000000000 : ℝ) ≤ Real.log (1 + (974522519 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((974522519 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-254872924030743 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (441479901921 / 20000000000000 : ℝ) ≤ (2758801359539 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (154872591591858461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 441479901921 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 441479901921 : ℝ) = (441479901921 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (286237613378509 / 1000000000000000 : ℝ) ≤ Real.arctan (551849877401 / 1875000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (1875000000000 / 551849877401 : ℝ) ≤ (256911742683277523847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (1875000000000 / 551849877401 : ℝ) = (551849877401 / 1875000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (154872591591858461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (441479901921 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (551849877401 / 25000000000000 : ℝ)) ≤ (256911742683277523847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_15 : ∀ t : ℝ, (396324613 / 1000000000000 : ℝ) < t → t ≤ (974522519 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-279305183338956206823557363 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (396324613 / 1000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_15
  have hV : (265286871045236928998921758432997 / 250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (974522519 / 2000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_15 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (974522519 / 2000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (974522519 / 2000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_16 : (327978365792685361268200427181649 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (289098953 / 500000000000 : ℝ) := by
  have hp : (0 : ℝ) < (289098953 / 500000000000 : ℝ) := by norm_num
  have hs1 : (2404574611027 / 100000000000000 : ℝ) ≤ Real.sqrt (289098953 / 500000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (289098953 / 500000000000 : ℝ) ≤ (601143652757 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (601143652757 / 25000000000000 : ℝ) = (25000000000000 / 601143652757 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (2404574611027 / 100000000000000 : ℝ) = (7500000000000 / 2404574611027 : ℝ) := by norm_num
  have hL1 : (57803081399 / 100000000000000 : ℝ) ≤ Real.log (1 + (289098953 / 500000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((289098953 / 500000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-508269032653581 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (601143652757 / 25000000000000 : ℝ) ≤ (24041113317361 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (154675521347753561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 601143652757 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 601143652757 : ℝ) = (601143652757 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (31025613766709 / 100000000000000 : ℝ) ≤ Real.arctan (2404574611027 / 7500000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7500000000000 / 2404574611027 : ℝ) ≤ (252108037825561323847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (7500000000000 / 2404574611027 : ℝ) = (2404574611027 / 7500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (154675521347753561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (601143652757 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (2404574611027 / 100000000000000 : ℝ)) ≤ (252108037825561323847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_16 : ∀ t : ℝ, (974522519 / 2000000000000 : ℝ) < t → t ≤ (289098953 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-3497376374357506927056083 / 1250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (974522519 / 2000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_16
  have hV : (327978365792685361268200427181649 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (289098953 / 500000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_16 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (289098953 / 500000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (289098953 / 500000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_17 : (1291336280886928613274291162083833 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (729961631 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (729961631 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (675445052817 / 25000000000000 : ℝ) ≤ Real.sqrt (729961631 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (729961631 / 1000000000000 : ℝ) ≤ (2701780211269 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2701780211269 / 100000000000000 : ℝ) = (100000000000000 / 2701780211269 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (675445052817 / 25000000000000 : ℝ) = (625000000000 / 225148350939 : ℝ) := by norm_num
  have hL1 : (36484766929 / 50000000000000 : ℝ) ≤ Real.log (1 + (729961631 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((729961631 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-126462985247189 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2701780211269 / 100000000000000 : ℝ) ≤ (13505615502073 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (154378509579075061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 2701780211269 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 2701780211269 : ℝ) = (2701780211269 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (172882846746561 / 500000000000000 : ℝ) ≤ Real.arctan (225148350939 / 625000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (625000000000 / 225148350939 : ℝ) ≤ (245006126660354923847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (625000000000 / 225148350939 : ℝ) = (225148350939 / 625000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (154378509579075061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2701780211269 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (675445052817 / 25000000000000 : ℝ)) ≤ (245006126660354923847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_17 : ∀ t : ℝ, (289098953 / 500000000000 : ℝ) < t → t ≤ (729961631 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-140299247846894980680558127 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (289098953 / 500000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_17
  have hV : (1291336280886928613274291162083833 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (729961631 / 1000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_17 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (729961631 / 1000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (729961631 / 1000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_18 : (1282375152218983899213056722992669 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (1611686987 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1611686987 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (354842283077 / 12500000000000 : ℝ) ≤ Real.sqrt (1611686987 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1611686987 / 2000000000000 : ℝ) ≤ (2838738264617 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2838738264617 / 100000000000000 : ℝ) = (100000000000000 / 2838738264617 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (354842283077 / 12500000000000 : ℝ) = (937500000000 / 354842283077 : ℝ) := by norm_num
  have hL1 : (20137974399 / 25000000000000 : ℝ) ≤ Real.log (1 + (1611686987 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1611686987 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-504664956630783 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2838738264617 / 100000000000000 : ℝ) ≤ (3547470133547 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (154241656572652061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 2838738264617 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 2838738264617 : ℝ) = (2838738264617 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (45229282296197 / 125000000000000 : ℝ) ≤ Real.arctan (354842283077 / 937500000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (937500000000 / 354842283077 : ℝ) ≤ (241792413685064123847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (937500000000 / 354842283077 : ℝ) = (354842283077 / 937500000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (154241656572652061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2838738264617 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (354842283077 / 12500000000000 : ℝ)) ≤ (241792413685064123847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_18 : ∀ t : ℝ, (729961631 / 1000000000000 : ℝ) < t → t ≤ (1611686987 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-14058144779552195767876503 / 5000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (729961631 / 1000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_18
  have hV : (1282375152218983899213056722992669 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (1611686987 / 2000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_18 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (1611686987 / 2000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (1611686987 / 2000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_19 : (1274128395526980931703998560016649 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (220431339 / 250000000000 : ℝ) := by
  have hp : (0 : ℝ) < (220431339 / 250000000000 : ℝ) := by norm_num
  have hs1 : (742346514439 / 25000000000000 : ℝ) ≤ Real.sqrt (220431339 / 250000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (220431339 / 250000000000 : ℝ) ≤ (2969386057757 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2969386057757 / 100000000000000 : ℝ) = (100000000000000 / 2969386057757 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (742346514439 / 25000000000000 : ℝ) = (1875000000000 / 742346514439 : ℝ) := by norm_num
  have hL1 : (44066843227 / 50000000000000 : ℝ) ≤ Real.log (1 + (220431339 / 250000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((220431339 / 250000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-62936487059367 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2969386057757 / 100000000000000 : ℝ) ≤ (5937027583021 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (154111118887979161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 2969386057757 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 2969386057757 : ℝ) = (2969386057757 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (376982587875129 / 1000000000000000 : ℝ) ≤ Real.arctan (742346514439 / 1875000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (1875000000000 / 742346514439 : ℝ) ≤ (238762747783953523847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (1875000000000 / 742346514439 : ℝ) = (742346514439 / 1875000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (154111118887979161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2969386057757 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (742346514439 / 25000000000000 : ℝ)) ≤ (238762747783953523847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_19 : ∀ t : ℝ, (1611686987 / 2000000000000 : ℝ) < t → t ≤ (220431339 / 250000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-281514737178973769803437117 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (1611686987 / 2000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_19
  have hV : (1274128395526980931703998560016649 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (220431339 / 250000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_19 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (220431339 / 250000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (220431339 / 250000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_20 : (1261387361433427164727594855980933 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (4047462733 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4047462733 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (397622953321 / 12500000000000 : ℝ) ≤ Real.sqrt (4047462733 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4047462733 / 4000000000000 : ℝ) ≤ (3180983626569 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3180983626569 / 100000000000000 : ℝ) = (100000000000000 / 3180983626569 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (397622953321 / 12500000000000 : ℝ) = (937500000000 / 397622953321 : ℝ) := by norm_num
  have hL1 : (12641926153 / 12500000000000 : ℝ) ≤ Real.log (1 + (4047462733 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4047462733 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-20060461842053 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3180983626569 / 100000000000000 : ℝ) ≤ (1271964547237 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (153899721311397161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 3180983626569 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 3180983626569 : ℝ) = (3180983626569 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (401134493736299 / 1000000000000000 : ℝ) ≤ Real.arctan (397622953321 / 937500000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (937500000000 / 397622953321 : ℝ) ≤ (233932366611719523847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (937500000000 / 397622953321 : ℝ) = (397622953321 / 937500000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (153899721311397161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3180983626569 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (397622953321 / 12500000000000 : ℝ)) ≤ (233932366611719523847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_20 : ∀ t : ℝ, (220431339 / 250000000000 : ℝ) < t → t ≤ (4047462733 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2204430428372891296480279 / 781250000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (220431339 / 250000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_20
  have hV : (1261387361433427164727594855980933 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (4047462733 / 4000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_20 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (4047462733 / 4000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (4047462733 / 4000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_21 : (1250121938081039347163202099269369 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (2284012021 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2284012021 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (844839485679 / 25000000000000 : ℝ) ≤ Real.sqrt (2284012021 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2284012021 / 2000000000000 : ℝ) ≤ (3379357942717 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3379357942717 / 100000000000000 : ℝ) = (100000000000000 / 3379357942717 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (844839485679 / 25000000000000 : ℝ) = (625000000000 / 281613161893 : ℝ) := by norm_num
  have hL1 : (114135441767 / 100000000000000 : ℝ) ≤ Real.log (1 + (2284012021 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2284012021 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24978482657227 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3379357942717 / 100000000000000 : ℝ) ≤ (33780724077613 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (153701560271728361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 3379357942717 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 3379357942717 : ℝ) = (3379357942717 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (211668515109333 / 500000000000000 : ℝ) ≤ Real.arctan (281613161893 / 625000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (625000000000 / 281613161893 : ℝ) ≤ (229491859315246123847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (625000000000 / 281613161893 : ℝ) = (281613161893 / 625000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (153701560271728361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3379357942717 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (844839485679 / 25000000000000 : ℝ)) ≤ (229491859315246123847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_21 : ∀ t : ℝ, (4047462733 / 4000000000000 : ℝ) < t → t ≤ (2284012021 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-56489682990916919911849411 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (4047462733 / 4000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_21
  have hV : (1250121938081039347163202099269369 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (2284012021 / 2000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_21 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (2284012021 / 2000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (2284012021 / 2000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_22 : (155009253408972575187665811792931 / 156250000000000000000000000000000 : ℝ) ≤ Vfield (5088585351 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5088585351 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (3566716049463 / 100000000000000 : ℝ) ≤ Real.sqrt (5088585351 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5088585351 / 4000000000000 : ℝ) ≤ (445839506183 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (445839506183 / 12500000000000 : ℝ) = (12500000000000 / 445839506183 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3566716049463 / 100000000000000 : ℝ) = (2500000000000 / 1188905349821 : ℝ) := by norm_num
  have hL1 : (3178344613 / 2500000000000 : ℝ) ≤ Real.log (1 + (5088585351 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5088585351 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-49766475250839 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (445839506183 / 12500000000000 : ℝ) ≤ (4456505926591 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (153514427938216861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 445839506183 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 445839506183 : ℝ) = (445839506183 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (443906892214837 / 1000000000000000 : ℝ) ≤ Real.arctan (1188905349821 / 2500000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (2500000000000 / 1188905349821 : ℝ) ≤ (225377886916011923847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (2500000000000 / 1188905349821 : ℝ) = (1188905349821 / 2500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (153514427938216861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (445839506183 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3566716049463 / 100000000000000 : ℝ)) ≤ (225377886916011923847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_22 : ∀ t : ℝ, (2284012021 / 2000000000000 : ℝ) < t → t ≤ (5088585351 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-282767039638574273823494047 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (2284012021 / 2000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_22
  have hV : (155009253408972575187665811792931 / 156250000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (5088585351 / 4000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_22 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (5088585351 / 4000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (5088585351 / 4000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_23 : (615525310680615063940268246868279 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (280457333 / 200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (280457333 / 200000000000 : ℝ) := by norm_num
  have hs1 : (3744711824693 / 100000000000000 : ℝ) ≤ Real.sqrt (280457333 / 200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (280457333 / 200000000000 : ℝ) ≤ (1872355912347 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1872355912347 / 50000000000000 : ℝ) = (50000000000000 / 1872355912347 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3744711824693 / 100000000000000 : ℝ) = (7500000000000 / 3744711824693 : ℝ) := by norm_num
  have hL1 : (35032609481 / 25000000000000 : ℝ) ≤ Real.log (1 + (280457333 / 200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((280457333 / 200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-123948865268327 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1872355912347 / 50000000000000 : ℝ) ≤ (18714814547307 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (153336669770028261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 1872355912347 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 1872355912347 : ℝ) = (1872355912347 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : (463083377891697 / 1000000000000000 : ℝ) ≤ Real.arctan (3744711824693 / 7500000000000 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7500000000000 / 3744711824693 : ℝ) ≤ (221542589780639923847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (7500000000000 / 3744711824693 : ℝ) = (3744711824693 / 7500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (153336669770028261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1872355912347 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3744711824693 / 100000000000000 : ℝ)) ≤ (221542589780639923847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_23 : ∀ t : ℝ, (5088585351 / 4000000000000 : ℝ) < t → t ≤ (280457333 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-35394138455335797124678923 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (5088585351 / 4000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_23
  have hV : (615525310680615063940268246868279 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (280457333 / 200000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_23 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (280457333 / 200000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (280457333 / 200000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_24 : (1217309624717630104607038953008031 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (6519108259 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (6519108259 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (2018524872741 / 50000000000000 : ℝ) ≤ Real.sqrt (6519108259 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (6519108259 / 4000000000000 : ℝ) ≤ (4037049745483 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4037049745483 / 100000000000000 : ℝ) = (100000000000000 / 4037049745483 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (2018524872741 / 50000000000000 : ℝ) = (1250000000000 / 672841624247 : ℝ) := by norm_num
  have hL1 : (162845041933 / 100000000000000 : ℝ) ≤ Real.log (1 + (6519108259 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((6519108259 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-246304755976807 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4037049745483 / 100000000000000 : ℝ) ≤ (8069717447831 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (153044773955574161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 4037049745483 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 4037049745483 : ℝ) = (4037049745483 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA7 : (246897714502233 / 1000000000000000 : ℝ) ≤ Real.arctan (53827329939760 / 213566638800503 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA6 : (246897714502233 / 500000000000000 : ℝ) ≤ Real.arctan (672841624247 / 1250000000000 : ℝ) := by
    have hw : Real.sqrt (1 + (672841624247 / 1250000000000 : ℝ) ^ 2) ≤ (113566638800503 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
    have := arctan_ge_half (by norm_num) hw
    have e : (672841624247 / 1250000000000 : ℝ) / (1 + (113566638800503 / 100000000000000 : ℝ)) = (53827329939760 / 213566638800503 : ℝ) := by norm_num
    rw [e] at this; linarith [hA7]
  have hA5 : Real.arctan (1250000000000 / 672841624247 : ℝ) ≤ (215400179558086123847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (1250000000000 / 672841624247 : ℝ) = (672841624247 / 1250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (153044773955574161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4037049745483 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (2018524872741 / 50000000000000 : ℝ)) ≤ (215400179558086123847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_24 : ∀ t : ℝ, (280457333 / 200000000000 : ℝ) < t → t ≤ (6519108259 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-283915307968191474970423841 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (280457333 / 200000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_24
  have hV : (1217309624717630104607038953008031 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (6519108259 / 4000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_24 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (6519108259 / 4000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (6519108259 / 4000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_25 : (120567399116125513458047891768147 / 125000000000000000000000000000000 : ℝ) ≤ Vfield (3714534929 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3714534929 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (4309602608709 / 100000000000000 : ℝ) ≤ Real.sqrt (3714534929 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3714534929 / 2000000000000 : ℝ) ≤ (430960260871 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (430960260871 / 10000000000000 : ℝ) = (10000000000000 / 430960260871 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4309602608709 / 100000000000000 : ℝ) = (2500000000000 / 1436534202903 : ℝ) := by norm_num
  have hL1 : (92777243791 / 50000000000000 : ℝ) ≤ Real.log (1 + (3714534929 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3714534929 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-489521939388767 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (430960260871 / 10000000000000 : ℝ) ≤ (53836719371 / 1250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (152772695129809661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 430960260871 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 430960260871 : ℝ) = (430960260871 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA7 : (130385975621911 / 500000000000000 : ℝ) ≤ Real.arctan (11492273623224 / 43066693586881 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA6 : (130385975621911 / 250000000000000 : ℝ) ≤ Real.arctan (1436534202903 / 2500000000000 : ℝ) := by
    have hw : Real.sqrt (1 + (1436534202903 / 2500000000000 : ℝ) ^ 2) ≤ (23066693586881 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
    have := arctan_ge_half (by norm_num) hw
    have e : (1436534202903 / 2500000000000 : ℝ) / (1 + (23066693586881 / 20000000000000 : ℝ)) = (11492273623224 / 43066693586881 : ℝ) := by norm_num
    rw [e] at this; linarith [hA7]
  have hA5 : Real.arctan (2500000000000 / 1436534202903 : ℝ) ≤ (209850484861450523847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (2500000000000 / 1436534202903 : ℝ) = (1436534202903 / 2500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (152772695129809661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (430960260871 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4309602608709 / 100000000000000 : ℝ)) ≤ (209850484861450523847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_25 : ∀ t : ℝ, (6519108259 / 4000000000000 : ℝ) < t → t ≤ (3714534929 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-56834906398966478282910149 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (6519108259 / 4000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_25
  have hV : (120567399116125513458047891768147 / 125000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (3714534929 / 2000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_25 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (3714534929 / 2000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (3714534929 / 2000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_26 : (239146895943491440349058989522453 / 250000000000000000000000000000000 : ℝ) ≤ Vfield (8339031457 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (8339031457 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (1141478718661 / 25000000000000 : ℝ) ≤ Real.sqrt (8339031457 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (8339031457 / 4000000000000 : ℝ) ≤ (913182974929 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (913182974929 / 20000000000000 : ℝ) = (20000000000000 / 913182974929 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1141478718661 / 25000000000000 : ℝ) = (1875000000000 / 1141478718661 : ℝ) := by norm_num
  have hL1 : (52064694303 / 25000000000000 : ℝ) ≤ Real.log (1 + (8339031457 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((8339031457 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-486526849523553 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (913182974929 / 20000000000000 : ℝ) ≤ (22813729476601 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (152516886784169461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 913182974929 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 913182974929 : ℝ) = (913182974929 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA7 : (136714173599181 / 500000000000000 : ℝ) ≤ Real.arctan (91318297492880 / 325610453723571 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA6 : (136714173599181 / 250000000000000 : ℝ) ≤ Real.arctan (1141478718661 / 1875000000000 : ℝ) := by
    have hw : Real.sqrt (1 + (1141478718661 / 1875000000000 : ℝ) ^ 2) ≤ (58536817907857 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
    have := arctan_ge_half (by norm_num) hw
    have e : (1141478718661 / 1875000000000 : ℝ) / (1 + (58536817907857 / 50000000000000 : ℝ)) = (91318297492880 / 325610453723571 : ℝ) := by norm_num
    rw [e] at this; linarith [hA7]
  have hA5 : Real.arctan (1875000000000 / 1141478718661 : ℝ) ≤ (204787926479634523847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (1875000000000 / 1141478718661 : ℝ) = (1141478718661 / 1875000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (152516886784169461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (913182974929 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1141478718661 / 25000000000000 : ℝ)) ≤ (204787926479634523847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_26 : ∀ t : ℝ, (3714534929 / 2000000000000 : ℝ) < t → t ≤ (8339031457 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-56895465247786563506496721 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (3714534929 / 2000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_26
  have hV : (239146895943491440349058989522453 / 250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (8339031457 / 4000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_26 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (8339031457 / 4000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (8339031457 / 4000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_27 : (237438570779561520680417410919081 / 250000000000000000000000000000000 : ℝ) ≤ Vfield (289031033 / 125000000000 : ℝ) := by
  have hp : (0 : ℝ) < (289031033 / 125000000000 : ℝ) := by norm_num
  have hs1 : (75134129151 / 1562500000000 : ℝ) ≤ Real.sqrt (289031033 / 125000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (289031033 / 125000000000 : ℝ) ≤ (961716853133 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (961716853133 / 20000000000000 : ℝ) = (20000000000000 / 961716853133 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (75134129151 / 1562500000000 : ℝ) = (39062500000 / 25044709717 : ℝ) := by norm_num
  have hL1 : (46191582633 / 20000000000000 : ℝ) ≤ Real.log (1 + (289031033 / 125000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((289031033 / 125000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-120904715705457 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (961716853133 / 20000000000000 : ℝ) ≤ (48048831854593 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (152274749494030361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 961716853133 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 961716853133 : ℝ) = (961716853133 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA7 : (285062375210247 / 1000000000000000 : ℝ) ≤ Real.arctan (64114456875520 / 218788314157761 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA6 : (285062375210247 / 500000000000000 : ℝ) ≤ Real.arctan (25044709717 / 39062500000 : ℝ) := by
    have hw : Real.sqrt (1 + (25044709717 / 39062500000 : ℝ) ^ 2) ≤ (118788314157761 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
    have := arctan_ge_half (by norm_num) hw
    have e : (25044709717 / 39062500000 : ℝ) / (1 + (118788314157761 / 100000000000000 : ℝ)) = (64114456875520 / 218788314157761 : ℝ) := by norm_num
    rw [e] at this; linarith [hA7]
  have hA5 : Real.arctan (39062500000 / 25044709717 : ℝ) ≤ (200134315274880523847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (39062500000 / 25044709717 : ℝ) = (25044709717 / 39062500000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (152274749494030361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (961716853133 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (75134129151 / 1562500000000 : ℝ)) ≤ (200134315274880523847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_27 : ∀ t : ℝ, (8339031457 / 4000000000000 : ℝ) < t → t ≤ (289031033 / 125000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-142430401946706779596191059 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (8339031457 / 4000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_27
  have hV : (237438570779561520680417410919081 / 250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (289031033 / 125000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_27 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (289031033 / 125000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (289031033 / 125000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_28 : (14568195093660560196271147220221 / 15625000000000000000000000000000 : ℝ) ≤ Vfield (124379927 / 40000000000 : ℝ) := by
  have hp : (0 : ℝ) < (124379927 / 40000000000 : ℝ) := by norm_num
  have hs1 : (5576287452239 / 100000000000000 : ℝ) ≤ Real.sqrt (124379927 / 40000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (124379927 / 40000000000 : ℝ) ≤ (69703593153 / 1250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (69703593153 / 1250000000000 : ℝ) = (1250000000000 / 69703593153 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5576287452239 / 100000000000000 : ℝ) = (7500000000000 / 5576287452239 : ℝ) := by norm_num
  have hL1 : (77616842103 / 25000000000000 : ℝ) ≤ Real.log (1 + (124379927 / 40000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((124379927 / 40000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-237023739257047 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (69703593153 / 1250000000000 : ℝ) ≤ (55705183931963 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (151509114286293361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1250000000000 / 69703593153 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (1250000000000 / 69703593153 : ℝ) = (69703593153 / 1250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA7 : (319665664545649 / 1000000000000000 : ℝ) ≤ Real.arctan (31864499727080 / 96262021255419 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA6 : (319665664545649 / 500000000000000 : ℝ) ≤ Real.arctan (5576287452239 / 7500000000000 : ℝ) := by
    have hw : Real.sqrt (1 + (5576287452239 / 7500000000000 : ℝ) ^ 2) ≤ (124611382929311 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
    have := arctan_ge_half (by norm_num) hw
    have e : (5576287452239 / 7500000000000 : ℝ) / (1 + (124611382929311 / 100000000000000 : ℝ)) = (31864499727080 / 96262021255419 : ℝ) := by norm_num
    rw [e] at this; linarith [hA7]
  have hA5 : Real.arctan (7500000000000 / 5576287452239 : ℝ) ≤ (186292999540719723847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (7500000000000 / 5576287452239 : ℝ) = (5576287452239 / 7500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (151509114286293361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (69703593153 / 1250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5576287452239 / 100000000000000 : ℝ)) ≤ (186292999540719723847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_28 : ∀ t : ℝ, (289031033 / 125000000000 : ℝ) < t → t ≤ (124379927 / 40000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-285707693309385314951570509 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (289031033 / 125000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_28
  have hV : (14568195093660560196271147220221 / 15625000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (124379927 / 40000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_28 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (124379927 / 40000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (124379927 / 40000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_29 : (289531307233729438206221877547721 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (7016246261 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7016246261 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (5922941102611 / 100000000000000 : ℝ) ≤ Real.sqrt (7016246261 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7016246261 / 2000000000000 : ℝ) ≤ (1480735275653 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1480735275653 / 25000000000000 : ℝ) = (25000000000000 / 1480735275653 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5922941102611 / 100000000000000 : ℝ) = (7500000000000 / 5922941102611 : ℝ) := by norm_num
  have hL1 : (350198402019 / 100000000000000 : ℝ) ≤ Real.log (1 + (7016246261 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7016246261 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-469584756761021 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1480735275653 / 25000000000000 : ℝ) ≤ (14790073773153 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (151163603170228461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 1480735275653 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 1480735275653 : ℝ) = (1480735275653 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA7 : (5222222785697 / 15625000000000 : ℝ) ≤ Real.arctan (236917644104440 / 682269499290747 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA6 : (5222222785697 / 7812500000000 : ℝ) ≤ Real.arctan (5922941102611 / 7500000000000 : ℝ) := by
    have hw : Real.sqrt (1 + (5922941102611 / 7500000000000 : ℝ) ^ 2) ≤ (127423166430249 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
    have := arctan_ge_half (by norm_num) hw
    have e : (5922941102611 / 7500000000000 : ℝ) / (1 + (127423166430249 / 100000000000000 : ℝ)) = (236917644104440 / 682269499290747 : ℝ) := by norm_num
    rw [e] at this; linarith [hA7]
  have hA5 : Real.arctan (7500000000000 / 5922941102611 : ℝ) ≤ (180470362045136123847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (7500000000000 / 5922941102611 : ℝ) = (5922941102611 / 7500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (151163603170228461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1480735275653 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5922941102611 / 100000000000000 : ℝ)) ≤ (180470362045136123847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_29 : ∀ t : ℝ, (124379927 / 40000000000 : ℝ) < t → t ≤ (7016246261 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-286018759122783173258038489 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (124379927 / 40000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_29
  have hV : (289531307233729438206221877547721 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (7016246261 / 2000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_29 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (7016246261 / 2000000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (7016246261 / 2000000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_30 : (1152534092134601561124147996169143 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (1953374043 / 500000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1953374043 / 500000000000 : ℝ) := by norm_num
  have hs1 : (3125199228049 / 50000000000000 : ℝ) ≤ Real.sqrt (1953374043 / 500000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1953374043 / 500000000000 : ℝ) ≤ (6250398456099 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6250398456099 / 100000000000000 : ℝ) = (100000000000000 / 6250398456099 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3125199228049 / 50000000000000 : ℝ) = (3750000000000 / 3125199228049 : ℝ) := by norm_num
  have hL1 : (77982731269 / 20000000000000 : ℝ) ≤ Real.log (1 + (1953374043 / 500000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1953374043 / 500000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-29082044665731 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6250398456099 / 100000000000000 : ℝ) ≤ (12484555810367 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (150837354774306161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 6250398456099 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 6250398456099 : ℝ) = (6250398456099 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA7 : (43423101831247 / 125000000000000 : ℝ) ≤ Real.arctan (62503984560980 / 172630671850599 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA6 : (43423101831247 / 62500000000000 : ℝ) ≤ Real.arctan (3125199228049 / 3750000000000 : ℝ) := by
    have hw : Real.sqrt (1 + (3125199228049 / 3750000000000 : ℝ) ^ 2) ≤ (32543557283533 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
    have := arctan_ge_half (by norm_num) hw
    have e : (3125199228049 / 3750000000000 : ℝ) / (1 + (32543557283533 / 25000000000000 : ℝ)) = (62503984560980 / 172630671850599 : ℝ) := by norm_num
    rw [e] at this; linarith [hA7]
  have hA5 : Real.arctan (3750000000000 / 3125199228049 : ℝ) ≤ (175205339498988923847 / 200000000000000000000 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_lt_d20
    have e : (1 : ℝ) / (3750000000000 / 3125199228049 : ℝ) = (3125199228049 / 3750000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA6]
  have hA1' : (150837354774306161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6250398456099 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3125199228049 / 50000000000000 : ℝ)) ≤ (175205339498988923847 / 200000000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_30 : ∀ t : ℝ, (7016246261 / 2000000000000 : ℝ) < t → t ≤ (1953374043 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-286249726575931037718699949 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_antitoneOn (show (7016246261 / 2000000000000 : ℝ) ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by norm_num)) (show t ∈ Set.Iic (aρ 1) by rw [aρ_1]; exact Set.mem_Iic.mpr (by linarith)) h1.le) U_pt_30
  have hV : (1152534092134601561124147996169143 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (1953374043 / 500000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_30 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (1953374043 / 500000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (1953374043 / 500000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_31 : (4567797667624645445829235536147287 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (59205077 / 10000000000 : ℝ) := by
  have hp : (0 : ℝ) < (59205077 / 10000000000 : ℝ) := by norm_num
  have hs1 : (3847241771711 / 50000000000000 : ℝ) ≤ Real.sqrt (59205077 / 10000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (59205077 / 10000000000 : ℝ) ≤ (7694483543423 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7694483543423 / 100000000000000 : ℝ) = (100000000000000 / 7694483543423 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3847241771711 / 50000000000000 : ℝ) = (3750000000000 / 3847241771711 : ℝ) := by norm_num
  have hL1 : (590305036459 / 100000000000000 : ℝ) ≤ Real.log (1 + (59205077 / 10000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((59205077 / 10000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-111536471489397 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7694483543423 / 100000000000000 : ℝ) ≤ (2399797554803 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (149400280504120061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 7694483543423 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 7694483543423 : ℝ) = (7694483543423 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (375000000000000000000000000 / 921974298157572884713630037 : ℝ) ≤ (386299623528461 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (3750000000000 / 3847241771711 : ℝ) ≤ (386299623528461 / 500000000000000 : ℝ) := by
    have hw : (139645531231467 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (3750000000000 / 3847241771711 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3750000000000 / 3847241771711 : ℝ) / (1 + (139645531231467 / 100000000000000 : ℝ)) = (375000000000000000000000000 / 921974298157572884713630037 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (149400280504120061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7694483543423 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3847241771711 / 50000000000000 : ℝ)) ≤ (386299623528461 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_neg hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_31 : ∀ t : ℝ, (1953374043 / 500000000000 : ℝ) < t → t ≤ (59205077 / 10000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-286831084198255509109161609 / 100000000000000000000000000 : ℝ) := by
    have e1 := Uρ_of_mem (t := t) (by rw [aρ_1]; linarith) (by rw [bρ_1]; linarith)
    have e2 := Uρ_of_mem (t := (1953374043 / 500000000000 : ℝ)) (by rw [aρ_1]; norm_num) (by rw [bρ_1]; norm_num)
    rw [e1, ← e2]; exact U_pt_31
  have hV : (4567797667624645445829235536147287 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205077 / 10000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ) := by norm_num
    refine le_trans V_pt_31 (Vfield_antitoneOn (show t ∈ Set.Ioc 0 qm from ⟨by linarith, by show t ≤ (59205077 / 10 ^ 10 : ℝ); linarith⟩) (show (59205077 / 10000000000 : ℝ) ∈ Set.Ioc 0 qm from ⟨by norm_num, by show (59205077 / 10000000000 : ℝ) ≤ (59205077 / 10 ^ 10 : ℝ); norm_num⟩) h2)
  show _ ≤ -1329 / 200
  linarith

lemma Vstar_ge : (2283898813827172868022922124621917 / 2500000000000000000000000000000000 : ℝ) ≤ Vstar := by
  unfold Vstar
  have hs1 : (3847241771711 / 50000000000000 : ℝ) ≤ Real.sqrt qm := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt qp ≤ (3847241836693 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have hsqp : 0 < Real.sqrt qp := sqrt_qp_pos
  have e1 : (1 : ℝ) / (3847241836693 / 50000000000000 : ℝ) = (50000000000000 / 3847241836693 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3847241771711 / 50000000000000 : ℝ) = (3750000000000 / 3847241771711 : ℝ) := by norm_num
  have hL1 : (590305036459 / 100000000000000 : ℝ) ≤ Real.log (1 + qm) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log (qp + (3 / 40) ^ 2) ≤ (-446145884225313 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3847241836693 / 50000000000000 : ℝ) ≤ (19198380761419 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (149400280374922061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 3847241836693 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 3847241836693 : ℝ) = (3847241836693 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (375000000000000000000000000 / 921974298157572884713630037 : ℝ) ≤ (386299623528461 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (3750000000000 / 3847241771711 : ℝ) ≤ (386299623528461 / 500000000000000 : ℝ) := by
    have hw : (139645531231467 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (3750000000000 / 3847241771711 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3750000000000 / 3847241771711 : ℝ) / (1 + (139645531231467 / 100000000000000 : ℝ)) = (375000000000000000000000000 / 921974298157572884713630037 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hm1 : Real.arctan (1 / (3847241836693 / 50000000000000 : ℝ)) ≤ Real.arctan (1 / Real.sqrt qp) := Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left zero_le_one hsqp hs2)
  have hm2 : Real.arctan ((3 / 40) / Real.sqrt qm) ≤ Real.arctan ((3 / 40) / (3847241771711 / 50000000000000 : ℝ)) := Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs1)
  rw [e1] at hm1; rw [e2] at hm2
  have hpi := Real.pi_gt_d20
  have hPle : (-2500251814231 / 100000000000000000000 : ℝ) ≤ Real.pi + Real.arctan (1 / Real.sqrt qp) - 6 * Real.arctan ((3 / 40) / Real.sqrt qm) := by linarith [hA3, hA5]
  have hprod : 2 * (3847241836693 / 50000000000000 : ℝ) * (-2500251814231 / 100000000000000000000 : ℝ) ≤ 2 * Real.sqrt qp * (Real.pi + Real.arctan (1 / Real.sqrt qp) - 6 * Real.arctan ((3 / 40) / Real.sqrt qm)) := by
    calc 2 * (3847241836693 / 50000000000000 : ℝ) * (-2500251814231 / 100000000000000000000 : ℝ) ≤ 2 * Real.sqrt qp * (-2500251814231 / 100000000000000000000 : ℝ) := mul_le_mul_of_nonpos_right (by linarith) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hPle (by positivity)
  have hl2' : 6 * (3 / 40) * Real.log (qp + (3 / 40) ^ 2) ≤ 6 * (3 / 40) * (-446145884225313 / 100000000000000 : ℝ) := mul_le_mul_of_nonneg_left hL2 (by norm_num)
  linarith

lemma I_32 : ∀ t : ℝ, (59205077 / 10000000000 : ℝ) < t → t ≤ (59205079 / 10000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-286831084198255509109161609 / 100000000000000000000000000 : ℝ) := by
    have e1 := Uρ_of_mem (t := t) (by rw [aρ_1]; linarith) (by rw [bρ_1]; linarith)
    have e2 := Uρ_of_mem (t := (59205077 / 10000000000 : ℝ)) (by rw [aρ_1]; norm_num) (by rw [bρ_1]; norm_num)
    rw [e1, ← e2]; exact U_pt_32
  have hV : (2283898813827172868022922124621917 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    exact le_trans Vstar_ge (Vfield_ge_Vstar h1.le h2)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_33 : (913559533524911463081400803411613 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (59205079 / 10000000000 : ℝ) := by
  have hp : (0 : ℝ) < (59205079 / 10000000000 : ℝ) := by norm_num
  have hs1 : (1538896734677 / 20000000000000 : ℝ) ≤ Real.sqrt (59205079 / 10000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (59205079 / 10000000000 : ℝ) ≤ (3847241836693 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3847241836693 / 50000000000000 : ℝ) = (50000000000000 / 3847241836693 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1538896734677 / 20000000000000 : ℝ) = (1500000000000 / 1538896734677 : ℝ) := by norm_num
  have hL1 : (590305056341 / 100000000000000 : ℝ) ≤ Real.log (1 + (59205079 / 10000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((59205079 / 10000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-446145884225313 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3847241836693 / 50000000000000 : ℝ) ≤ (19198380761419 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (149400280374922061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 3847241836693 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 3847241836693 : ℝ) = (3847241836693 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (12500000000000000000000000 / 30732476976967905618472661 : ℝ) ≤ (386299619307243 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (1500000000000 / 1538896734677 : ℝ) ≤ (386299619307243 / 500000000000000 : ℝ) := by
    have hw : (34911382520579 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (1500000000000 / 1538896734677 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (1500000000000 / 1538896734677 : ℝ) / (1 + (34911382520579 / 25000000000000 : ℝ)) = (12500000000000000000000000 / 30732476976967905618472661 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (149400280374922061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3847241836693 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1538896734677 / 20000000000000 : ℝ)) ≤ (386299619307243 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_33 : ∀ t : ℝ, (59205079 / 10000000000 : ℝ) < t → t ≤ (8992695531 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-286831084198255509109161609 / 100000000000000000000000000 : ℝ) := by
    have e1 := Uρ_of_mem (t := t) (by rw [aρ_1]; linarith) (by rw [bρ_1]; linarith)
    have e2 := Uρ_of_mem (t := (59205079 / 10000000000 : ℝ)) (by rw [aρ_1]; norm_num) (by rw [bρ_1]; norm_num)
    rw [e1, ← e2]; exact U_pt_33
  have hV : (913559533524911463081400803411613 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (59205079 / 10000000000 : ℝ) := by norm_num
    refine le_trans V_pt_33 (Vfield_monotoneOn (show (59205079 / 10000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (59205079 / 10000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_34 : (4623890840011806853024720846206723 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (8992695531 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (8992695531 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (9482982405867 / 100000000000000 : ℝ) ≤ Real.sqrt (8992695531 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (8992695531 / 1000000000000 : ℝ) ≤ (2370745601467 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2370745601467 / 25000000000000 : ℝ) = (25000000000000 / 2370745601467 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (9482982405867 / 100000000000000 : ℝ) = (2500000000000 / 3160994135289 : ℝ) := by norm_num
  have hL1 : (89525020301 / 10000000000000 : ℝ) ≤ Real.log (1 + (8992695531 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((8992695531 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-13204757686511 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2370745601467 / 25000000000000 : ℝ) ≤ (94547089447431 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (147624923734746561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 2370745601467 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 2370745601467 : ℝ) = (2370745601467 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (250000000000000000000000000 / 719111620829514726019737213 : ℝ) ≤ (167290397241589 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (2500000000000 / 3160994135289 : ℝ) ≤ (167290397241589 / 250000000000000 : ℝ) := by
    have hw : (127495398615717 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (2500000000000 / 3160994135289 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (2500000000000 / 3160994135289 : ℝ) / (1 + (127495398615717 / 100000000000000 : ℝ)) = (250000000000000000000000000 / 719111620829514726019737213 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (147624923734746561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2370745601467 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (9482982405867 / 100000000000000 : ℝ)) ≤ (167290397241589 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_34 : ∀ t : ℝ, (8992695531 / 1000000000000 : ℝ) < t → t ≤ (19572466643 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-286020563914077139609829389 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19572466643 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_35
  have hV : (4623890840011806853024720846206723 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (8992695531 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_34 (Vfield_monotoneOn (show (8992695531 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (8992695531 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_35 : (581379453724600930419875065495279 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (19572466643 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19572466643 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (1236567408791 / 12500000000000 : ℝ) ≤ Real.sqrt (19572466643 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19572466643 / 2000000000000 : ℝ) ≤ (9892539270329 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (9892539270329 / 100000000000000 : ℝ) = (100000000000000 / 9892539270329 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1236567408791 / 12500000000000 : ℝ) = (937500000000 / 1236567408791 : ℝ) := by norm_num
  have hL1 : (973865827537 / 100000000000000 : ℝ) ≤ Real.log (1 + (19572466643 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19572466643 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-13039558116223 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (9892539270329 / 100000000000000 : ℝ) ≤ (9860457205751 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (147219175473738661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 9892539270329 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 9892539270329 : ℝ) = (9892539270329 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (5859375000000000000000000 / 17427139160522516907418651 : ℝ) ≤ (64869489765043 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (937500000000 / 1236567408791 : ℝ) ≤ (64869489765043 / 100000000000000 : ℝ) := by
    have hw : (7843157426461 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (937500000000 / 1236567408791 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (937500000000 / 1236567408791 : ℝ) / (1 + (7843157426461 / 6250000000000 : ℝ)) = (5859375000000000000000000 / 17427139160522516907418651 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (147219175473738661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (9892539270329 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1236567408791 / 12500000000000 : ℝ)) ≤ (64869489765043 / 100000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_35 : ∀ t : ℝ, (19572466643 / 2000000000000 : ℝ) < t → t ≤ (40732008867 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-285849657419784029883406909 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (40732008867 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_36
  have hV : (581379453724600930419875065495279 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19572466643 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_35 (Vfield_monotoneOn (show (19572466643 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19572466643 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_36 : (4665914246056666194334715168589711 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (40732008867 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (40732008867 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (10091086272919 / 100000000000000 : ℝ) ≤ Real.sqrt (40732008867 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (40732008867 / 4000000000000 : ℝ) ≤ (252277156823 / 2500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (252277156823 / 2500000000000 : ℝ) = (2500000000000 / 252277156823 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10091086272919 / 100000000000000 : ℝ) = (7500000000000 / 10091086272919 : ℝ) := by norm_num
  have hL1 : (1013150475379 / 100000000000000 : ℝ) ≤ Real.log (1 + (40732008867 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((40732008867 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-414723899618733 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (252277156823 / 2500000000000 : ℝ) ≤ (100570415208091 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (147022591158680561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (2500000000000 / 252277156823 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (2500000000000 / 252277156823 : ℝ) = (252277156823 / 2500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (125000000000000000000000000 / 377734567847878569552260829 : ℝ) ≤ (9986786481901 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7500000000000 / 10091086272919 : ℝ) ≤ (9986786481901 / 15625000000000 : ℝ) := by
    have hw : (62297494332673 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (7500000000000 / 10091086272919 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7500000000000 / 10091086272919 : ℝ) / (1 + (62297494332673 / 50000000000000 : ℝ)) = (125000000000000000000000000 / 377734567847878569552260829 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (147022591158680561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (252277156823 / 2500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10091086272919 / 100000000000000 : ℝ)) ≤ (9986786481901 / 15625000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_36 : ∀ t : ℝ, (40732008867 / 4000000000000 : ℝ) < t → t ≤ (1322471389 / 125000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-285710088820188505697116349 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1322471389 / 125000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_37
  have hV : (4665914246056666194334715168589711 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (40732008867 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_36 (Vfield_monotoneOn (show (40732008867 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (40732008867 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_37 : (4681557961704254603595804092665067 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1322471389 / 125000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1322471389 / 125000000000 : ℝ) := by norm_num
  have hs1 : (10285801433043 / 100000000000000 : ℝ) ≤ Real.sqrt (1322471389 / 125000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1322471389 / 125000000000 : ℝ) ≤ (2571450358261 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2571450358261 / 25000000000000 : ℝ) = (25000000000000 / 2571450358261 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10285801433043 / 100000000000000 : ℝ) = (2500000000000 / 3428600477681 : ℝ) := by norm_num
  have hL1 : (526209848223 / 50000000000000 : ℝ) ≤ Real.log (1 + (1322471389 / 125000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1322471389 / 125000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-412244956545817 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2571450358261 / 25000000000000 : ℝ) ≤ (102497561600261 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (146829876519463561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 2571450358261 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 2571450358261 : ℝ) = (2571450358261 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (125000000000000000000000000 / 383593293770440700065171053 : ℝ) ≤ (157507469028237 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (2500000000000 / 3428600477681 : ℝ) ≤ (157507469028237 / 250000000000000 : ℝ) := by
    have hw : (61880429425213 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (2500000000000 / 3428600477681 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (2500000000000 / 3428600477681 : ℝ) / (1 + (61880429425213 / 50000000000000 : ℝ)) = (125000000000000000000000000 / 383593293770440700065171053 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (146829876519463561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2571450358261 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10285801433043 / 100000000000000 : ℝ)) ≤ (157507469028237 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_37 : ∀ t : ℝ, (1322471389 / 125000000000 : ℝ) < t → t ≤ (4549323561 / 400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-285485839281551924431582129 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4549323561 / 400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_38
  have hV : (4681557961704254603595804092665067 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1322471389 / 125000000000 : ℝ) := by norm_num
    refine le_trans V_pt_37 (Vfield_monotoneOn (show (1322471389 / 125000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1322471389 / 125000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_38 : (2357437287490982604046828904140887 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (4549323561 / 400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4549323561 / 400000000000 : ℝ) := by norm_num
  have hs1 : (5332285837823 / 50000000000000 : ℝ) ≤ Real.sqrt (4549323561 / 400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4549323561 / 400000000000 : ℝ) ≤ (10664571675647 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (10664571675647 / 100000000000000 : ℝ) = (100000000000000 / 10664571675647 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5332285837823 / 50000000000000 : ℝ) = (3750000000000 / 5332285837823 : ℝ) := by norm_num
  have hL1 : (226182381337 / 20000000000000 : ℝ) ≤ Real.log (1 + (4549323561 / 400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4549323561 / 400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-407464141463787 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (10664571675647 / 100000000000000 : ℝ) ≤ (26561037154251 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (146455217817789261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 10664571675647 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 10664571675647 : ℝ) = (10664571675647 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (23437500000000000000000000 / 74069774886358650835814623 : ℝ) ≤ (306456312643331 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (3750000000000 / 5332285837823 : ℝ) ≤ (306456312643331 / 500000000000000 : ℝ) := by
    have hw : (7640811021601 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (3750000000000 / 5332285837823 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3750000000000 / 5332285837823 : ℝ) / (1 + (7640811021601 / 6250000000000 : ℝ)) = (23437500000000000000000000 / 74069774886358650835814623 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (146455217817789261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (10664571675647 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5332285837823 / 50000000000000 : ℝ)) ≤ (306456312643331 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_38 : ∀ t : ℝ, (4549323561 / 400000000000 : ℝ) < t → t ≤ (12166846693 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-285306655847742696134579989 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (12166846693 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_39
  have hV : (2357437287490982604046828904140887 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4549323561 / 400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_38 (Vfield_monotoneOn (show (4549323561 / 400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4549323561 / 400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_39 : (1187630175979311107479072086579777 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (12166846693 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (12166846693 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (2757585752633 / 25000000000000 : ℝ) ≤ Real.sqrt (12166846693 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (12166846693 / 1000000000000 : ℝ) ≤ (11030343010533 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (11030343010533 / 100000000000000 : ℝ) = (100000000000000 / 11030343010533 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (2757585752633 / 25000000000000 : ℝ) = (1875000000000 / 2757585752633 : ℝ) := by norm_num
  have hL1 : (120934255497 / 10000000000000 : ℝ) ≤ Real.log (1 + (12166846693 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((12166846693 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-201450748800843 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (11030343010533 / 100000000000000 : ℝ) ≤ (109859319373459 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (146093700742143761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 11030343010533 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 11030343010533 : ℝ) = (11030343010533 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000000000000000 / 1624596742912768195902959 : ℝ) ≤ (11942747999181 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (1875000000000 / 2757585752633 : ℝ) ≤ (11942747999181 / 20000000000000 : ℝ) := by
    have hw : (967412028469 / 800000000000 : ℝ) ≤ Real.sqrt (1 + (1875000000000 / 2757585752633 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (1875000000000 / 2757585752633 : ℝ) / (1 + (967412028469 / 800000000000 : ℝ)) = (500000000000000000000000 / 1624596742912768195902959 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (146093700742143761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (11030343010533 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (2757585752633 / 25000000000000 : ℝ)) ≤ (11942747999181 / 20000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_39 : ∀ t : ℝ, (12166846693 / 1000000000000 : ℝ) < t → t ≤ (3068199571 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-284808118987486553957006549 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3068199571 / 200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_40
  have hV : (1187630175979311107479072086579777 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (12166846693 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_39 (Vfield_monotoneOn (show (12166846693 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (12166846693 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
