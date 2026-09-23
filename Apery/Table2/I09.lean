import Apery.Table2.U09
import Apery.Table2.U10

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_360 : (3794576954393596969495123393509751 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (23302054419351 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23302054419351 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (12068050386079 / 20000000000000 : ℝ) ≤ Real.sqrt (23302054419351 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23302054419351 / 64000000000000 : ℝ) ≤ (15085062982599 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (15085062982599 / 25000000000000 : ℝ) = (25000000000000 / 15085062982599 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (12068050386079 / 20000000000000 : ℝ) = (1500000000000 / 12068050386079 : ℝ) := by norm_num
  have hL1 : (3104909120767 / 10000000000000 : ℝ) ≤ Real.log (1 + (23302054419351 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23302054419351 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-49750519857413 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (15085062982599 / 54198615124505 : ℝ) ≤ (271458798786611 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (15085062982599 / 25000000000000 : ℝ) ≤ (271458798786611 / 500000000000000 : ℝ) := by
    have hw : (5839723024901 / 5000000000000 : ℝ) ≤ Real.sqrt (1 + (15085062982599 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (15085062982599 / 25000000000000 : ℝ) / (1 + (5839723024901 / 5000000000000 : ℝ)) = (15085062982599 / 54198615124505 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102787872922167461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 15085062982599 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 15085062982599 : ℝ) = (15085062982599 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 12068050386079 : ℝ) ≤ (123660917444881 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102787872922167461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (15085062982599 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (12068050386079 / 20000000000000 : ℝ)) ≤ (123660917444881 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_360 : ∀ t : ℝ, (23302054419351 / 64000000000000 : ℝ) < t → t ≤ (46687825988961 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-4458547231973658670380689 / 3125000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (46687825988961 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_361
  have hV : (3794576954393596969495123393509751 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23302054419351 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_360 (Vfield_monotoneOn (show (23302054419351 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23302054419351 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_361 : (9495726431305107417224536537444049 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (46687825988961 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (46687825988961 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (30197211814121 / 50000000000000 : ℝ) ≤ Real.sqrt (46687825988961 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (46687825988961 / 128000000000000 : ℝ) ≤ (60394423628243 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (60394423628243 / 100000000000000 : ℝ) = (100000000000000 / 60394423628243 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (30197211814121 / 50000000000000 : ℝ) = (3750000000000 / 30197211814121 : ℝ) := by norm_num
  have hL1 : (31097026555449 / 100000000000000 : ℝ) ≤ Real.log (1 + (46687825988961 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((46687825988961 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6207768394217 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (60394423628243 / 216822456768327 : ℝ) ≤ (27165731404031 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (60394423628243 / 100000000000000 : ℝ) ≤ (27165731404031 / 50000000000000 : ℝ) := by
    have hw : (116822456768327 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (60394423628243 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (60394423628243 / 100000000000000 : ℝ) / (1 + (116822456768327 / 100000000000000 : ℝ)) = (60394423628243 / 216822456768327 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102748169871427661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 60394423628243 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 60394423628243 : ℝ) = (60394423628243 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 30197211814121 : ℝ) ≤ (61775561870139 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102748169871427661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (60394423628243 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (30197211814121 / 50000000000000 : ℝ)) ≤ (61775561870139 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_361 : ∀ t : ℝ, (46687825988961 / 128000000000000 : ℝ) < t → t ≤ (2338577156961 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-142473746229224165845212167 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2338577156961 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_362
  have hV : (9495726431305107417224536537444049 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (46687825988961 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_361 (Vfield_monotoneOn (show (46687825988961 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (46687825988961 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_362 : (4752501431637205984204149115490799 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (2338577156961 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2338577156961 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (15112136694871 / 25000000000000 : ℝ) ≤ Real.sqrt (2338577156961 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2338577156961 / 6400000000000 : ℝ) ≤ (12089709355897 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (12089709355897 / 20000000000000 : ℝ) = (20000000000000 / 12089709355897 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (15112136694871 / 25000000000000 : ℝ) = (1875000000000 / 15112136694871 : ℝ) := by norm_num
  have hL1 : (31144938936261 / 100000000000000 : ℝ) ≤ Real.log (1 + (2338577156961 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2338577156961 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-9914786073843 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (12089709355897 / 43370089266198 : ℝ) ≤ (271855556364061 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (12089709355897 / 20000000000000 : ℝ) ≤ (271855556364061 / 500000000000000 : ℝ) := by
    have hw : (11685044633099 / 10000000000000 : ℝ) ≤ Real.sqrt (1 + (12089709355897 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (12089709355897 / 20000000000000 : ℝ) / (1 + (11685044633099 / 10000000000000 : ℝ)) = (12089709355897 / 43370089266198 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102708521406677461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 12089709355897 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 12089709355897 : ℝ) = (12089709355897 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 15112136694871 : ℝ) ≤ (123441621968051 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102708521406677461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (12089709355897 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (15112136694871 / 25000000000000 : ℝ)) ≤ (123441621968051 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_362 : ∀ t : ℝ, (2338577156961 / 6400000000000 : ℝ) < t → t ≤ (46855260289479 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-142275622145062138939189351 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (46855260289479 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_363
  have hV : (4752501431637205984204149115490799 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2338577156961 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_362 (Vfield_monotoneOn (show (2338577156961 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2338577156961 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_363 : (9514271699704589194236554752844107 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (46855260289479 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (46855260289479 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (30251310757203 / 50000000000000 : ℝ) ≤ Real.sqrt (46855260289479 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (46855260289479 / 128000000000000 : ℝ) ≤ (60502621514407 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (60502621514407 / 100000000000000 : ℝ) = (100000000000000 / 60502621514407 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (30251310757203 / 50000000000000 : ℝ) = (1250000000000 / 10083770252401 : ℝ) := by norm_num
  have hL1 : (3899103546513 / 12500000000000 : ℝ) ≤ Real.log (1 + (46855260289479 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((46855260289479 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-98971737909261 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (60502621514407 / 216878429190828 : ℝ) ≤ (54410705299251 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (60502621514407 / 100000000000000 : ℝ) ≤ (54410705299251 / 100000000000000 : ℝ) := by
    have hw : (29219607297707 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (60502621514407 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (60502621514407 / 100000000000000 : ℝ) / (1 + (29219607297707 / 25000000000000 : ℝ)) = (60502621514407 / 216878429190828 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102668927380238661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 60502621514407 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 60502621514407 : ℝ) = (60502621514407 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 10083770252401 : ℝ) ≤ (123332410836753 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102668927380238661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (60502621514407 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (30251310757203 / 50000000000000 : ℝ)) ≤ (123332410836753 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_363 : ∀ t : ℝ, (46855260289479 / 128000000000000 : ℝ) < t → t ≤ (23469488719869 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-35519767963712729586058141 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23469488719869 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_364
  have hV : (9514271699704589194236554752844107 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (46855260289479 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_363 (Vfield_monotoneOn (show (46855260289479 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (46855260289479 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_364 : (19047065916677930017865116666488221 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (23469488719869 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23469488719869 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (60556647962709 / 100000000000000 : ℝ) ≤ Real.sqrt (23469488719869 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23469488719869 / 64000000000000 : ℝ) ≤ (6055664796271 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6055664796271 / 10000000000000 : ℝ) = (10000000000000 / 6055664796271 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (60556647962709 / 100000000000000 : ℝ) = (2500000000000 / 20185549320903 : ℝ) := by norm_num
  have hL1 : (1952543430309 / 6250000000000 : ℝ) ≤ Real.log (1 + (23469488719869 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23469488719869 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-98795924727323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (30278323981355 / 108453202676328 : ℝ) ≤ (272251225172079 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6055664796271 / 10000000000000 : ℝ) ≤ (272251225172079 / 500000000000000 : ℝ) := by
    have hw : (7306650334541 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (6055664796271 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (6055664796271 / 10000000000000 : ℝ) / (1 + (7306650334541 / 6250000000000 : ℝ)) = (30278323981355 / 108453202676328 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102629387645073861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 6055664796271 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 6055664796271 : ℝ) = (6055664796271 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 20185549320903 : ℝ) ≤ (4928939562517 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102629387645073861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6055664796271 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (60556647962709 / 100000000000000 : ℝ)) ≤ (4928939562517 / 40000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_364 : ∀ t : ℝ, (23469488719869 / 64000000000000 : ℝ) < t → t ≤ (47022694589997 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-1773550417721720446632847 / 1250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (47022694589997 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_365
  have hV : (19047065916677930017865116666488221 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23469488719869 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_364 (Vfield_monotoneOn (show (23469488719869 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23469488719869 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_365 : (4766393328426051022621493830753451 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (47022694589997 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (47022694589997 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (15152656563379 / 25000000000000 : ℝ) ≤ Real.sqrt (47022694589997 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (47022694589997 / 128000000000000 : ℝ) ≤ (60610626253517 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (60610626253517 / 100000000000000 : ℝ) = (100000000000000 / 60610626253517 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (15152656563379 / 25000000000000 : ℝ) = (1875000000000 / 15152656563379 : ℝ) := by norm_num
  have hL1 : (15644269248357 / 50000000000000 : ℝ) ≤ Real.log (1 + (47022694589997 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((47022694589997 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-98620420105723 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (60610626253517 / 216934374821279 : ℝ) ≤ (272448653123559 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (60610626253517 / 100000000000000 : ℝ) ≤ (272448653123559 / 500000000000000 : ℝ) := by
    have hw : (116934374821279 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (60610626253517 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (60610626253517 / 100000000000000 : ℝ) / (1 + (116934374821279 / 100000000000000 : ℝ)) = (60610626253517 / 216934374821279 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102589902054777861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 60610626253517 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 60610626253517 : ℝ) = (60610626253517 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 15152656563379 : ℝ) ≤ (123114855371029 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102589902054777861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (60610626253517 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (15152656563379 / 25000000000000 : ℝ)) ≤ (123114855371029 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_365 : ∀ t : ℝ, (47022694589997 / 128000000000000 : ℝ) < t → t ≤ (1472075366883 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-28338089933848800902015263 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1472075366883 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_366
  have hV : (4766393328426051022621493830753451 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (47022694589997 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_365 (Vfield_monotoneOn (show (47022694589997 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (47022694589997 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_366 : (9542032812850914855112758066627841 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1472075366883 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1472075366883 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (30332278257689 / 50000000000000 : ℝ) ≤ Real.sqrt (1472075366883 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1472075366883 / 4000000000000 : ℝ) ≤ (60664556515379 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (60664556515379 / 100000000000000 : ℝ) = (100000000000000 / 60664556515379 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (30332278257689 / 50000000000000 : ℝ) = (3750000000000 / 30332278257689 : ℝ) := by norm_num
  have hL1 : (31336359229319 / 100000000000000 : ℝ) ≤ Real.log (1 + (1472075366883 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1472075366883 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24611305740821 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (60664556515379 / 216962337601501 : ℝ) ≤ (136322905539787 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (60664556515379 / 100000000000000 : ℝ) ≤ (136322905539787 / 250000000000000 : ℝ) := by
    have hw : (116962337601501 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (60664556515379 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (60664556515379 / 100000000000000 : ℝ) / (1 + (116962337601501 / 100000000000000 : ℝ)) = (60664556515379 / 216962337601501 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102550470463574861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 60664556515379 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 60664556515379 : ℝ) = (60664556515379 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 30332278257689 : ℝ) ≤ (6150325424669 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102550470463574861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (60664556515379 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (30332278257689 / 50000000000000 : ℝ)) ≤ (6150325424669 / 50000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_366 : ∀ t : ℝ, (1472075366883 / 4000000000000 : ℝ) < t → t ≤ (9438025778103 / 25600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-35374566926526472843841321 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9438025778103 / 25600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_367
  have hV : (9542032812850914855112758066627841 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1472075366883 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_366 (Vfield_monotoneOn (show (1472075366883 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1472075366883 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_367 : (19102542887747025451495417103987399 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9438025778103 / 25600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9438025778103 / 25600000000000 : ℝ) := by norm_num
  have hs1 : (60718438876271 / 100000000000000 : ℝ) ≤ Real.sqrt (9438025778103 / 25600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9438025778103 / 25600000000000 : ℝ) ≤ (3794902429767 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3794902429767 / 6250000000000 : ℝ) = (6250000000000 / 3794902429767 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (60718438876271 / 100000000000000 : ℝ) = (7500000000000 / 60718438876271 : ℝ) := by norm_num
  have hL1 : (31384157104629 / 100000000000000 : ℝ) ≤ Real.log (1 + (9438025778103 / 25600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9438025778103 / 25600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-196540664449 / 200000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (5059869906356 / 18082524474843 : ℝ) ≤ (13642134988293 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3794902429767 / 6250000000000 : ℝ) ≤ (13642134988293 / 25000000000000 : ℝ) := by
    have hw : (29247573424529 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (3794902429767 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3794902429767 / 6250000000000 : ℝ) / (1 + (29247573424529 / 25000000000000 : ℝ)) = (5059869906356 / 18082524474843 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102511092726317661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 3794902429767 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 3794902429767 : ℝ) = (3794902429767 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 60718438876271 : ℝ) ≤ (61449223585049 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102511092726317661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3794902429767 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (60718438876271 / 100000000000000 : ℝ)) ≤ (61449223585049 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_367 : ∀ t : ℝ, (9438025778103 / 25600000000000 : ℝ) < t → t ≤ (23636923020387 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-110396436281849917355127 / 78125000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23636923020387 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_368
  have hV : (19102542887747025451495417103987399 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9438025778103 / 25600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_367 (Vfield_monotoneOn (show (9438025778103 / 25600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9438025778103 / 25600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_368 : (19121005134782300375786282062208783 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (23636923020387 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23636923020387 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (60772273463607 / 100000000000000 : ℝ) ≤ Real.sqrt (23636923020387 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23636923020387 / 64000000000000 : ℝ) ≤ (7596534182951 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7596534182951 / 12500000000000 : ℝ) = (12500000000000 / 7596534182951 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (60772273463607 / 100000000000000 : ℝ) = (2500000000000 / 20257424487869 : ℝ) := by norm_num
  have hL1 : (7857983036121 / 25000000000000 : ℝ) ≤ Real.log (1 + (23636923020387 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23636923020387 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-98095746819499 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (60772273463608 / 217018243115915 : ℝ) ≤ (5460786398101 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7596534182951 / 12500000000000 : ℝ) ≤ (5460786398101 / 10000000000000 : ℝ) := by
    have hw : (23403648623183 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (7596534182951 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7596534182951 / 12500000000000 : ℝ) / (1 + (23403648623183 / 20000000000000 : ℝ)) = (60772273463608 / 217018243115915 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102471768698479661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 7596534182951 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 7596534182951 : ℝ) = (7596534182951 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 20257424487869 : ℝ) ≤ (122790670149031 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102471768698479661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7596534182951 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (60772273463607 / 100000000000000 : ℝ)) ≤ (122790670149031 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_368 : ∀ t : ℝ, (23636923020387 / 64000000000000 : ℝ) < t → t ≤ (47357563191033 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-28223583242864334045248517 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (47357563191033 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_369
  have hV : (19121005134782300375786282062208783 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23636923020387 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_368 (Vfield_monotoneOn (show (23636923020387 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23636923020387 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_369 : (19139452401615458292222968129960177 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (47357563191033 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (47357563191033 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (60826060404233 / 100000000000000 : ℝ) ≤ Real.sqrt (47357563191033 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (47357563191033 / 128000000000000 : ℝ) ≤ (30413030202117 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (30413030202117 / 50000000000000 : ℝ) = (50000000000000 / 30413030202117 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (60826060404233 / 100000000000000 : ℝ) = (7500000000000 / 60826060404233 : ℝ) := by norm_num
  have hL1 : (15739842185347 / 50000000000000 : ℝ) ≤ Real.log (1 + (47357563191033 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((47357563191033 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-97921465684001 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (60826060404234 / 217046185859683 : ℝ) ≤ (273235672216681 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (30413030202117 / 50000000000000 : ℝ) ≤ (273235672216681 / 500000000000000 : ℝ) := by
    have hw : (117046185859683 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (30413030202117 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (30413030202117 / 50000000000000 : ℝ) / (1 + (117046185859683 / 100000000000000 : ℝ)) = (60826060404234 / 217046185859683 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102432498236153461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 30413030202117 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 30413030202117 : ℝ) = (30413030202117 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 60826060404233 : ℝ) ≤ (122683176185701 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102432498236153461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (30413030202117 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (60826060404233 / 100000000000000 : ℝ)) ≤ (122683176185701 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_369 : ∀ t : ℝ, (47357563191033 / 128000000000000 : ℝ) < t → t ≤ (11860320085323 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-35232414614698425992719703 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11860320085323 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_370
  have hV : (19139452401615458292222968129960177 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (47357563191033 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_369 (Vfield_monotoneOn (show (47357563191033 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (47357563191033 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_370 : (4789471180730162033321503342012821 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (11860320085323 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11860320085323 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (15219949956109 / 25000000000000 : ℝ) ≤ Real.sqrt (11860320085323 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11860320085323 / 32000000000000 : ℝ) ≤ (60879799824437 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (60879799824437 / 100000000000000 : ℝ) = (100000000000000 / 60879799824437 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (15219949956109 / 25000000000000 : ℝ) = (1875000000000 / 15219949956109 : ℝ) := by norm_num
  have hL1 : (7881853451259 / 25000000000000 : ℝ) ≤ Real.log (1 + (11860320085323 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11860320085323 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-48873743879641 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (60879799824437 / 217074121934198 : ℝ) ≤ (273431757417217 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (60879799824437 / 100000000000000 : ℝ) ≤ (273431757417217 / 500000000000000 : ℝ) := by
    have hw : (58537060967099 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (60879799824437 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (60879799824437 / 100000000000000 : ℝ) / (1 + (58537060967099 / 50000000000000 : ℝ)) = (60879799824437 / 217074121934198 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102393281196046261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 60879799824437 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 60879799824437 : ℝ) = (60879799824437 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 15219949956109 : ℝ) ≤ (24515192808649 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102393281196046261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (60879799824437 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (15219949956109 / 25000000000000 : ℝ)) ≤ (24515192808649 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_370 : ∀ t : ℝ, (11860320085323 / 32000000000000 : ℝ) < t → t ≤ (47524997491551 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-17592828175159491727008347 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (47524997491551 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_371
  have hV : (4789471180730162033321503342012821 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11860320085323 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_370 (Vfield_monotoneOn (show (11860320085323 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11860320085323 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_371 : (3835260426647758812333086012686541 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (47524997491551 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (47524997491551 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (12186698369989 / 20000000000000 : ℝ) ≤ Real.sqrt (47524997491551 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (47524997491551 / 128000000000000 : ℝ) ≤ (30466745924973 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (30466745924973 / 50000000000000 : ℝ) = (50000000000000 / 30466745924973 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (12186698369989 / 20000000000000 : ℝ) = (1500000000000 / 12186698369989 : ℝ) := by norm_num
  have hL1 : (31575120469257 / 100000000000000 : ℝ) ≤ Real.log (1 + (47524997491551 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((47524997491551 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-48786905996067 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (60933491849946 / 217102051344233 : ℝ) ≤ (13681378811003 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (30466745924973 / 50000000000000 : ℝ) ≤ (13681378811003 / 25000000000000 : ℝ) := by
    have hw : (117102051344233 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (30466745924973 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (30466745924973 / 50000000000000 : ℝ) / (1 + (117102051344233 / 100000000000000 : ℝ)) = (60933491849946 / 217102051344233 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102354117435477661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 30466745924973 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 30466745924973 : ℝ) = (30466745924973 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 12186698369989 : ℝ) ≤ (24493806498471 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102354117435477661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (30466745924973 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (12186698369989 / 20000000000000 : ℝ)) ≤ (24493806498471 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_371 : ∀ t : ℝ, (47524997491551 / 128000000000000 : ℝ) < t → t ≤ (4760871464181 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-140556779803738587370508533 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4760871464181 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_372
  have hV : (3835260426647758812333086012686541 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (47524997491551 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_371 (Vfield_monotoneOn (show (47524997491551 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (47524997491551 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_372 : (9597352333489786469364862886848161 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (4760871464181 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4760871464181 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (30493568302969 / 50000000000000 : ℝ) ≤ Real.sqrt (4760871464181 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4760871464181 / 12800000000000 : ℝ) ≤ (60987136605939 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (60987136605939 / 100000000000000 : ℝ) = (100000000000000 / 60987136605939 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (30493568302969 / 50000000000000 : ℝ) = (3750000000000 / 30493568302969 : ℝ) := by norm_num
  have hL1 : (1976425274067 / 6250000000000 : ℝ) ≤ Real.log (1 + (4760871464181 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4760871464181 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-97400437334829 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (60987136605939 / 217129974094556 : ℝ) ≤ (8556972791737 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (60987136605939 / 100000000000000 : ℝ) ≤ (8556972791737 / 15625000000000 : ℝ) := by
    have hw : (29282493523639 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (60987136605939 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (60987136605939 / 100000000000000 : ℝ) / (1 + (29282493523639 / 25000000000000 : ℝ)) = (60987136605939 / 217129974094556 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102315006812372861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 60987136605939 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 60987136605939 : ℝ) = (60987136605939 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 30493568302969 : ℝ) ≤ (122362380311211 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102315006812372861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (60987136605939 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (30493568302969 / 50000000000000 : ℝ)) ≤ (122362380311211 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_372 : ∀ t : ℝ, (4760871464181 / 12800000000000 : ℝ) < t → t ≤ (47692431792069 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-140372086733382787260768173 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (47692431792069 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_373
  have hV : (9597352333489786469364862886848161 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4760871464181 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_372 (Vfield_monotoneOn (show (4760871464181 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4760871464181 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_373 : (240163654480249060417553302366297 / 62500000000000000000000000000000 : ℝ) ≤ Vfield (47692431792069 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (47692431792069 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (763009177713 / 1250000000000 : ℝ) ≤ Real.sqrt (47692431792069 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (47692431792069 / 128000000000000 : ℝ) ≤ (61040734217041 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (61040734217041 / 100000000000000 : ℝ) = (100000000000000 / 61040734217041 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (763009177713 / 1250000000000 : ℝ) = (31250000000 / 254336392571 : ℝ) := by norm_num
  have hL1 : (6334093114833 / 20000000000000 : ℝ) ≤ Real.log (1 + (47692431792069 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((47692431792069 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3889094509803 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (61040734217041 / 217157890189928 : ℝ) ≤ (274018417471133 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (61040734217041 / 100000000000000 : ℝ) ≤ (274018417471133 / 500000000000000 : ℝ) := by
    have hw : (14644736273741 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (61040734217041 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (61040734217041 / 100000000000000 : ℝ) / (1 + (14644736273741 / 12500000000000 : ℝ)) = (61040734217041 / 217157890189928 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102275949185263061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 61040734217041 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 61040734217041 : ℝ) = (61040734217041 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (31250000000 / 254336392571 : ℝ) ≤ (30564001571359 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102275949185263061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (61040734217041 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (763009177713 / 1250000000000 : ℝ)) ≤ (30564001571359 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_373 : ∀ t : ℝ, (47692431792069 / 128000000000000 : ℝ) < t → t ≤ (5972018617791 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-35047128339817078111185689 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5972018617791 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_374
  have hV : (240163654480249060417553302366297 / 62500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (47692431792069 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_373 (Vfield_monotoneOn (show (47692431792069 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (47692431792069 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_374 : (19231465241706725373246830208872539 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (5972018617791 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5972018617791 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (61094284807331 / 100000000000000 : ℝ) ≤ Real.sqrt (5972018617791 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5972018617791 / 16000000000000 : ℝ) ≤ (15273571201833 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (15273571201833 / 25000000000000 : ℝ) = (25000000000000 / 15273571201833 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (61094284807331 / 100000000000000 : ℝ) = (7500000000000 / 61094284807331 : ℝ) := by norm_num
  have hL1 : (31718104058189 / 100000000000000 : ℝ) ≤ Real.log (1 + (5972018617791 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5972018617791 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-48527293592993 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (30547142403666 / 108592899817553 : ℝ) ≤ (274213441331051 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (15273571201833 / 25000000000000 : ℝ) ≤ (274213441331051 / 500000000000000 : ℝ) := by
    have hw : (58592899817553 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (15273571201833 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (15273571201833 / 25000000000000 : ℝ) / (1 + (58592899817553 / 50000000000000 : ℝ)) = (30547142403666 / 108592899817553 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102236944413279461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 15273571201833 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 15273571201833 : ℝ) = (15273571201833 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 61094284807331 : ℝ) ≤ (30537477302007 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102236944413279461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (15273571201833 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (61094284807331 / 100000000000000 : ℝ)) ≤ (30537477302007 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_374 : ∀ t : ℝ, (5972018617791 / 16000000000000 : ℝ) < t → t ≤ (47859866092587 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-17500753596452019866218911 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (47859866092587 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_375
  have hV : (19231465241706725373246830208872539 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5972018617791 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_374 (Vfield_monotoneOn (show (5972018617791 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5972018617791 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_375 : (4812455837714235752548322034486903 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (47859866092587 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (47859866092587 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (15286947125087 / 25000000000000 : ℝ) ≤ Real.sqrt (47859866092587 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (47859866092587 / 128000000000000 : ℝ) ≤ (61147788500349 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (61147788500349 / 100000000000000 : ℝ) = (100000000000000 / 61147788500349 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (15286947125087 / 25000000000000 : ℝ) = (1875000000000 / 15286947125087 : ℝ) := by norm_num
  have hL1 : (1985357491173 / 6250000000000 : ℝ) ≤ Real.log (1 + (47859866092587 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((47859866092587 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-96882109626039 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (20382596166783 / 72404567478280 : ℝ) ≤ (54881640323341 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (61147788500349 / 100000000000000 : ℝ) ≤ (54881640323341 / 100000000000000 : ℝ) := by
    have hw : (2930342560871 / 2500000000000 : ℝ) ≤ Real.sqrt (1 + (61147788500349 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (61147788500349 / 100000000000000 : ℝ) / (1 + (2930342560871 / 2500000000000 : ℝ)) = (20382596166783 / 72404567478280 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102197992356148661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 61147788500349 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 61147788500349 : ℝ) = (61147788500349 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 15286947125087 : ℝ) ≤ (61022043939651 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102197992356148661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (61147788500349 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (15286947125087 / 25000000000000 : ℝ)) ≤ (61022043939651 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_375 : ∀ t : ℝ, (47859866092587 / 128000000000000 : ℝ) < t → t ≤ (23971791621423 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-139824603820775193451400039 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23971791621423 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_376
  have hV : (4812455837714235752548322034486903 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (47859866092587 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_375 (Vfield_monotoneOn (show (47859866092587 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (47859866092587 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_376 : (19268166719757625128468742087372903 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (23971791621423 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23971791621423 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (61201245419087 / 100000000000000 : ℝ) ≤ Real.sqrt (23971791621423 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23971791621423 / 64000000000000 : ℝ) ≤ (3825077838693 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3825077838693 / 6250000000000 : ℝ) = (6250000000000 / 3825077838693 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (61201245419087 / 100000000000000 : ℝ) = (7500000000000 / 61201245419087 : ℝ) := by norm_num
  have hL1 : (7953328249373 / 25000000000000 : ℝ) ≤ Real.log (1 + (23971791621423 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23971791621423 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-96709929039041 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (61201245419088 / 217241598593875 : ℝ) ≤ (274602699026489 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3825077838693 / 6250000000000 : ℝ) ≤ (274602699026489 / 500000000000000 : ℝ) := by
    have hw : (937932788751 / 800000000000 : ℝ) ≤ Real.sqrt (1 + (3825077838693 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3825077838693 / 6250000000000 : ℝ) / (1 + (937932788751 / 800000000000 : ℝ)) = (61201245419088 / 217241598593875 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102159092874191861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 3825077838693 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 3825077838693 : ℝ) = (3825077838693 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 61201245419087 : ℝ) ≤ (3048463527671 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102159092874191861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3825077838693 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (61201245419087 / 100000000000000 : ℝ)) ≤ (3048463527671 / 25000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_376 : ∀ t : ℝ, (23971791621423 / 64000000000000 : ℝ) < t → t ≤ (9605460078621 / 25600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-139644210973282918920749143 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9605460078621 / 25600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_377
  have hV : (19268166719757625128468742087372903 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23971791621423 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_376 (Vfield_monotoneOn (show (23971791621423 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23971791621423 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_377 : (19286495382167097183857206420834383 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9605460078621 / 25600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9605460078621 / 25600000000000 : ℝ) := by norm_num
  have hs1 : (61254655686007 / 100000000000000 : ℝ) ≤ Real.sqrt (9605460078621 / 25600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9605460078621 / 25600000000000 : ℝ) ≤ (7656831960751 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7656831960751 / 12500000000000 : ℝ) = (12500000000000 / 7656831960751 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (61254655686007 / 100000000000000 : ℝ) = (7500000000000 / 61254655686007 : ℝ) := by norm_num
  have hL1 : (15930441747961 / 50000000000000 : ℝ) ≤ Real.log (1 + (9605460078621 / 25600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9605460078621 / 25600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-9653804440409 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (61254655686008 / 217269488116949 : ℝ) ≤ (274796934255849 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7656831960751 / 12500000000000 : ℝ) ≤ (274796934255849 / 500000000000000 : ℝ) := by
    have hw : (117269488116949 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (7656831960751 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7656831960751 / 12500000000000 : ℝ) / (1 + (117269488116949 / 100000000000000 : ℝ)) = (61254655686008 / 217269488116949 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102120245828319861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 7656831960751 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 7656831960751 : ℝ) = (7656831960751 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 61254655686007 : ℝ) ≤ (12183326770543 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102120245828319861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7656831960751 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (61254655686007 / 100000000000000 : ℝ)) ≤ (12183326770543 / 100000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_377 : ∀ t : ℝ, (9605460078621 / 25600000000000 : ℝ) < t → t ≤ (12027754385841 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-34866206045715412452886681 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (12027754385841 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_378
  have hV : (19286495382167097183857206420834383 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9605460078621 / 25600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_377 (Vfield_monotoneOn (show (9605460078621 / 25600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9605460078621 / 25600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_378 : (3860961874343229022683457617757783 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (12027754385841 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (12027754385841 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (12261603884607 / 20000000000000 : ℝ) ≤ Real.sqrt (12027754385841 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (12027754385841 / 32000000000000 : ℝ) ≤ (15327004855759 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (15327004855759 / 25000000000000 : ℝ) = (25000000000000 / 15327004855759 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (12261603884607 / 20000000000000 : ℝ) = (500000000000 / 4087201294869 : ℝ) := by norm_num
  have hL1 : (31908431375589 / 100000000000000 : ℝ) ≤ Real.log (1 + (12027754385841 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((12027754385841 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-96366454705537 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (15327004855759 / 54324342752199 : ℝ) ≤ (34373863499663 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (15327004855759 / 25000000000000 : ℝ) ≤ (34373863499663 / 62500000000000 : ℝ) := by
    have hw : (29324342752199 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (15327004855759 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (15327004855759 / 25000000000000 : ℝ) / (1 + (29324342752199 / 25000000000000 : ℝ)) = (15327004855759 / 54324342752199 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102081451080028861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 15327004855759 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 15327004855759 : ℝ) = (15327004855759 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 4087201294869 : ℝ) ≤ (121728266497009 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102081451080028861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (15327004855759 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (12261603884607 / 20000000000000 : ℝ)) ≤ (121728266497009 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_378 : ∀ t : ℝ, (12027754385841 / 32000000000000 : ℝ) < t → t ≤ (48194734693623 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-34821604693620753662426341 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (48194734693623 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_379
  have hV : (3860961874343229022683457617757783 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (12027754385841 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_378 (Vfield_monotoneOn (show (12027754385841 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (12027754385841 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_379 : (19323108721907991648061524746050023 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (48194734693623 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (48194734693623 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (61361336751567 / 100000000000000 : ℝ) ≤ Real.sqrt (48194734693623 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (48194734693623 / 128000000000000 : ℝ) ≤ (3835083546973 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3835083546973 / 6250000000000 : ℝ) = (6250000000000 / 3835083546973 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (61361336751567 / 100000000000000 : ℝ) = (2500000000000 / 20453778917189 : ℝ) := by norm_num
  have hL1 : (31955956657991 / 100000000000000 : ℝ) ≤ Real.log (1 + (48194734693623 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((48194734693623 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-96195158932957 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (61361336751568 / 217325247274145 : ℝ) ≤ (137592310470227 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3835083546973 / 6250000000000 : ℝ) ≤ (137592310470227 / 250000000000000 : ℝ) := by
    have hw : (23465049454829 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (3835083546973 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3835083546973 / 6250000000000 : ℝ) / (1 + (23465049454829 / 20000000000000 : ℝ)) = (61361336751568 / 217325247274145 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102042708491398861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 3835083546973 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 3835083546973 : ℝ) = (3835083546973 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 20453778917189 : ℝ) ≤ (121623536310609 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102042708491398861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3835083546973 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (61361336751567 / 100000000000000 : ℝ)) ≤ (121623536310609 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_379 : ∀ t : ℝ, (48194734693623 / 128000000000000 : ℝ) < t → t ≤ (24139225921941 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-139108971339924110431061977 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (24139225921941 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_380
  have hV : (19323108721907991648061524746050023 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (48194734693623 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_379 (Vfield_monotoneOn (show (48194734693623 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (48194734693623 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_380 : (2417674183264870412097291919166371 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (24139225921941 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (24139225921941 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (7676825974059 / 12500000000000 : ℝ) ≤ Real.sqrt (24139225921941 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (24139225921941 / 64000000000000 : ℝ) ≤ (61414607792473 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (61414607792473 / 100000000000000 : ℝ) = (100000000000000 / 61414607792473 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7676825974059 / 12500000000000 : ℝ) = (312500000000 / 2558941991353 : ℝ) := by norm_num
  have hL1 : (32003459364597 / 100000000000000 : ℝ) ≤ Real.log (1 + (24139225921941 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((24139225921941 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6001509755069 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (4724200599421 / 16719470532132 : ℝ) ≤ (27537807377201 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (61414607792473 / 100000000000000 : ℝ) ≤ (27537807377201 / 50000000000000 : ℝ) := by
    have hw : (29338279229429 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (61414607792473 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (61414607792473 / 100000000000000 : ℝ) / (1 + (29338279229429 / 25000000000000 : ℝ)) = (4724200599421 / 16719470532132 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102004017925087661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 61414607792473 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 61414607792473 : ℝ) = (61414607792473 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (312500000000 / 2558941991353 : ℝ) ≤ (24303815196461 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102004017925087661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (61414607792473 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7676825974059 / 12500000000000 : ℝ)) ≤ (24303815196461 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_380 : ∀ t : ℝ, (24139225921941 / 64000000000000 : ℝ) < t → t ≤ (48362168994141 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-138932459643440611339002959 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (48362168994141 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_381
  have hV : (2417674183264870412097291919166371 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (24139225921941 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_380 (Vfield_monotoneOn (show (24139225921941 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (24139225921941 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_381 : (1209978977349990846838978552849239 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (48362168994141 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (48362168994141 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (3841739541631 / 6250000000000 : ℝ) ≤ Real.sqrt (48362168994141 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (48362168994141 / 128000000000000 : ℝ) ≤ (61467832666097 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (61467832666097 / 100000000000000 : ℝ) = (100000000000000 / 61467832666097 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3841739541631 / 6250000000000 : ℝ) = (468750000000 / 3841739541631 : ℝ) := by norm_num
  have hL1 : (6410187903369 / 20000000000000 : ℝ) ≤ Real.log (1 + (48362168994141 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((48362168994141 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-23963361287471 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (61467832666097 / 217380979944228 : ℝ) ≤ (137785633587899 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (61467832666097 / 100000000000000 : ℝ) ≤ (137785633587899 / 250000000000000 : ℝ) := by
    have hw : (29345244986057 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (61467832666097 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (61467832666097 / 100000000000000 : ℝ) / (1 + (29345244986057 / 25000000000000 : ℝ)) = (61467832666097 / 217380979944228 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101965379244330061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 61467832666097 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 61467832666097 : ℝ) = (61467832666097 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (468750000000 / 3841739541631 : ℝ) ≤ (30353721088789 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101965379244330061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (61467832666097 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3841739541631 / 6250000000000 : ℝ)) ≤ (30353721088789 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_381 : ∀ t : ℝ, (48362168994141 / 128000000000000 : ℝ) < t → t ≤ (121114715361 / 320000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-34689215634097777936978743 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (121114715361 / 320000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_382
  have hV : (1209978977349990846838978552849239 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (48362168994141 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_381 (Vfield_monotoneOn (show (48362168994141 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (48362168994141 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_382 : (19377919269475546548520191008405247 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (121114715361 / 320000000000 : ℝ) := by
  have hp : (0 : ℝ) < (121114715361 / 320000000000 : ℝ) := by norm_num
  have hs1 : (61521011492263 / 100000000000000 : ℝ) ≤ Real.sqrt (121114715361 / 320000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (121114715361 / 320000000000 : ℝ) ≤ (7690126436533 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7690126436533 / 12500000000000 : ℝ) = (12500000000000 / 7690126436533 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (61521011492263 / 100000000000000 : ℝ) = (7500000000000 / 61521011492263 : ℝ) := by norm_num
  have hL1 : (2006149821009 / 6250000000000 : ℝ) ≤ Real.log (1 + (121114715361 / 320000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((121114715361 / 320000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-11960378143039 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (30760505746132 / 108704418179195 : ℝ) ≤ (137882100916391 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7690126436533 / 12500000000000 : ℝ) ≤ (137882100916391 / 250000000000000 : ℝ) := by
    have hw : (11740883635839 / 10000000000000 : ℝ) ≤ Real.sqrt (1 + (7690126436533 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7690126436533 / 12500000000000 : ℝ) / (1 + (11740883635839 / 10000000000000 : ℝ)) = (30760505746132 / 108704418179195 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101926792312933261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 7690126436533 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 7690126436533 : ℝ) = (7690126436533 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 61521011492263 : ℝ) ≤ (24262192055831 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101926792312933261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7690126436533 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (61521011492263 / 100000000000000 : ℝ)) ≤ (24262192055831 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_382 : ∀ t : ℝ, (121114715361 / 320000000000 : ℝ) < t → t ≤ (48529603294659 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-1732276998497288780814161 / 1250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (48529603294659 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_383
  have hV : (19377919269475546548520191008405247 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (121114715361 / 320000000000 : ℝ) := by norm_num
    refine le_trans V_pt_382 (Vfield_monotoneOn (show (121114715361 / 320000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (121114715361 / 320000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_383 : (19396160394746625866499762450911089 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (48529603294659 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (48529603294659 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (61574144390281 / 100000000000000 : ℝ) ≤ Real.sqrt (48529603294659 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (48529603294659 / 128000000000000 : ℝ) ≤ (30787072195141 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (30787072195141 / 50000000000000 : ℝ) = (50000000000000 / 30787072195141 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (61574144390281 / 100000000000000 : ℝ) = (7500000000000 / 61574144390281 : ℝ) := by norm_num
  have hL1 : (8036458060967 / 25000000000000 : ℝ) ≤ Real.log (1 + (48529603294659 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((48529603294659 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-19102579014897 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (30787072195141 / 108718343082454 : ℝ) ≤ (68989219605271 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (30787072195141 / 50000000000000 : ℝ) ≤ (68989219605271 / 125000000000000 : ℝ) := by
    have hw : (29359171541227 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (30787072195141 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (30787072195141 / 50000000000000 : ℝ) / (1 + (29359171541227 / 25000000000000 : ℝ)) = (30787072195141 / 108718343082454 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101888256995272861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 30787072195141 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 30787072195141 : ℝ) = (30787072195141 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 61574144390281 : ℝ) ≤ (30301825652793 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101888256995272861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (30787072195141 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (61574144390281 / 100000000000000 : ℝ)) ≤ (30301825652793 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_383 : ∀ t : ℝ, (48529603294659 / 128000000000000 : ℝ) < t → t ≤ (24306660222459 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-69204166236932677215170537 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (24306660222459 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_384
  have hV : (19396160394746625866499762450911089 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (48529603294659 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_383 (Vfield_monotoneOn (show (48529603294659 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (48529603294659 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_384 : (9707193523144637707375491111188199 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (24306660222459 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (24306660222459 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (30813615739471 / 50000000000000 : ℝ) ≤ Real.sqrt (24306660222459 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (24306660222459 / 64000000000000 : ℝ) ≤ (61627231478943 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (61627231478943 / 100000000000000 : ℝ) = (100000000000000 / 61627231478943 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (30813615739471 / 50000000000000 : ℝ) = (3750000000000 / 30813615739471 : ℝ) := by norm_num
  have hL1 : (16096622430683 / 50000000000000 : ℝ) ≤ Real.log (1 + (24306660222459 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((24306660222459 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-95343053955541 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (6847470164327 / 24162725485387 : ℝ) ≤ (276149297615989 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (61627231478943 / 100000000000000 : ℝ) ≤ (276149297615989 / 500000000000000 : ℝ) := by
    have hw : (117464529368483 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (61627231478943 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (61627231478943 / 100000000000000 : ℝ) / (1 + (117464529368483 / 100000000000000 : ℝ)) = (6847470164327 / 24162725485387 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101849773156291861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 61627231478943 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 61627231478943 : ℝ) = (61627231478943 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 30813615739471 : ℝ) ≤ (60551955107453 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101849773156291861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (61627231478943 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (30813615739471 / 50000000000000 : ℝ)) ≤ (60551955107453 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_384 : ∀ t : ℝ, (24306660222459 / 64000000000000 : ℝ) < t → t ≤ (48697037595177 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-138235361993992281663353053 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (48697037595177 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_385
  have hV : (9707193523144637707375491111188199 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (24306660222459 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_384 (Vfield_monotoneOn (show (24306660222459 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (24306660222459 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_385 : (1943259925685732091971404589210157 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (48697037595177 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (48697037595177 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (6168027287653 / 10000000000000 : ℝ) ≤ Real.sqrt (48697037595177 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (48697037595177 / 128000000000000 : ℝ) ≤ (61680272876531 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (61680272876531 / 100000000000000 : ℝ) = (100000000000000 / 61680272876531 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6168027287653 / 10000000000000 : ℝ) = (750000000000 / 6168027287653 : ℝ) := by norm_num
  have hL1 : (16120317504977 / 50000000000000 : ℝ) ≤ Real.log (1 + (48697037595177 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((48697037595177 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-95173500807631 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (61680272876531 / 217492365973808 : ℝ) ≤ (276341460089987 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (61680272876531 / 100000000000000 : ℝ) ≤ (276341460089987 / 500000000000000 : ℝ) := by
    have hw : (7343272873363 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (61680272876531 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (61680272876531 / 100000000000000 : ℝ) / (1 + (7343272873363 / 6250000000000 : ℝ)) = (61680272876531 / 217492365973808 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101811340661492261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 61680272876531 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 61680272876531 : ℝ) = (61680272876531 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 6168027287653 : ℝ) ≤ (4840031278433 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101811340661492261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (61680272876531 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6168027287653 / 10000000000000 : ℝ)) ≤ (4840031278433 / 40000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_385 : ∀ t : ℝ, (48697037595177 / 128000000000000 : ℝ) < t → t ≤ (12195188686359 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-69031615466044816499749187 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (12195188686359 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_386
  have hV : (1943259925685732091971404589210157 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (48697037595177 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_385 (Vfield_monotoneOn (show (48697037595177 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (48697037595177 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_386 : (1215674816192508175692785743517969 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (12195188686359 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (12195188686359 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (3858329293801 / 6250000000000 : ℝ) ≤ Real.sqrt (12195188686359 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (12195188686359 / 32000000000000 : ℝ) ≤ (61733268700817 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (61733268700817 / 100000000000000 : ℝ) = (100000000000000 / 61733268700817 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3858329293801 / 6250000000000 : ℝ) = (468750000000 / 3858329293801 : ℝ) := by norm_num
  have hL1 : (16144001355459 / 50000000000000 : ℝ) ≤ Real.log (1 + (12195188686359 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((12195188686359 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-95004234655877 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (61733268700817 / 217520195985572 : ℝ) ≤ (276533366512749 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (61733268700817 / 100000000000000 : ℝ) ≤ (276533366512749 / 500000000000000 : ℝ) := by
    have hw : (29380048996393 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (61733268700817 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (61733268700817 / 100000000000000 : ℝ) / (1 + (29380048996393 / 25000000000000 : ℝ)) = (61733268700817 / 217520195985572 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101772959376939861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 61733268700817 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 61733268700817 : ℝ) = (61733268700817 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (468750000000 / 3858329293801 : ℝ) ≤ (60448958363063 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101772959376939861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (61733268700817 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3858329293801 / 6250000000000 : ℝ)) ≤ (60448958363063 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_386 : ∀ t : ℝ, (12195188686359 / 32000000000000 : ℝ) < t → t ≤ (9772894379139 / 25600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-137891922543132017105167529 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9772894379139 / 25600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_387
  have hV : (1215674816192508175692785743517969 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (12195188686359 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_386 (Vfield_monotoneOn (show (12195188686359 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (12195188686359 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_387 : (1946898048546641249779050364406483 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (9772894379139 / 25600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9772894379139 / 25600000000000 : ℝ) := by norm_num
  have hs1 : (6178621906907 / 10000000000000 : ℝ) ≤ Real.sqrt (9772894379139 / 25600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9772894379139 / 25600000000000 : ℝ) ≤ (61786219069071 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (61786219069071 / 100000000000000 : ℝ) = (100000000000000 / 61786219069071 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6178621906907 / 10000000000000 : ℝ) = (750000000000 / 6178621906907 : ℝ) := by norm_num
  have hL1 : (32335347985513 / 100000000000000 : ℝ) ≤ Real.log (1 + (9772894379139 / 25600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9772894379139 / 25600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-23708813632587 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (20595406356357 / 72516006469486 : ℝ) ≤ (55345003510237 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (61786219069071 / 100000000000000 : ℝ) ≤ (55345003510237 / 100000000000000 : ℝ) := by
    have hw : (58774009704229 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (61786219069071 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (61786219069071 / 100000000000000 : ℝ) / (1 + (58774009704229 / 50000000000000 : ℝ)) = (20595406356357 / 72516006469486 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101734629169252661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 61786219069071 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 61786219069071 : ℝ) = (61786219069071 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 6178621906907 : ℝ) ≤ (7549707087167 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101734629169252661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (61786219069071 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6178621906907 / 10000000000000 : ℝ)) ≤ (7549707087167 / 62500000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_387 : ∀ t : ℝ, (9772894379139 / 25600000000000 : ℝ) < t → t ≤ (24474094522977 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-137721420796117784973700357 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (24474094522977 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_388
  have hV : (1946898048546641249779050364406483 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9772894379139 / 25600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_387 (Vfield_monotoneOn (show (9772894379139 / 25600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9772894379139 / 25600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_388 : (19487149568403172416100369445522371 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (24474094522977 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (24474094522977 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (61839124098059 / 100000000000000 : ℝ) ≤ Real.sqrt (24474094522977 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (24474094522977 / 64000000000000 : ℝ) ≤ (3091956204903 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3091956204903 / 5000000000000 : ℝ) = (5000000000000 / 3091956204903 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (61839124098059 / 100000000000000 : ℝ) = (7500000000000 / 61839124098059 : ℝ) := by norm_num
  have hL1 : (6476534170993 / 20000000000000 : ℝ) ≤ Real.log (1 + (24474094522977 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((24474094522977 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-94666559466017 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (5153260341505 / 18131319687262 : ℝ) ≤ (138458206934719 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3091956204903 / 5000000000000 : ℝ) ≤ (138458206934719 / 250000000000000 : ℝ) := by
    have hw : (14696979530893 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (3091956204903 / 5000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3091956204903 / 5000000000000 : ℝ) / (1 + (14696979530893 / 12500000000000 : ℝ)) = (5153260341505 / 18131319687262 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101696349905602061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 3091956204903 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 3091956204903 : ℝ) = (3091956204903 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 61839124098059 : ℝ) ≤ (7543310678559 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101696349905602061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3091956204903 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (61839124098059 / 100000000000000 : ℝ)) ≤ (7543310678559 / 62500000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_388 : ∀ t : ℝ, (24474094522977 / 64000000000000 : ℝ) < t → t ≤ (6139452918309 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-137382776407759414630251603 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (6139452918309 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_389
  have hV : (19487149568403172416100369445522371 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (24474094522977 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_388 (Vfield_monotoneOn (show (24474094522977 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (24474094522977 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_389 : (19523444832870957425793937460768197 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (6139452918309 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (6139452918309 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (61944798602813 / 100000000000000 : ℝ) ≤ Real.sqrt (6139452918309 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (6139452918309 / 16000000000000 : ℝ) ≤ (30972399301407 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (30972399301407 / 50000000000000 : ℝ) = (50000000000000 / 30972399301407 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (61944798602813 / 100000000000000 : ℝ) = (7500000000000 / 61944798602813 : ℝ) := by norm_num
  have hL1 : (32477249463193 / 100000000000000 : ℝ) ≤ Real.log (1 + (6139452918309 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((6139452918309 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-94330020685201 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (30972399301407 / 108815725095299 : ℝ) ≤ (11091937799529 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (30972399301407 / 50000000000000 : ℝ) ≤ (11091937799529 / 20000000000000 : ℝ) := by
    have hw : (58815725095299 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (30972399301407 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (30972399301407 / 50000000000000 : ℝ) / (1 + (58815725095299 / 50000000000000 : ℝ)) = (30972399301407 / 108815725095299 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101619943681844661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 30972399301407 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 30972399301407 : ℝ) = (30972399301407 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 61944798602813 : ℝ) ≤ (120489063757407 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101619943681844661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (30972399301407 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (61944798602813 / 100000000000000 : ℝ)) ≤ (120489063757407 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_389 : ∀ t : ℝ, (6139452918309 / 16000000000000 : ℝ) < t → t ≤ (4928305764699 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-137047182178219535582382819 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4928305764699 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_390
  have hV : (19523444832870957425793937460768197 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (6139452918309 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_389 (Vfield_monotoneOn (show (6139452918309 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (6139452918309 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_390 : (4889920777293329435666637765512349 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (4928305764699 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4928305764699 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (15512573284821 / 25000000000000 : ℝ) ≤ Real.sqrt (4928305764699 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4928305764699 / 12800000000000 : ℝ) ≤ (12410058627857 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (12410058627857 / 20000000000000 : ℝ) = (20000000000000 / 12410058627857 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (15512573284821 / 25000000000000 : ℝ) = (625000000000 / 5170857761607 : ℝ) := by norm_num
  have hL1 : (8142934676201 / 25000000000000 : ℝ) ≤ Real.log (1 + (4928305764699 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4928305764699 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-46997305345077 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (12410058627857 / 43537407570649 : ℝ) ≤ (69419866281897 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (12410058627857 / 20000000000000 : ℝ) ≤ (69419866281897 / 125000000000000 : ℝ) := by
    have hw : (23537407570649 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (12410058627857 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (12410058627857 / 20000000000000 : ℝ) / (1 + (23537407570649 / 20000000000000 : ℝ)) = (12410058627857 / 43537407570649 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101543739653972061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 12410058627857 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 12410058627857 : ℝ) = (12410058627857 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (625000000000 / 5170857761607 : ℝ) ≤ (30071546670469 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101543739653972061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (12410058627857 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (15512573284821 / 25000000000000 : ℝ)) ≤ (30071546670469 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_390 : ∀ t : ℝ, (4928305764699 / 12800000000000 : ℝ) < t → t ≤ (12362622986877 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-136714531412886259203207971 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (12362622986877 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_391
  have hV : (4889920777293329435666637765512349 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4928305764699 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_390 (Vfield_monotoneOn (show (4928305764699 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4928305764699 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_391 : (2449483081512030866858064361680851 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (12362622986877 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (12362622986877 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (7769451077979 / 12500000000000 : ℝ) ≤ Real.sqrt (12362622986877 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (12362622986877 / 32000000000000 : ℝ) ≤ (62155608623833 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (62155608623833 / 100000000000000 : ℝ) = (100000000000000 / 62155608623833 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7769451077979 / 12500000000000 : ℝ) = (312500000000 / 2589817025993 : ℝ) := by norm_num
  have hL1 : (32666138748523 / 100000000000000 : ℝ) ≤ Real.log (1 + (12362622986877 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((12362622986877 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-18732064386811 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (62155608623833 / 217742599272307 : ℝ) ≤ (278059479502799 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (62155608623833 / 100000000000000 : ℝ) ≤ (278059479502799 / 500000000000000 : ℝ) := by
    have hw : (117742599272307 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (62155608623833 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (62155608623833 / 100000000000000 : ℝ) / (1 + (117742599272307 / 100000000000000 : ℝ)) = (62155608623833 / 217742599272307 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101467736778929861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 62155608623833 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 62155608623833 : ℝ) = (62155608623833 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (312500000000 / 2589817025993 : ℝ) ≤ (1876317671679 / 15625000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101467736778929861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (62155608623833 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7769451077979 / 12500000000000 : ℝ)) ≤ (1876317671679 / 15625000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_391 : ∀ t : ℝ, (12362622986877 / 32000000000000 : ℝ) < t → t ≤ (24808963124013 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-34096181327437687084381967 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (24808963124013 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_392
  have hV : (2449483081512030866858064361680851 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (12362622986877 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_391 (Vfield_monotoneOn (show (12362622986877 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (12362622986877 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_392 : (1963198971454345263895403319308883 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (24808963124013 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (24808963124013 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (6226074596507 / 10000000000000 : ℝ) ≤ Real.sqrt (24808963124013 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (24808963124013 / 64000000000000 : ℝ) ≤ (62260745965071 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (62260745965071 / 100000000000000 : ℝ) = (100000000000000 / 62260745965071 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6226074596507 / 10000000000000 : ℝ) = (750000000000 / 6226074596507 : ℝ) := by norm_num
  have hL1 : (32760449762597 / 100000000000000 : ℝ) ≤ Real.log (1 + (24808963124013 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((24808963124013 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-18665429389103 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (62260745965071 / 217798134484919 : ℝ) ≤ (278438493286449 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (62260745965071 / 100000000000000 : ℝ) ≤ (278438493286449 / 500000000000000 : ℝ) := by
    have hw : (117798134484919 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (62260745965071 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (62260745965071 / 100000000000000 : ℝ) / (1 + (117798134484919 / 100000000000000 : ℝ)) = (62260745965071 / 217798134484919 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101391934022199861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 62260745965071 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 62260745965071 : ℝ) = (62260745965071 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 6226074596507 : ℝ) ≤ (119883488132441 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101391934022199861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (62260745965071 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6226074596507 / 10000000000000 : ℝ)) ≤ (119883488132441 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_392 : ∀ t : ℝ, (24808963124013 / 64000000000000 : ℝ) < t → t ≤ (777896258571 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-27211534420191990348031153 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (777896258571 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_393
  have hV : (1963198971454345263895403319308883 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (24808963124013 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_392 (Vfield_monotoneOn (show (24808963124013 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (24808963124013 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_393 : (19668058547553488536763101471341781 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (777896258571 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (777896258571 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (62365706063949 / 100000000000000 : ℝ) ≤ Real.sqrt (777896258571 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (777896258571 / 2000000000000 : ℝ) ≤ (1247314121279 / 2000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1247314121279 / 2000000000000 : ℝ) = (2000000000000 / 1247314121279 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (62365706063949 / 100000000000000 : ℝ) = (2500000000000 / 20788568687983 : ℝ) := by norm_num
  have hL1 : (32854671914797 / 100000000000000 : ℝ) ≤ Real.log (1 + (777896258571 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((777896258571 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3719803133103 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (1685559623350 / 5887936311571 : ℝ) ≤ (139408255804457 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1247314121279 / 2000000000000 : ℝ) ≤ (139408255804457 / 250000000000000 : ℝ) := by
    have hw : (117853643528127 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (1247314121279 / 2000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (1247314121279 / 2000000000000 : ℝ) / (1 + (117853643528127 / 100000000000000 : ℝ)) = (1685559623350 / 5887936311571 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101316330357706861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (2000000000000 / 1247314121279 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (2000000000000 / 1247314121279 : ℝ) = (1247314121279 / 2000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 20788568687983 : ℝ) ≤ (59841824837403 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101316330357706861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1247314121279 / 2000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (62365706063949 / 100000000000000 : ℝ)) ≤ (59841824837403 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_393 : ∀ t : ℝ, (777896258571 / 2000000000000 : ℝ) < t → t ≤ (24976397424531 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-5429331452525765849268913 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (24976397424531 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_394
  have hV : (19668058547553488536763101471341781 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (777896258571 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_393 (Vfield_monotoneOn (show (777896258571 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (777896258571 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_394 : (3940814280064322822126668133605899 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (24976397424531 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (24976397424531 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (12494097962771 / 20000000000000 : ℝ) ≤ Real.sqrt (24976397424531 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (24976397424531 / 64000000000000 : ℝ) ≤ (1952202806683 / 3125000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1952202806683 / 3125000000000 : ℝ) = (3125000000000 / 1952202806683 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (12494097962771 / 20000000000000 : ℝ) = (1500000000000 / 12494097962771 : ℝ) := by norm_num
  have hL1 : (32948805372421 / 100000000000000 : ℝ) ≤ Real.log (1 + (24976397424531 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((24976397424531 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1158301359459 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (62470489813856 / 217909126438893 : ℝ) ≤ (279193539558857 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1952202806683 / 3125000000000 : ℝ) ≤ (279193539558857 / 500000000000000 : ℝ) := by
    have hw : (117909126438893 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (1952202806683 / 3125000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (1952202806683 / 3125000000000 : ℝ) / (1 + (117909126438893 / 100000000000000 : ℝ)) = (62470489813856 / 217909126438893 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101240924767718261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (3125000000000 / 1952202806683 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (3125000000000 / 1952202806683 : ℝ) = (1952202806683 / 3125000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 12494097962771 : ℝ) ≤ (119484807270703 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101240924767718261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1952202806683 / 3125000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (12494097962771 / 20000000000000 : ℝ)) ≤ (119484807270703 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_394 : ∀ t : ℝ, (24976397424531 / 64000000000000 : ℝ) < t → t ≤ (2506011457479 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-67705744063461806684147433 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2506011457479 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_395
  have hV : (3940814280064322822126668133605899 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (24976397424531 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_394 (Vfield_monotoneOn (show (24976397424531 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (24976397424531 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_395 : (19740028520215424876907128427294841 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2506011457479 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2506011457479 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (62575098100689 / 100000000000000 : ℝ) ≤ Real.sqrt (2506011457479 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2506011457479 / 6400000000000 : ℝ) ≤ (6257509810069 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6257509810069 / 10000000000000 : ℝ) = (10000000000000 / 6257509810069 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (62575098100689 / 100000000000000 : ℝ) = (2500000000000 / 20858366033563 : ℝ) := by norm_num
  have hL1 : (6608570060459 / 20000000000000 : ℝ) ≤ Real.log (1 + (2506011457479 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2506011457479 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-18466846196383 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (8939299728670 / 31137797607727 : ℝ) ≤ (279569582183681 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6257509810069 / 10000000000000 : ℝ) ≤ (279569582183681 / 500000000000000 : ℝ) := by
    have hw : (117964583254089 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (6257509810069 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (6257509810069 / 10000000000000 : ℝ) / (1 + (117964583254089 / 100000000000000 : ℝ)) = (8939299728670 / 31137797607727 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101165716242753461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 6257509810069 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 6257509810069 : ℝ) = (6257509810069 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 20858366033563 : ℝ) ≤ (23857390534603 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101165716242753461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6257509810069 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (62575098100689 / 100000000000000 : ℝ)) ≤ (23857390534603 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_395 : ∀ t : ℝ, (2506011457479 / 6400000000000 : ℝ) < t → t ≤ (25143831725049 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-67546101409858375454709647 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (25143831725049 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_396
  have hV : (19740028520215424876907128427294841 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2506011457479 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_395 (Vfield_monotoneOn (show (2506011457479 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2506011457479 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_396 : (3955186030559438495391792721401017 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (25143831725049 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (25143831725049 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (12535906360593 / 20000000000000 : ℝ) ≤ Real.sqrt (25143831725049 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (25143831725049 / 64000000000000 : ℝ) ≤ (31339765901483 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (31339765901483 / 50000000000000 : ℝ) = (50000000000000 / 31339765901483 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (12535906360593 / 20000000000000 : ℝ) = (500000000000 / 4178635453531 : ℝ) := by norm_num
  have hL1 : (8284201717693 / 25000000000000 : ℝ) ≤ Real.log (1 + (25143831725049 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((25143831725049 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-18401087564729 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (62679531802966 / 218020014010501 : ℝ) ≤ (279944644490033 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (31339765901483 / 50000000000000 : ℝ) ≤ (279944644490033 / 500000000000000 : ℝ) := by
    have hw : (118020014010501 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (31339765901483 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (31339765901483 / 50000000000000 : ℝ) / (1 + (118020014010501 / 100000000000000 : ℝ)) = (62679531802966 / 218020014010501 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101090703781483061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 31339765901483 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 31339765901483 : ℝ) = (31339765901483 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 4178635453531 : ℝ) ≤ (119090077729899 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101090703781483061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (31339765901483 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (12535906360593 / 20000000000000 : ℝ)) ≤ (119090077729899 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_396 : ∀ t : ℝ, (25143831725049 / 64000000000000 : ℝ) < t → t ≤ (6306887218827 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-26955072055777745756050541 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (6306887218827 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_397
  have hV : (3955186030559438495391792721401017 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (25143831725049 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_396 (Vfield_monotoneOn (show (25143831725049 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (25143831725049 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_397 : (3962355308367743679027002100936913 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (6306887218827 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (6306887218827 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (12556758358377 / 20000000000000 : ℝ) ≤ Real.sqrt (6306887218827 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (6306887218827 / 16000000000000 : ℝ) ≤ (31391895895943 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (31391895895943 / 50000000000000 : ℝ) = (50000000000000 / 31391895895943 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (12556758358377 / 20000000000000 : ℝ) = (500000000000 / 4185586119459 : ℝ) := by norm_num
  have hL1 : (16615337621871 / 50000000000000 : ℝ) ≤ Real.log (1 + (6306887218827 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((6306887218827 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-4583886108649 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (62783791791886 / 218075418744829 : ℝ) ≤ (140159365722111 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (31391895895943 / 50000000000000 : ℝ) ≤ (140159365722111 / 250000000000000 : ℝ) := by
    have hw : (118075418744829 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (31391895895943 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (31391895895943 / 50000000000000 : ℝ) / (1 + (118075418744829 / 100000000000000 : ℝ)) = (62783791791886 / 218075418744829 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (101015886390645261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 31391895895943 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 31391895895943 : ℝ) = (31391895895943 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 4185586119459 : ℝ) ≤ (29723543595849 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (101015886390645261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (31391895895943 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (12556758358377 / 20000000000000 : ℝ)) ≤ (29723543595849 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_397 : ∀ t : ℝ, (6306887218827 / 16000000000000 : ℝ) < t → t ≤ (12697491587913 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-67074371791839712417347337 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (12697491587913 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_398
  have hV : (3962355308367743679027002100936913 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (6306887218827 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_397 (Vfield_monotoneOn (show (6306887218827 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (6306887218827 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_398 : (19883304555558660922601455308078433 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (12697491587913 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (12697491587913 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (62991794078457 / 100000000000000 : ℝ) ≤ Real.sqrt (12697491587913 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (12697491587913 / 32000000000000 : ℝ) ≤ (31495897039229 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (31495897039229 / 50000000000000 : ℝ) = (50000000000000 / 31495897039229 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (62991794078457 / 100000000000000 : ℝ) = (2500000000000 / 20997264692819 : ℝ) := by norm_num
  have hL1 : (3341814806437 / 10000000000000 : ℝ) ≤ Real.log (1 + (12697491587913 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((12697491587913 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-45512747653079 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (31495897039229 / 109093075146803 : ℝ) ≤ (281063998962567 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (31495897039229 / 50000000000000 : ℝ) ≤ (281063998962567 / 500000000000000 : ℝ) := by
    have hw : (59093075146803 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (31495897039229 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (31495897039229 / 50000000000000 : ℝ) / (1 + (59093075146803 / 50000000000000 : ℝ)) = (31495897039229 / 109093075146803 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (100866832886976261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 31495897039229 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 31495897039229 : ℝ) = (31495897039229 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 20997264692819 : ℝ) ≤ (118505250709443 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (100866832886976261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (31495897039229 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (62991794078457 / 100000000000000 : ℝ)) ≤ (118505250709443 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_398 : ∀ t : ℝ, (12697491587913 / 32000000000000 : ℝ) < t → t ≤ (3195302184543 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-133531154324118429851828579 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3195302184543 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_399
  have hV : (19883304555558660922601455308078433 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (12697491587913 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_398 (Vfield_monotoneOn (show (12697491587913 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (12697491587913 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_399 : (19954614476466348725264794970137207 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3195302184543 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3195302184543 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (63199111787103 / 100000000000000 : ℝ) ≤ Real.sqrt (3195302184543 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3195302184543 / 8000000000000 : ℝ) ≤ (1974972243347 / 3125000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1974972243347 / 3125000000000 : ℝ) = (3125000000000 / 1974972243347 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (63199111787103 / 100000000000000 : ℝ) = (2500000000000 / 21066370595701 : ℝ) := by norm_num
  have hL1 : (33605270081971 / 100000000000000 : ℝ) ≤ Real.log (1 + (3195302184543 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3195302184543 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-22594373721763 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (31599555893552 / 109148389096151 : ℝ) ≤ (56361084736023 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1974972243347 / 3125000000000 : ℝ) ≤ (56361084736023 / 100000000000000 : ℝ) := by
    have hw : (59148389096151 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (1974972243347 / 3125000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (1974972243347 / 3125000000000 : ℝ) / (1 + (59148389096151 / 50000000000000 : ℝ)) = (31599555893552 / 109148389096151 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (100718547943466661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (3125000000000 / 1974972243347 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (3125000000000 / 1974972243347 : ℝ) = (1974972243347 / 3125000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 21066370595701 : ℝ) ≤ (29530029753223 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (100718547943466661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1974972243347 / 3125000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (63199111787103 / 100000000000000 : ℝ)) ≤ (29530029753223 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_399 : ∀ t : ℝ, (3195302184543 / 8000000000000 : ℝ) < t → t ≤ (12864925888431 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-64903398392534418063471 / 48828125000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (12864925888431 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_400
  have hV : (19954614476466348725264794970137207 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3195302184543 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_399 (Vfield_monotoneOn (show (3195302184543 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3195302184543 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
