import Apery.Table2.U10
import Apery.Table2.U11

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_400 : (20025708192171622564139260393415097 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (12864925888431 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (12864925888431 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (63405751632913 / 100000000000000 : ℝ) ≤ Real.sqrt (12864925888431 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (12864925888431 / 32000000000000 : ℝ) ≤ (31702875816457 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (31702875816457 / 50000000000000 : ℝ) = (50000000000000 / 31702875816457 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (63405751632913 / 100000000000000 : ℝ) = (7500000000000 / 63405751632913 : ℝ) := by norm_num
  have hL1 : (33792042606953 / 100000000000000 : ℝ) ≤ Real.log (1 + (12864925888431 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((12864925888431 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-44866833246571 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (63405751632914 / 218407302731439 : ℝ) ≤ (282543043921671 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (31702875816457 / 50000000000000 : ℝ) ≤ (282543043921671 / 500000000000000 : ℝ) := by
    have hw : (118407302731439 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (31702875816457 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (31702875816457 / 50000000000000 : ℝ) / (1 + (118407302731439 / 100000000000000 : ℝ)) = (63405751632914 / 218407302731439 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (100571023895155461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 31702875816457 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 31702875816457 : ℝ) = (31702875816457 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 63405751632913 : ℝ) ≤ (23547743614269 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (100571023895155461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (31702875816457 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (63405751632913 / 100000000000000 : ℝ)) ≤ (23547743614269 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_400 : ∀ t : ℝ, (12864925888431 / 32000000000000 : ℝ) < t → t ≤ (1294864303869 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-132321370854697799201025757 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1294864303869 / 3200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_401
  have hV : (20025708192171622564139260393415097 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (12864925888431 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_400 (Vfield_monotoneOn (show (12864925888431 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (12864925888431 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_401 : (2009658756335319103439134612599879 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (1294864303869 / 3200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1294864303869 / 3200000000000 : ℝ) := by norm_num
  have hs1 : (6361172022191 / 10000000000000 : ℝ) ≤ Real.sqrt (1294864303869 / 3200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1294864303869 / 3200000000000 : ℝ) ≤ (63611720221911 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (63611720221911 / 100000000000000 : ℝ) = (100000000000000 / 63611720221911 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6361172022191 / 10000000000000 : ℝ) = (750000000000 / 6361172022191 : ℝ) := by norm_num
  have hL1 : (8494616735599 / 25000000000000 : ℝ) ≤ Real.log (1 + (1294864303869 / 3200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1294864303869 / 3200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-89093956746357 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (21203906740637 / 72839241400061 : ℝ) ≤ (141638448704549 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (63611720221911 / 100000000000000 : ℝ) ≤ (141638448704549 / 250000000000000 : ℝ) := by
    have hw : (118517724200183 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (63611720221911 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (63611720221911 / 100000000000000 : ℝ) / (1 + (118517724200183 / 100000000000000 : ℝ)) = (21203906740637 / 72839241400061 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (100424253197670061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 63611720221911 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 63611720221911 : ℝ) = (63611720221911 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 6361172022191 : ℝ) ≤ (938887904299 / 8000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (100424253197670061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (63611720221911 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6361172022191 / 10000000000000 : ℝ)) ≤ (938887904299 / 8000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_401 : ∀ t : ℝ, (1294864303869 / 3200000000000 : ℝ) < t → t ≤ (13032360188949 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-26345686873338474546033639 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (13032360188949 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_402
  have hV : (2009658756335319103439134612599879 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1294864303869 / 3200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_401 (Vfield_monotoneOn (show (1294864303869 / 3200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1294864303869 / 3200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_402 : (2520906803036523877601611019608841 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (13032360188949 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (13032360188949 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (7977128006689 / 12500000000000 : ℝ) ≤ Real.sqrt (13032360188949 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (13032360188949 / 32000000000000 : ℝ) ≤ (63817024053513 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (63817024053513 / 100000000000000 : ℝ) = (100000000000000 / 63817024053513 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7977128006689 / 12500000000000 : ℝ) = (937500000000 / 7977128006689 : ℝ) := by norm_num
  have hL1 : (4270568048013 / 12500000000000 : ℝ) ≤ Real.log (1 + (13032360188949 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((13032360188949 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-44229156643259 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (63817024053513 / 218628042886354 : ℝ) ≤ (71001755318641 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (63817024053513 / 100000000000000 : ℝ) ≤ (71001755318641 / 125000000000000 : ℝ) := by
    have hw : (59314021443177 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (63817024053513 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (63817024053513 / 100000000000000 : ℝ) / (1 + (59314021443177 / 50000000000000 : ℝ)) = (63817024053513 / 218628042886354 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (100278228424576861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 63817024053513 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 63817024053513 : ℝ) = (63817024053513 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (937500000000 / 7977128006689 : ℝ) ≤ (23397374079817 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (100278228424576861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (63817024053513 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7977128006689 / 12500000000000 : ℝ)) ≤ (23397374079817 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_402 : ∀ t : ℝ, (13032360188949 / 32000000000000 : ℝ) < t → t ≤ (1639509667401 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-16392878642750851111238951 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1639509667401 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_403
  have hV : (2520906803036523877601611019608841 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (13032360188949 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_402 (Vfield_monotoneOn (show (13032360188949 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (13032360188949 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_403 : (5059427645848385876533548363417139 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (1639509667401 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1639509667401 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (16005417380731 / 25000000000000 : ℝ) ≤ Real.sqrt (1639509667401 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1639509667401 / 4000000000000 : ℝ) ≤ (2560866780917 / 4000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2560866780917 / 4000000000000 : ℝ) = (4000000000000 / 2560866780917 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16005417380731 / 25000000000000 : ℝ) = (1875000000000 / 16005417380731 : ℝ) := by norm_num
  have hL1 : (34350276220663 / 100000000000000 : ℝ) ≤ Real.log (1 + (1639509667401 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1639509667401 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-43913342372811 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (12804333904585 / 43747651815287 : ℝ) ≤ (4448960188647 / 15625000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2560866780917 / 4000000000000 : ℝ) ≤ (4448960188647 / 7812500000000 : ℝ) := by
    have hw : (23747651815287 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (2560866780917 / 4000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (2560866780917 / 4000000000000 : ℝ) / (1 + (23747651815287 / 20000000000000 : ℝ)) = (12804333904585 / 43747651815287 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (100132942264808061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (4000000000000 / 2560866780917 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (4000000000000 / 2560866780917 : ℝ) = (2560866780917 / 4000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 16005417380731 : ℝ) ≤ (29154076985507 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (100132942264808061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2560866780917 / 4000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16005417380731 / 25000000000000 : ℝ)) ≤ (29154076985507 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_403 : ∀ t : ℝ, (1639509667401 / 4000000000000 : ℝ) < t → t ≤ (6641755819863 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-129993659918244428677919917 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (6641755819863 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_404
  have hV : (5059427645848385876533548363417139 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1639509667401 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_403 (Vfield_monotoneOn (show (1639509667401 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1639509667401 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_404 : (20377997903358620036641395004628349 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (6641755819863 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (6641755819863 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (64429010448821 / 100000000000000 : ℝ) ≤ Real.sqrt (6641755819863 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (6641755819863 / 16000000000000 : ℝ) ≤ (32214505224411 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (32214505224411 / 50000000000000 : ℝ) = (50000000000000 / 32214505224411 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (64429010448821 / 100000000000000 : ℝ) = (7500000000000 / 64429010448821 : ℝ) := by norm_num
  have hL1 : (8680177049223 / 25000000000000 : ℝ) ≤ Real.log (1 + (6641755819863 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((6641755819863 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-43287635880421 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (32214505224411 / 109479192553813 : ℝ) ≤ (11447015115329 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (32214505224411 / 50000000000000 : ℝ) ≤ (11447015115329 / 20000000000000 : ℝ) := by
    have hw : (59479192553813 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (32214505224411 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (32214505224411 / 50000000000000 : ℝ) / (1 + (59479192553813 / 50000000000000 : ℝ)) = (32214505224411 / 109479192553813 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (99844557102844661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 32214505224411 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 32214505224411 : ℝ) = (32214505224411 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 64429010448821 : ℝ) ≤ (115885625981797 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (99844557102844661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (32214505224411 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (64429010448821 / 100000000000000 : ℝ)) ≤ (115885625981797 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_404 : ∀ t : ℝ, (6641755819863 / 16000000000000 : ℝ) < t → t ≤ (3362736485061 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-128871178141472142313893579 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3362736485061 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_405
  have hV : (20377997903358620036641395004628349 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (6641755819863 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_404 (Vfield_monotoneOn (show (6641755819863 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (6641755819863 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_405 : (20517463491960449633125744655142607 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3362736485061 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3362736485061 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (64833792163703 / 100000000000000 : ℝ) ≤ Real.sqrt (3362736485061 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3362736485061 / 8000000000000 : ℝ) ≤ (8104224020463 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8104224020463 / 12500000000000 : ℝ) = (12500000000000 / 8104224020463 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (64833792163703 / 100000000000000 : ℝ) = (7500000000000 / 64833792163703 : ℝ) := by norm_num
  have hL1 : (17544886518691 / 50000000000000 : ℝ) ≤ Real.log (1 + (3362736485061 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3362736485061 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-85339325764103 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (64833792163704 / 219178104559211 : ℝ) ≤ (143801478105859 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8104224020463 / 12500000000000 : ℝ) ≤ (143801478105859 / 250000000000000 : ℝ) := by
    have hw : (119178104559211 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (8104224020463 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (8104224020463 / 12500000000000 : ℝ) / (1 + (119178104559211 / 100000000000000 : ℝ)) = (64833792163704 / 219178104559211 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (99559041437146061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 8104224020463 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 8104224020463 : ℝ) = (8104224020463 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 64833792163703 : ℝ) ≤ (115168509024533 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (99559041437146061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8104224020463 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (64833792163703 / 100000000000000 : ℝ)) ≤ (115168509024533 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_405 : ∀ t : ℝ, (3362736485061 / 8000000000000 : ℝ) < t → t ≤ (6809190120381 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-127773795136629610632401703 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (6809190120381 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_406
  have hV : (20517463491960449633125744655142607 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3362736485061 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_405 (Vfield_monotoneOn (show (3362736485061 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3362736485061 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_406 : (20656120935117686640148600857518919 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (6809190120381 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (6809190120381 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (65236062306351 / 100000000000000 : ℝ) ≤ Real.sqrt (6809190120381 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (6809190120381 / 16000000000000 : ℝ) ≤ (4077253894147 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4077253894147 / 6250000000000 : ℝ) = (6250000000000 / 4077253894147 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (65236062306351 / 100000000000000 : ℝ) = (2500000000000 / 21745354102117 : ℝ) := by norm_num
  have hL1 : (35457480796283 / 100000000000000 : ℝ) ≤ Real.log (1 + (6809190120381 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((6809190120381 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-16823693817267 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (16309015576588 / 54849354918949 : ℝ) ≤ (2312131679747 / 8000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4077253894147 / 6250000000000 : ℝ) ≤ (2312131679747 / 4000000000000 : ℝ) := by
    have hw : (29849354918949 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (4077253894147 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (4077253894147 / 6250000000000 : ℝ) / (1 + (29849354918949 / 25000000000000 : ℝ)) = (16309015576588 / 54849354918949 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (99276340685814661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 4077253894147 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 4077253894147 : ℝ) = (4077253894147 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 21745354102117 : ℝ) ≤ (57232271235979 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (99276340685814661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4077253894147 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (65236062306351 / 100000000000000 : ℝ)) ≤ (57232271235979 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_406 : ∀ t : ℝ, (6809190120381 / 16000000000000 : ℝ) < t → t ≤ (86161340883 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-126699955989173938526989547 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (86161340883 / 200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_407
  have hV : (20656120935117686640148600857518919 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (6809190120381 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_406 (Vfield_monotoneOn (show (6809190120381 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (6809190120381 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_407 : (20793983450483509785207051014117537 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (86161340883 / 200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (86161340883 / 200000000000 : ℝ) := by norm_num
  have hs1 : (65635867055673 / 100000000000000 : ℝ) ≤ Real.sqrt (86161340883 / 200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (86161340883 / 200000000000 : ℝ) ≤ (32817933527837 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (32817933527837 / 50000000000000 : ℝ) = (50000000000000 / 32817933527837 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (65635867055673 / 100000000000000 : ℝ) = (2500000000000 / 21878622351891 : ℝ) := by norm_num
  have hL1 : (17911920708621 / 50000000000000 : ℝ) ≤ Real.log (1 + (86161340883 / 200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((86161340883 / 200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-20728084431133 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (65635867055674 / 219616332681411 : ℝ) ≤ (72604038488041 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (32817933527837 / 50000000000000 : ℝ) ≤ (72604038488041 / 125000000000000 : ℝ) := by
    have hw : (119616332681411 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (32817933527837 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (32817933527837 / 50000000000000 : ℝ) / (1 + (119616332681411 / 100000000000000 : ℝ)) = (65635867055674 / 219616332681411 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (98996401889056861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 32817933527837 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 32817933527837 : ℝ) = (32817933527837 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 21878622351891 : ℝ) ≤ (28443332313071 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (98996401889056861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (32817933527837 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (65635867055673 / 100000000000000 : ℝ)) ≤ (28443332313071 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_407 : ∀ t : ℝ, (86161340883 / 200000000000 : ℝ) < t → t ≤ (54181913021 / 125000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-24985746611234844265338441 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (54181913021 / 125000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_408
  have hV : (20793983450483509785207051014117537 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (86161340883 / 200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_407 (Vfield_monotoneOn (show (86161340883 / 200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (86161340883 / 200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_408 : (130396690515748895205442440082079 / 31250000000000000000000000000000 : ℝ) ≤ Vfield (54181913021 / 125000000000 : ℝ) := by
  have hp : (0 : ℝ) < (54181913021 / 125000000000 : ℝ) := by norm_num
  have hs1 : (411483265991 / 625000000000 : ℝ) ≤ Real.sqrt (54181913021 / 125000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (54181913021 / 125000000000 : ℝ) ≤ (65837322558561 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (65837322558561 / 100000000000000 : ℝ) = (100000000000000 / 65837322558561 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (411483265991 / 625000000000 : ℝ) = (46875000000 / 411483265991 : ℝ) := by norm_num
  have hL1 : (36008782634211 / 100000000000000 : ℝ) ≤ Real.log (1 + (54181913021 / 125000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((54181913021 / 125000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-102884119613 / 125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (65837322558561 / 219726993788702 : ℝ) ≤ (291119496226203 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (65837322558561 / 100000000000000 : ℝ) ≤ (291119496226203 / 500000000000000 : ℝ) := by
    have hw : (59863496894351 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (65837322558561 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (65837322558561 / 100000000000000 : ℝ) / (1 + (59863496894351 / 50000000000000 : ℝ)) = (65837322558561 / 219726993788702 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (98855733434249061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 65837322558561 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 65837322558561 : ℝ) = (65837322558561 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (46875000000 / 411483265991 : ℝ) ≤ (11342817734101 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (98855733434249061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (65837322558561 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (411483265991 / 625000000000 : ℝ)) ≤ (11342817734101 / 100000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_408 : ∀ t : ℝ, (54181913021 / 125000000000 : ℝ) < t → t ≤ (436103903921 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-123888944722313362545474597 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (436103903921 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_409
  have hV : (130396690515748895205442440082079 / 31250000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (54181913021 / 125000000000 : ℝ) := by norm_num
    refine le_trans V_pt_408 (Vfield_monotoneOn (show (54181913021 / 125000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (54181913021 / 125000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_409 : (20932758760020712048952397756313677 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (436103903921 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (436103903921 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (66038163505733 / 100000000000000 : ℝ) ≤ Real.sqrt (436103903921 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (436103903921 / 1000000000000 : ℝ) ≤ (33019081752867 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (33019081752867 / 50000000000000 : ℝ) = (50000000000000 / 33019081752867 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (66038163505733 / 100000000000000 : ℝ) = (7500000000000 / 66038163505733 : ℝ) := by norm_num
  have hL1 : (36193382449937 / 100000000000000 : ℝ) ≤ Real.log (1 + (436103903921 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((436103903921 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-10213236551243 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (33019081752867 / 109918776354349 : ℝ) ≤ (145909699244529 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (33019081752867 / 50000000000000 : ℝ) ≤ (145909699244529 / 250000000000000 : ℝ) := by
    have hw : (59918776354349 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (33019081752867 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (33019081752867 / 50000000000000 : ℝ) / (1 + (59918776354349 / 50000000000000 : ℝ)) = (33019081752867 / 109918776354349 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (98715752981678061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 33019081752867 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 33019081752867 : ℝ) = (33019081752867 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 66038163505733 : ℝ) ≤ (113086147777861 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (98715752981678061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (33019081752867 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (66038163505733 / 100000000000000 : ℝ)) ≤ (113086147777861 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_409 : ∀ t : ℝ, (436103903921 / 1000000000000 : ℝ) < t → t ≤ (219376251837 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-4918977940820734563496111 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (219376251837 / 500000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_410
  have hV : (20932758760020712048952397756313677 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (436103903921 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_409 (Vfield_monotoneOn (show (436103903921 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (436103903921 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_410 : (32815390462214812629406665642781 / 7812500000000000000000000000000 : ℝ) ≤ Vfield (219376251837 / 500000000000 : ℝ) := by
  have hp : (0 : ℝ) < (219376251837 / 500000000000 : ℝ) := by norm_num
  have hs1 : (103497492949 / 156250000000 : ℝ) ≤ Real.sqrt (219376251837 / 500000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (219376251837 / 500000000000 : ℝ) ≤ (66238395487361 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (66238395487361 / 100000000000000 : ℝ) = (100000000000000 / 66238395487361 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (103497492949 / 156250000000 : ℝ) = (11718750000 / 103497492949 : ℝ) := by norm_num
  have hL1 : (727552842451 / 2000000000000 : ℝ) ≤ Real.log (1 + (219376251837 / 500000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((219376251837 / 500000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-81108084377377 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (66238395487361 / 219948009723963 : ℝ) ≤ (146257946431469 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (66238395487361 / 100000000000000 : ℝ) ≤ (146257946431469 / 250000000000000 : ℝ) := by
    have hw : (119948009723963 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (66238395487361 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (66238395487361 / 100000000000000 : ℝ) / (1 + (119948009723963 / 100000000000000 : ℝ)) = (66238395487361 / 219948009723963 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (98576454106902061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 66238395487361 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 66238395487361 : ℝ) = (66238395487361 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (11718750000 / 103497492949 : ℝ) ≤ (28186798442033 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (98576454106902061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (66238395487361 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (103497492949 / 156250000000 : ℝ)) ≤ (28186798442033 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_410 : ∀ t : ℝ, (219376251837 / 500000000000 : ℝ) < t → t ≤ (880153607101 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-15318036896809525999576783 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (880153607101 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_411
  have hV : (32815390462214812629406665642781 / 7812500000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (219376251837 / 500000000000 : ℝ) := by norm_num
    refine le_trans V_pt_410 (Vfield_monotoneOn (show (219376251837 / 500000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (219376251837 / 500000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_411 : (21036322033678068052552331693028091 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (880153607101 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (880153607101 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (66338284839939 / 100000000000000 : ℝ) ≤ Real.sqrt (880153607101 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (880153607101 / 2000000000000 : ℝ) ≤ (3316914241997 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3316914241997 / 5000000000000 : ℝ) = (5000000000000 / 3316914241997 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (66338284839939 / 100000000000000 : ℝ) = (2500000000000 / 22112761613313 : ℝ) := by norm_num
  have hL1 : (4558705599557 / 12500000000000 : ℝ) ≤ Real.log (1 + (880153607101 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((880153607101 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-40405257598041 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (16584571209985 / 55000800026317 : ℝ) ≤ (292862872001001 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3316914241997 / 5000000000000 : ℝ) ≤ (292862872001001 / 500000000000000 : ℝ) := by
    have hw : (30000800026317 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (3316914241997 / 5000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3316914241997 / 5000000000000 : ℝ) / (1 + (30000800026317 / 25000000000000 : ℝ)) = (16584571209985 / 55000800026317 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (98507058279289461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 3316914241997 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 3316914241997 : ℝ) = (3316914241997 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 22112761613313 : ℝ) ≤ (22515771148009 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (98507058279289461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3316914241997 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (66338284839939 / 100000000000000 : ℝ)) ≤ (22515771148009 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_411 : ∀ t : ℝ, (880153607101 / 2000000000000 : ℝ) < t → t ≤ (441401103427 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-122127438768509115877705103 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (441401103427 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_412
  have hV : (21036322033678068052552331693028091 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (880153607101 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_411 (Vfield_monotoneOn (show (880153607101 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (880153607101 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_412 : (5267686370293331609026475836856767 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (441401103427 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (441401103427 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (16609506002343 / 25000000000000 : ℝ) ≤ Real.sqrt (441401103427 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (441401103427 / 1000000000000 : ℝ) ≤ (66438024009373 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (66438024009373 / 100000000000000 : ℝ) = (100000000000000 / 66438024009373 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16609506002343 / 25000000000000 : ℝ) = (625000000000 / 5536502000781 : ℝ) := by norm_num
  have hL1 : (914039072581 / 2500000000000 : ℝ) ≤ Real.log (1 + (441401103427 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((441401103427 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-8051382886253 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (66438024009373 / 220058365115763 : ℝ) ≤ (293209011000339 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (66438024009373 / 100000000000000 : ℝ) ≤ (293209011000339 / 500000000000000 : ℝ) := by
    have hw : (120058365115763 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (66438024009373 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (66438024009373 / 100000000000000 : ℝ) / (1 + (120058365115763 / 100000000000000 : ℝ)) = (66438024009373 / 220058365115763 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (98437830479421861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 66438024009373 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 66438024009373 : ℝ) = (66438024009373 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (625000000000 / 5536502000781 : ℝ) ≤ (112411269493113 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (98437830479421861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (66438024009373 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16609506002343 / 25000000000000 : ℝ)) ≤ (112411269493113 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_412 : ∀ t : ℝ, (441401103427 / 1000000000000 : ℝ) < t → t ≤ (885450806607 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-121721681336487756015821709 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (885450806607 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_413
  have hV : (5267686370293331609026475836856767 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (441401103427 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_412 (Vfield_monotoneOn (show (441401103427 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (441401103427 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_413 : (5276280108476728829262791874100133 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (885450806607 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (885450806607 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (16634403417757 / 25000000000000 : ℝ) ≤ Real.sqrt (885450806607 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (885450806607 / 2000000000000 : ℝ) ≤ (66537613671029 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (66537613671029 / 100000000000000 : ℝ) = (100000000000000 / 66537613671029 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16634403417757 / 25000000000000 : ℝ) = (1875000000000 / 16634403417757 : ℝ) := by norm_num
  have hL1 : (36653396598223 / 100000000000000 : ℝ) ≤ Real.log (1 + (885450806607 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((885450806607 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-2506813129801 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (66537613671029 / 220113504790406 : ℝ) ≤ (36694289218211 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (66537613671029 / 100000000000000 : ℝ) ≤ (36694289218211 / 62500000000000 : ℝ) := by
    have hw : (60056752395203 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (66537613671029 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (66537613671029 / 100000000000000 : ℝ) / (1 + (60056752395203 / 50000000000000 : ℝ)) = (66537613671029 / 220113504790406 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (98368769930352061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 66537613671029 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 66537613671029 : ℝ) = (66537613671029 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 16634403417757 : ℝ) ≤ (28061107362057 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (98368769930352061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (66537613671029 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16634403417757 / 25000000000000 : ℝ)) ≤ (28061107362057 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_413 : ∀ t : ℝ, (885450806607 / 2000000000000 : ℝ) < t → t ≤ (22202485159 / 50000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-121325417510932168507365897 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (22202485159 / 50000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_414
  have hV : (5276280108476728829262791874100133 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (885450806607 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_413 (Vfield_monotoneOn (show (885450806607 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (885450806607 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_414 : (5284861771545921934864471139802583 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (22202485159 / 50000000000 : ℝ) := by
  have hp : (0 : ℝ) < (22202485159 / 50000000000 : ℝ) := by norm_num
  have hs1 : (16659263623807 / 25000000000000 : ℝ) ≤ Real.sqrt (22202485159 / 50000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (22202485159 / 50000000000 : ℝ) ≤ (66637054495229 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (66637054495229 / 100000000000000 : ℝ) = (100000000000000 / 66637054495229 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16659263623807 / 25000000000000 : ℝ) = (1875000000000 / 16659263623807 : ℝ) := by norm_num
  have hL1 : (18372573018151 / 50000000000000 : ℝ) ≤ Real.log (1 + (22202485159 / 50000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((22202485159 / 50000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-15984616778503 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (66637054495229 / 220168619164073 : ℝ) ≤ (293898784093609 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (66637054495229 / 100000000000000 : ℝ) ≤ (293898784093609 / 500000000000000 : ℝ) := by
    have hw : (120168619164073 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (66637054495229 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (66637054495229 / 100000000000000 : ℝ) / (1 + (120168619164073 / 100000000000000 : ℝ)) = (66637054495229 / 220168619164073 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (98299875860767861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 66637054495229 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 66637054495229 : ℝ) = (66637054495229 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 16659263623807 : ℝ) ≤ (112078330084081 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (98299875860767861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (66637054495229 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16659263623807 / 25000000000000 : ℝ)) ≤ (112078330084081 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_414 : ∀ t : ℝ, (22202485159 / 50000000000 : ℝ) < t → t ≤ (890748006113 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-30234357770677561922951989 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (890748006113 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_415
  have hV : (5284861771545921934864471139802583 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (22202485159 / 50000000000 : ℝ) := by norm_num
    refine le_trans V_pt_414 (Vfield_monotoneOn (show (22202485159 / 50000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (22202485159 / 50000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_415 : (211737256310224174573951518067737 / 50000000000000000000000000000000 : ℝ) ≤ Vfield (890748006113 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (890748006113 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (667363471473 / 1000000000000 : ℝ) ≤ Real.sqrt (890748006113 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (890748006113 / 2000000000000 : ℝ) ≤ (66736347147301 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (66736347147301 / 100000000000000 : ℝ) = (100000000000000 / 66736347147301 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (667363471473 / 1000000000000 : ℝ) = (25000000000 / 222454490491 : ℝ) := by norm_num
  have hL1 : (7367362274389 / 20000000000000 : ℝ) ≤ Real.log (1 + (890748006113 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((890748006113 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-39814507473987 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (66736347147301 / 220223708271559 : ℝ) ≤ (36780303234097 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (66736347147301 / 100000000000000 : ℝ) ≤ (36780303234097 / 62500000000000 : ℝ) := by
    have hw : (120223708271559 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (66736347147301 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (66736347147301 / 100000000000000 : ℝ) / (1 + (120223708271559 / 100000000000000 : ℝ)) = (66736347147301 / 220223708271559 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (98231147504934461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 66736347147301 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 66736347147301 : ℝ) = (66736347147301 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (25000000000 / 222454490491 : ℝ) ≤ (55956482968193 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (98231147504934461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (66736347147301 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (667363471473 / 1000000000000 : ℝ)) ≤ (55956482968193 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_415 : ∀ t : ℝ, (890748006113 / 2000000000000 : ℝ) < t → t ≤ (446698302933 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-15069596684615197128043829 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (446698302933 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_416
  have hV : (211737256310224174573951518067737 / 50000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (890748006113 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_415 (Vfield_monotoneOn (show (890748006113 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (890748006113 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_416 : (21207956260167935190762584425723239 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (446698302933 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (446698302933 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (66835492287631 / 100000000000000 : ℝ) ≤ Real.sqrt (446698302933 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (446698302933 / 1000000000000 : ℝ) ≤ (4177218267977 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4177218267977 / 6250000000000 : ℝ) = (6250000000000 / 4177218267977 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (66835492287631 / 100000000000000 : ℝ) = (7500000000000 / 66835492287631 : ℝ) := by norm_num
  have hL1 : (9232098189799 / 25000000000000 : ℝ) ≤ Real.log (1 + (446698302933 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((446698302933 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-79335808233943 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (33417746143816 / 110139386073791 : ℝ) ≤ (294585242884259 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4177218267977 / 6250000000000 : ℝ) ≤ (294585242884259 / 500000000000000 : ℝ) := by
    have hw : (60139386073791 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (4177218267977 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (4177218267977 / 6250000000000 : ℝ) / (1 + (60139386073791 / 50000000000000 : ℝ)) = (33417746143816 / 110139386073791 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (98162584102637861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 4177218267977 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 4177218267977 : ℝ) = (4177218267977 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 66835492287631 : ℝ) ≤ (111748331597127 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (98162584102637861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4177218267977 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (66835492287631 / 100000000000000 : ℝ)) ≤ (111748331597127 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_416 : ∀ t : ℝ, (446698302933 / 1000000000000 : ℝ) < t → t ≤ (896045205619 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-120182687105812788076975047 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (896045205619 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_417
  have hV : (21207956260167935190762584425723239 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (446698302933 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_416 (Vfield_monotoneOn (show (446698302933 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (446698302933 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_417 : (10621069582050541462514544848769033 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (896045205619 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (896045205619 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (33467245285857 / 50000000000000 : ℝ) ≤ Real.sqrt (896045205619 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (896045205619 / 2000000000000 : ℝ) ≤ (13386898114343 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13386898114343 / 20000000000000 : ℝ) = (20000000000000 / 13386898114343 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33467245285857 / 50000000000000 : ℝ) = (1250000000000 / 11155748428619 : ℝ) := by norm_num
  have hL1 : (9254972587919 / 25000000000000 : ℝ) ≤ Real.log (1 + (896045205619 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((896045205619 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-494021616931 / 625000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (66934490571715 / 220333810826778 : ℝ) ≤ (294927238901789 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13386898114343 / 20000000000000 : ℝ) ≤ (294927238901789 / 500000000000000 : ℝ) := by
    have hw : (60166905413389 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (13386898114343 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (13386898114343 / 20000000000000 : ℝ) / (1 + (60166905413389 / 50000000000000 : ℝ)) = (66934490571715 / 220333810826778 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (98094184899131861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 13386898114343 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 13386898114343 : ℝ) = (13386898114343 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 11155748428619 : ℝ) ≤ (111584421713823 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (98094184899131861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13386898114343 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33467245285857 / 50000000000000 : ℝ)) ≤ (111584421713823 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_417 : ∀ t : ℝ, (896045205619 / 2000000000000 : ℝ) < t → t ≤ (1794739010991 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-29999477705832988253195531 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1794739010991 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_418
  have hV : (10621069582050541462514544848769033 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (896045205619 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_417 (Vfield_monotoneOn (show (896045205619 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (896045205619 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_418 : (21259212778296631446537531220398189 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1794739010991 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1794739010991 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (66983934846181 / 100000000000000 : ℝ) ≤ Real.sqrt (1794739010991 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1794739010991 / 4000000000000 : ℝ) ≤ (33491967423091 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (33491967423091 / 50000000000000 : ℝ) = (50000000000000 / 33491967423091 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (66983934846181 / 100000000000000 : ℝ) = (7500000000000 / 66983934846181 : ℝ) := by norm_num
  have hL1 : (37065607772769 / 100000000000000 : ℝ) ≤ Real.log (1 + (1794739010991 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1794739010991 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-39448801914487 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (33491967423091 / 110180660364185 : ℝ) ≤ (295097930209711 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (33491967423091 / 50000000000000 : ℝ) ≤ (295097930209711 / 500000000000000 : ℝ) := by
    have hw : (12036132072837 / 10000000000000 : ℝ) ≤ Real.sqrt (1 + (33491967423091 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (33491967423091 / 50000000000000 : ℝ) / (1 + (12036132072837 / 10000000000000 : ℝ)) = (33491967423091 / 110180660364185 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (98060046637547461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 33491967423091 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 33491967423091 : ℝ) = (33491967423091 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 66983934846181 : ℝ) ≤ (3484460524547 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (98060046637547461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (33491967423091 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (66983934846181 / 100000000000000 : ℝ)) ≤ (3484460524547 / 31250000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_418 : ∀ t : ℝ, (1794739010991 / 4000000000000 : ℝ) < t → t ≤ (224673451343 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-59907277431286316871727269 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (224673451343 / 500000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_419
  have hV : (21259212778296631446537531220398189 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1794739010991 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_418 (Vfield_monotoneOn (show (1794739010991 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1794739010991 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_419 : (10638137266026674045799956598259207 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (224673451343 / 500000000000 : ℝ) := by
  have hp : (0 : ℝ) < (224673451343 / 500000000000 : ℝ) := by norm_num
  have hs1 : (33516671325103 / 50000000000000 : ℝ) ≤ Real.sqrt (224673451343 / 500000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (224673451343 / 500000000000 : ℝ) ≤ (67033342650207 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (67033342650207 / 100000000000000 : ℝ) = (100000000000000 / 67033342650207 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33516671325103 / 50000000000000 : ℝ) = (3750000000000 / 33516671325103 : ℝ) := by norm_num
  have hL1 : (18555652151293 / 50000000000000 : ℝ) ≤ Real.log (1 + (224673451343 / 500000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((224673451343 / 500000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-78751961375651 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67033342650207 / 220388824343707 : ℝ) ≤ (295268417672053 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (67033342650207 / 100000000000000 : ℝ) ≤ (295268417672053 / 500000000000000 : ℝ) := by
    have hw : (120388824343707 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (67033342650207 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (67033342650207 / 100000000000000 : ℝ) / (1 + (120388824343707 / 100000000000000 : ℝ)) = (67033342650207 / 220388824343707 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (98025949145079061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 67033342650207 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 67033342650207 : ℝ) = (67033342650207 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 33516671325103 : ℝ) ≤ (111421230988783 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (98025949145079061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (67033342650207 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33516671325103 / 50000000000000 : ℝ)) ≤ (111421230988783 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_419 : ∀ t : ℝ, (224673451343 / 500000000000 : ℝ) < t → t ≤ (1800036210497 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-119632558387996922544886661 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1800036210497 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_420
  have hV : (10638137266026674045799956598259207 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (224673451343 / 500000000000 : ℝ) := by norm_num
    refine le_trans V_pt_419 (Vfield_monotoneOn (show (224673451343 / 500000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (224673451343 / 500000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_420 : (21293324448831686222067937519107837 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1800036210497 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1800036210497 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (67082714064373 / 100000000000000 : ℝ) ≤ Real.sqrt (1800036210497 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1800036210497 / 4000000000000 : ℝ) ≤ (33541357032187 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (33541357032187 / 50000000000000 : ℝ) = (50000000000000 / 33541357032187 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (67082714064373 / 100000000000000 : ℝ) = (7500000000000 / 67082714064373 : ℝ) := by norm_num
  have hL1 : (37156979960213 / 100000000000000 : ℝ) ≤ Real.log (1 + (1800036210497 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1800036210497 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-19651632682781 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (33541357032187 / 110208160838549 : ℝ) ≤ (295438701752967 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (33541357032187 / 50000000000000 : ℝ) ≤ (295438701752967 / 500000000000000 : ℝ) := by
    have hw : (60208160838549 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (33541357032187 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (33541357032187 / 50000000000000 : ℝ) / (1 + (60208160838549 / 50000000000000 : ℝ)) = (33541357032187 / 110208160838549 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97991892328896261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 33541357032187 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 33541357032187 : ℝ) = (33541357032187 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 67082714064373 : ℝ) ≤ (27834975917473 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97991892328896261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (33541357032187 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (67082714064373 / 100000000000000 : ℝ)) ≤ (27834975917473 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_420 : ∀ t : ℝ, (1800036210497 / 4000000000000 : ℝ) < t → t ≤ (7210739241 / 16000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-119451865618070327773379287 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7210739241 / 16000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_421
  have hV : (21293324448831686222067937519107837 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1800036210497 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_420 (Vfield_monotoneOn (show (1800036210497 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1800036210497 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_421 : (21310362552014849979883597667402161 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (7210739241 / 16000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7210739241 / 16000000000 : ℝ) := by norm_num
  have hs1 : (67132049168969 / 100000000000000 : ℝ) ≤ Real.sqrt (7210739241 / 16000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7210739241 / 16000000000 : ℝ) ≤ (6713204916897 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6713204916897 / 10000000000000 : ℝ) = (10000000000000 / 6713204916897 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (67132049168969 / 100000000000000 : ℝ) = (7500000000000 / 67132049168969 : ℝ) := by norm_num
  have hL1 : (37202634764707 / 100000000000000 : ℝ) ≤ Real.log (1 + (7210739241 / 16000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7210739241 / 16000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-78461311280217 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (33566024584485 / 110221906366423 : ℝ) ≤ (2309443616523 / 7812500000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6713204916897 / 10000000000000 : ℝ) ≤ (2309443616523 / 3906250000000 : ℝ) := by
    have hw : (60221906366423 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (6713204916897 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (6713204916897 / 10000000000000 : ℝ) / (1 + (60221906366423 / 50000000000000 : ℝ)) = (33566024584485 / 110221906366423 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97957876096500861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 6713204916897 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 6713204916897 : ℝ) = (6713204916897 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 67132049168969 : ℝ) ≤ (55629377089201 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97957876096500861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6713204916897 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (67132049168969 / 100000000000000 : ℝ)) ≤ (55629377089201 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_421 : ∀ t : ℝ, (7210739241 / 16000000000 : ℝ) < t → t ≤ (1805333410003 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-59636212621458767267965717 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1805333410003 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_422
  have hV : (21310362552014849979883597667402161 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7210739241 / 16000000000 : ℝ) := by norm_num
    refine le_trans V_pt_421 (Vfield_monotoneOn (show (7210739241 / 16000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7210739241 / 16000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_422 : (5331847216227603631183424037901693 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (1805333410003 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1805333410003 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (16795337010997 / 25000000000000 : ℝ) ≤ Real.sqrt (1805333410003 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1805333410003 / 4000000000000 : ℝ) ≤ (67181348043989 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (67181348043989 / 100000000000000 : ℝ) = (100000000000000 / 67181348043989 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16795337010997 / 25000000000000 : ℝ) = (1875000000000 / 16795337010997 : ℝ) := by norm_num
  have hL1 : (372482687351 / 1000000000000 : ℝ) ≤ Real.log (1 + (1805333410003 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1805333410003 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1223692225163 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67181348043989 / 220471297515248 : ℝ) ≤ (147889330809419 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (67181348043989 / 100000000000000 : ℝ) ≤ (147889330809419 / 250000000000000 : ℝ) := by
    have hw : (7529456094703 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (67181348043989 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (67181348043989 / 100000000000000 : ℝ) / (1 + (7529456094703 / 6250000000000 : ℝ)) = (67181348043989 / 220471297515248 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97923900355722061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 67181348043989 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 67181348043989 : ℝ) = (67181348043989 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 16795337010997 : ℝ) ≤ (13897222733399 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97923900355722061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (67181348043989 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16795337010997 / 25000000000000 : ℝ)) ≤ (13897222733399 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_422 : ∀ t : ℝ, (1805333410003 / 4000000000000 : ℝ) < t → t ≤ (451995502439 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-29773547481447026273602621 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (451995502439 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_423
  have hV : (5331847216227603631183424037901693 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1805333410003 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_422 (Vfield_monotoneOn (show (1805333410003 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1805333410003 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_423 : (2668050426343615867014266859467429 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (451995502439 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (451995502439 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (8403826346141 / 12500000000000 : ℝ) ≤ Real.sqrt (451995502439 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (451995502439 / 1000000000000 : ℝ) ≤ (67230610769129 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (67230610769129 / 100000000000000 : ℝ) = (100000000000000 / 67230610769129 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8403826346141 / 12500000000000 : ℝ) = (937500000000 / 8403826346141 : ℝ) := by norm_num
  have hL1 : (46617352363 / 125000000000 : ℝ) ≤ Real.log (1 + (451995502439 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((451995502439 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-7817150351193 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67230610769129 / 220498776028597 : ℝ) ≤ (36993542290481 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (67230610769129 / 100000000000000 : ℝ) ≤ (36993542290481 / 62500000000000 : ℝ) := by
    have hw : (120498776028597 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (67230610769129 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (67230610769129 / 100000000000000 : ℝ) / (1 + (120498776028597 / 100000000000000 : ℝ)) = (67230610769129 / 220498776028597 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97889965014720061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 67230610769129 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 67230610769129 : ℝ) = (67230610769129 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (937500000000 / 8403826346141 : ℝ) ≤ (2777424652311 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97889965014720061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (67230610769129 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8403826346141 / 12500000000000 : ℝ)) ≤ (2777424652311 / 25000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_423 : ∀ t : ℝ, (451995502439 / 1000000000000 : ℝ) < t → t ≤ (1810630609509 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-29729278968512408850044443 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1810630609509 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_424
  have hV : (2668050426343615867014266859467429 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (451995502439 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_423 (Vfield_monotoneOn (show (451995502439 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (451995502439 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_424 : (5340351553171358090476227730089781 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (1810630609509 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1810630609509 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (16819959355949 / 25000000000000 : ℝ) ≤ Real.sqrt (1810630609509 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1810630609509 / 4000000000000 : ℝ) ≤ (67279837423797 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (67279837423797 / 100000000000000 : ℝ) = (100000000000000 / 67279837423797 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16819959355949 / 25000000000000 : ℝ) = (1875000000000 / 16819959355949 : ℝ) := by norm_num
  have hL1 : (18669737124793 / 50000000000000 : ℝ) ≤ Real.log (1 + (1810630609509 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1810630609509 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-39013456988759 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67279837423797 / 220526248277180 : ℝ) ≤ (59223562697509 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (67279837423797 / 100000000000000 : ℝ) ≤ (59223562697509 / 100000000000000 : ℝ) := by
    have hw : (6026312413859 / 5000000000000 : ℝ) ≤ Real.sqrt (1 + (67279837423797 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (67279837423797 / 100000000000000 : ℝ) / (1 + (6026312413859 / 5000000000000 : ℝ)) = (67279837423797 / 220526248277180 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97856069981980661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 67279837423797 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 67279837423797 : ℝ) = (67279837423797 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 16819959355949 : ℝ) ≤ (111016366213591 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97856069981980661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (67279837423797 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16819959355949 / 25000000000000 : ℝ)) ≤ (111016366213591 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_424 : ∀ t : ℝ, (1810630609509 / 4000000000000 : ℝ) < t → t ≤ (906639604631 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-59370581234092626787987899 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (906639604631 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_425
  have hV : (5340351553171358090476227730089781 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1810630609509 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_424 (Vfield_monotoneOn (show (1810630609509 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1810630609509 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_425 : (21378397293800352305032170215723359 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (906639604631 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (906639604631 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (67329028087111 / 100000000000000 : ℝ) ≤ Real.sqrt (906639604631 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (906639604631 / 2000000000000 : ℝ) ≤ (8416128510889 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8416128510889 / 12500000000000 : ℝ) = (12500000000000 / 8416128510889 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (67329028087111 / 100000000000000 : ℝ) = (7500000000000 / 67329028087111 : ℝ) := by norm_num
  have hL1 : (9346261457903 / 25000000000000 : ℝ) ≤ Real.log (1 + (906639604631 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((906639604631 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-9735316650329 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67329028087112 / 220553714265281 : ℝ) ≤ (74071771891471 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8416128510889 / 12500000000000 : ℝ) ≤ (74071771891471 / 125000000000000 : ℝ) := by
    have hw : (120553714265281 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (8416128510889 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (8416128510889 / 12500000000000 : ℝ) / (1 + (120553714265281 / 100000000000000 : ℝ)) = (67329028087112 / 220553714265281 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97822215166312861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 8416128510889 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 8416128510889 : ℝ) = (8416128510889 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 67329028087111 : ℝ) ≤ (55467960796669 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97822215166312861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8416128510889 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (67329028087111 / 100000000000000 : ℝ)) ≤ (55467960796669 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_425 : ∀ t : ℝ, (906639604631 / 2000000000000 : ℝ) < t → t ≤ (363185561803 / 800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-59283145970861863865417953 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (363185561803 / 800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_426
  have hV : (21378397293800352305032170215723359 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (906639604631 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_425 (Vfield_monotoneOn (show (906639604631 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (906639604631 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_426 : (213953766770980679519433696538451 / 50000000000000000000000000000000 : ℝ) ≤ Vfield (363185561803 / 800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (363185561803 / 800000000000 : ℝ) := by norm_num
  have hs1 : (673781828379 / 1000000000000 : ℝ) ≤ Real.sqrt (363185561803 / 800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (363185561803 / 800000000000 : ℝ) ≤ (67378182837901 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (67378182837901 / 100000000000000 : ℝ) = (100000000000000 / 67378182837901 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (673781828379 / 1000000000000 : ℝ) = (25000000000 / 224593942793 : ℝ) := by norm_num
  have hL1 : (18715298327703 / 50000000000000 : ℝ) ≤ Real.log (1 + (363185561803 / 800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((363185561803 / 800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3109534423413 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67378182837901 / 220581173997177 : ℝ) ≤ (296456161013191 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (67378182837901 / 100000000000000 : ℝ) ≤ (296456161013191 / 500000000000000 : ℝ) := by
    have hw : (120581173997177 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (67378182837901 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (67378182837901 / 100000000000000 : ℝ) / (1 + (120581173997177 / 100000000000000 : ℝ)) = (67378182837901 / 220581173997177 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97788400476851461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 67378182837901 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 67378182837901 : ℝ) = (67378182837901 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (25000000000 / 224593942793 : ℝ) ≤ (22171130319521 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97788400476851461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (67378182837901 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (673781828379 / 1000000000000 : ℝ)) ≤ (22171130319521 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_426 : ∀ t : ℝ, (363185561803 / 800000000000 : ℝ) < t → t ≤ (28415256387 / 62500000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23678493818229755652875811 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (28415256387 / 62500000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_427
  have hV : (213953766770980679519433696538451 / 50000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (363185561803 / 800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_426 (Vfield_monotoneOn (show (363185561803 / 800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (363185561803 / 800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_427 : (1338271524094295108535399571350461 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (28415256387 / 62500000000 : ℝ) := by
  have hp : (0 : ℝ) < (28415256387 / 62500000000 : ℝ) := by norm_num
  have hs1 : (4214206359669 / 6250000000000 : ℝ) ≤ Real.sqrt (28415256387 / 62500000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (28415256387 / 62500000000 : ℝ) ≤ (13485460350941 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13485460350941 / 20000000000000 : ℝ) = (20000000000000 / 13485460350941 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4214206359669 / 6250000000000 : ℝ) = (156250000000 / 1404735453223 : ℝ) := by norm_num
  have hL1 : (1171128960621 / 3125000000000 : ℝ) ≤ Real.log (1 + (28415256387 / 62500000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((28415256387 / 62500000000 : ℝ) + (3 / 40) ^ 2) ≤ (-38797197763123 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67427301754705 / 220608627477142 : ℝ) ≤ (74156258570547 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13485460350941 / 20000000000000 : ℝ) ≤ (74156258570547 / 125000000000000 : ℝ) := by
    have hw : (60304313738571 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (13485460350941 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (13485460350941 / 20000000000000 : ℝ) / (1 + (60304313738571 / 50000000000000 : ℝ)) = (67427301754705 / 220608627477142 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97754625823052061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 13485460350941 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 13485460350941 : ℝ) = (13485460350941 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (156250000000 / 1404735453223 : ℝ) ≤ (55387777797761 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97754625823052061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13485460350941 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4214206359669 / 6250000000000 : ℝ)) ≤ (55387777797761 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_427 : ∀ t : ℝ, (28415256387 / 62500000000 : ℝ) < t → t ≤ (1821225008521 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23643932208579277329703449 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1821225008521 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_428
  have hV : (1338271524094295108535399571350461 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (28415256387 / 62500000000 : ℝ) := by norm_num
    refine le_trans V_pt_427 (Vfield_monotoneOn (show (28415256387 / 62500000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (28415256387 / 62500000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_428 : (21429300441888324639469118517549051 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1821225008521 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1821225008521 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (67476384915779 / 100000000000000 : ℝ) ≤ Real.sqrt (1821225008521 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1821225008521 / 4000000000000 : ℝ) ≤ (3373819245789 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3373819245789 / 5000000000000 : ℝ) = (5000000000000 / 3373819245789 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (67476384915779 / 100000000000000 : ℝ) = (7500000000000 / 67476384915779 : ℝ) := by norm_num
  have hL1 : (7504327220777 / 20000000000000 : ℝ) ≤ Real.log (1 + (1821225008521 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1821225008521 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-38725318714317 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (22492128305260 / 73545358236481 : ℝ) ≤ (296793707824003 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3373819245789 / 5000000000000 : ℝ) ≤ (296793707824003 / 500000000000000 : ℝ) := by
    have hw : (120636074709443 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (3373819245789 / 5000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3373819245789 / 5000000000000 : ℝ) / (1 + (120636074709443 / 100000000000000 : ℝ)) = (22492128305260 / 73545358236481 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97720891114689061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 3373819245789 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 3373819245789 : ℝ) = (3373819245789 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 67476384915779 : ℝ) ≤ (27673908239851 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97720891114689061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3373819245789 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (67476384915779 / 100000000000000 : ℝ)) ≤ (27673908239851 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_428 : ∀ t : ℝ, (1821225008521 / 4000000000000 : ℝ) < t → t ≤ (911936804137 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23609567405570013087947473 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (911936804137 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_429
  have hV : (21429300441888324639469118517549051 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1821225008521 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_428 (Vfield_monotoneOn (show (1821225008521 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1821225008521 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_429 : (2680780608627352044787990757458103 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (911936804137 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (911936804137 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (8440679049887 / 12500000000000 : ℝ) ≤ Real.sqrt (911936804137 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (911936804137 / 2000000000000 : ℝ) ≤ (67525432399097 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (67525432399097 / 100000000000000 : ℝ) = (100000000000000 / 67525432399097 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8440679049887 / 12500000000000 : ℝ) = (937500000000 / 8440679049887 : ℝ) := by norm_num
  have hL1 : (37567124766297 / 100000000000000 : ℝ) ≤ Real.log (1 + (911936804137 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((911936804137 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-38653542849147 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67525432399097 / 220663515698346 : ℝ) ≤ (296962182088163 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (67525432399097 / 100000000000000 : ℝ) ≤ (296962182088163 / 500000000000000 : ℝ) := by
    have hw : (60331757849173 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (67525432399097 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (67525432399097 / 100000000000000 : ℝ) / (1 + (60331757849173 / 50000000000000 : ℝ)) = (67525432399097 / 220663515698346 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97687196261857061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 67525432399097 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 67525432399097 : ℝ) = (67525432399097 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (937500000000 / 8440679049887 : ℝ) ≤ (27653970766183 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97687196261857061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (67525432399097 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8440679049887 / 12500000000000 : ℝ)) ≤ (27653970766183 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_429 : ∀ t : ℝ, (911936804137 / 2000000000000 : ℝ) < t → t ≤ (1826522208027 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-5893848409619210993592699 / 5000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1826522208027 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_430
  have hV : (2680780608627352044787990757458103 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (911936804137 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_429 (Vfield_monotoneOn (show (911936804137 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (911936804137 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_430 : (21463177689608280881569016518776767 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1826522208027 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1826522208027 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (67574444282343 / 100000000000000 : ℝ) ≤ Real.sqrt (1826522208027 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1826522208027 / 4000000000000 : ℝ) ≤ (8446805535293 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8446805535293 / 12500000000000 : ℝ) = (12500000000000 / 8446805535293 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (67574444282343 / 100000000000000 : ℝ) = (2500000000000 / 22524814760781 : ℝ) := by norm_num
  have hL1 : (37612592745933 / 100000000000000 : ℝ) ≤ Real.log (1 + (1826522208027 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1826522208027 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-19290934935897 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67574444282344 / 220690950448107 : ℝ) ≤ (148565228761309 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8446805535293 / 12500000000000 : ℝ) ≤ (148565228761309 / 250000000000000 : ℝ) := by
    have hw : (120690950448107 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (8446805535293 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (8446805535293 / 12500000000000 : ℝ) / (1 + (120690950448107 / 100000000000000 : ℝ)) = (67574444282344 / 220690950448107 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97653541174966061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 8446805535293 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 8446805535293 : ℝ) = (8446805535293 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 22524814760781 : ℝ) ≤ (110536305290133 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97653541174966061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8446805535293 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (67574444282343 / 100000000000000 : ℝ)) ≤ (110536305290133 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_430 : ∀ t : ℝ, (1826522208027 / 4000000000000 : ℝ) < t → t ≤ (91458540389 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-11770702742907122869398129 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (91458540389 / 200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_431
  have hV : (21463177689608280881569016518776767 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1826522208027 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_430 (Vfield_monotoneOn (show (1826522208027 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1826522208027 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_431 : (859203957051639830414760152221373 / 200000000000000000000000000000000 : ℝ) ≤ Vfield (91458540389 / 200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (91458540389 / 200000000000 : ℝ) := by norm_num
  have hs1 : (2704936825717 / 4000000000000 : ℝ) ≤ Real.sqrt (91458540389 / 200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (91458540389 / 200000000000 : ℝ) ≤ (33811710321463 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (33811710321463 / 50000000000000 : ℝ) = (50000000000000 / 33811710321463 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (2704936825717 / 4000000000000 : ℝ) = (300000000000 / 2704936825717 : ℝ) := by norm_num
  have hL1 : (4707255007699 / 12500000000000 : ℝ) ≤ Real.log (1 + (91458540389 / 200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((91458540389 / 200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-77020598975417 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67623420642926 / 220718378962981 : ℝ) ≤ (29729853457373 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (33811710321463 / 50000000000000 : ℝ) ≤ (29729853457373 / 50000000000000 : ℝ) := by
    have hw : (120718378962981 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (33811710321463 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (33811710321463 / 50000000000000 : ℝ) / (1 + (120718378962981 / 100000000000000 : ℝ)) = (67623420642926 / 220718378962981 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97619925764743661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 33811710321463 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 33811710321463 : ℝ) = (33811710321463 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (300000000000 / 2704936825717 : ℝ) ≤ (1380711237717 / 12500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97619925764743661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (33811710321463 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (2704936825717 / 4000000000000 : ℝ)) ≤ (1380711237717 / 12500000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_431 : ∀ t : ℝ, (91458540389 / 200000000000 : ℝ) < t → t ≤ (1831819407533 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-117537989226275349821332013 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1831819407533 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_432
  have hV : (859203957051639830414760152221373 / 200000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (91458540389 / 200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_431 (Vfield_monotoneOn (show (91458540389 / 200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (91458540389 / 200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_432 : (21497008601629070295950122374343161 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1831819407533 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1831819407533 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (67672361557969 / 100000000000000 : ℝ) ≤ Real.sqrt (1831819407533 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1831819407533 / 4000000000000 : ℝ) ≤ (6767236155797 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6767236155797 / 10000000000000 : ℝ) = (10000000000000 / 6767236155797 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (67672361557969 / 100000000000000 : ℝ) = (7500000000000 / 67672361557969 : ℝ) := by norm_num
  have hL1 : (37703466732049 / 100000000000000 : ℝ) ≤ Real.log (1 + (1831819407533 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1831819407533 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-7687766280721 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67672361557970 / 220745801247217 : ℝ) ≤ (2974664136863 / 10000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6767236155797 / 10000000000000 : ℝ) ≤ (2974664136863 / 5000000000000 : ℝ) := by
    have hw : (120745801247217 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (6767236155797 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (6767236155797 / 10000000000000 : ℝ) / (1 + (120745801247217 / 100000000000000 : ℝ)) = (67672361557970 / 220745801247217 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97586349942229661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 6767236155797 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 6767236155797 : ℝ) = (6767236155797 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 67672361557969 : ℝ) ≤ (27594415907817 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97586349942229661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6767236155797 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (67672361557969 / 100000000000000 : ℝ)) ≤ (27594415907817 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_432 : ∀ t : ℝ, (1831819407533 / 4000000000000 : ℝ) < t → t ≤ (917234003643 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-117369829534121487717015297 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (917234003643 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_433
  have hV : (21497008601629070295950122374343161 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1831819407533 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_432 (Vfield_monotoneOn (show (1831819407533 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1831819407533 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_433 : (10756953369055669176459544548396809 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (917234003643 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (917234003643 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (33860633552161 / 50000000000000 : ℝ) ≤ Real.sqrt (917234003643 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (917234003643 / 2000000000000 : ℝ) ≤ (67721267104323 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (67721267104323 / 100000000000000 : ℝ) = (100000000000000 / 67721267104323 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33860633552161 / 50000000000000 : ℝ) = (3750000000000 / 33860633552161 : ℝ) := by norm_num
  have hL1 : (37748872776051 / 100000000000000 : ℝ) ≤ Real.log (1 + (917234003643 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((917234003643 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-19183732663727 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67721267104323 / 220773217305059 : ℝ) ≤ (59526819060713 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (67721267104323 / 100000000000000 : ℝ) ≤ (59526819060713 / 100000000000000 : ℝ) := by
    have hw : (120773217305059 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (67721267104323 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (67721267104323 / 100000000000000 : ℝ) / (1 + (120773217305059 / 100000000000000 : ℝ)) = (67721267104323 / 220773217305059 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97552813618776661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 67721267104323 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 67721267104323 : ℝ) = (67721267104323 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 33860633552161 : ℝ) ≤ (55149299259899 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97552813618776661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (67721267104323 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33860633552161 / 50000000000000 : ℝ)) ≤ (55149299259899 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_433 : ∀ t : ℝ, (917234003643 / 2000000000000 : ℝ) < t → t ≤ (1837116607039 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-117202525644704512296950943 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1837116607039 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_434
  have hV : (10756953369055669176459544548396809 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (917234003643 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_433 (Vfield_monotoneOn (show (917234003643 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (917234003643 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_434 : (4306158671630949469604565359680759 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (1837116607039 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1837116607039 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (13554027471711 / 20000000000000 : ℝ) ≤ Real.sqrt (1837116607039 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1837116607039 / 4000000000000 : ℝ) ≤ (16942534339639 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16942534339639 / 25000000000000 : ℝ) = (25000000000000 / 16942534339639 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13554027471711 / 20000000000000 : ℝ) = (500000000000 / 4518009157237 : ℝ) := by norm_num
  have hL1 : (18897129106161 / 50000000000000 : ℝ) ≤ Real.log (1 + (1837116607039 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1837116607039 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-38296200968473 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (33885068679278 / 110400313570373 : ℝ) ≤ (74450394966803 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16942534339639 / 25000000000000 : ℝ) ≤ (74450394966803 / 125000000000000 : ℝ) := by
    have hw : (60400313570373 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (16942534339639 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (16942534339639 / 25000000000000 : ℝ) / (1 + (60400313570373 / 50000000000000 : ℝ)) = (33885068679278 / 110400313570373 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97519316706047261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 16942534339639 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 16942534339639 : ℝ) = (16942534339639 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 4518009157237 : ℝ) ≤ (22043940614791 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97519316706047261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16942534339639 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13554027471711 / 20000000000000 : ℝ)) ≤ (22043940614791 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_434 : ∀ t : ℝ, (1837116607039 / 4000000000000 : ℝ) < t → t ≤ (229970650849 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-58518028042366373187940343 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (229970650849 / 500000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_435
  have hV : (4306158671630949469604565359680759 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1837116607039 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_434 (Vfield_monotoneOn (show (1837116607039 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1837116607039 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_435 : (10773834242051922160007639348416889 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (229970650849 / 500000000000 : ℝ) := by
  have hp : (0 : ℝ) < (229970650849 / 500000000000 : ℝ) := by norm_num
  have hs1 : (33909486198481 / 50000000000000 : ℝ) ≤ Real.sqrt (229970650849 / 500000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (229970650849 / 500000000000 : ℝ) ≤ (67818972396963 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (67818972396963 / 100000000000000 : ℝ) = (100000000000000 / 67818972396963 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33909486198481 / 50000000000000 : ℝ) = (3750000000000 / 33909486198481 : ℝ) := by norm_num
  have hL1 : (37839623059559 / 100000000000000 : ℝ) ≤ Real.log (1 + (229970650849 / 500000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((229970650849 / 500000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-76450076074247 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67818972396963 / 220828030758512 : ℝ) ≤ (14898443390869 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (67818972396963 / 100000000000000 : ℝ) ≤ (14898443390869 / 25000000000000 : ℝ) := by
    have hw : (7551751922407 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (67818972396963 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (67818972396963 / 100000000000000 : ℝ) / (1 + (7551751922407 / 6250000000000 : ℝ)) = (67818972396963 / 220828030758512 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97485859116013661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 67818972396963 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 67818972396963 : ℝ) = (67818972396963 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 33909486198481 : ℝ) ≤ (11014097668779 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97485859116013661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (67818972396963 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33909486198481 / 50000000000000 : ℝ)) ≤ (11014097668779 / 100000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_435 : ∀ t : ℝ, (229970650849 / 500000000000 : ℝ) < t → t ≤ (368482761309 / 800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23374080103811575886951373 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (368482761309 / 800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_436
  have hV : (10773834242051922160007639348416889 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (229970650849 / 500000000000 : ℝ) := by norm_num
    refine le_trans V_pt_435 (Vfield_monotoneOn (show (229970650849 / 500000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (229970650849 / 500000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_436 : (21564532138231615911113290341442947 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (368482761309 / 800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (368482761309 / 800000000000 : ℝ) := by norm_num
  have hs1 : (67867772295563 / 100000000000000 : ℝ) ≤ Real.sqrt (368482761309 / 800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (368482761309 / 800000000000 : ℝ) ≤ (16966943073891 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16966943073891 / 25000000000000 : ℝ) = (25000000000000 / 16966943073891 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (67867772295563 / 100000000000000 : ℝ) = (7500000000000 / 67867772295563 : ℝ) := by norm_num
  have hL1 : (37884967336433 / 100000000000000 : ℝ) ≤ Real.log (1 + (368482761309 / 800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((368482761309 / 800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-38153976245099 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (5655647691297 / 18404619013549 : ℝ) ≤ (59627191918533 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16966943073891 / 25000000000000 : ℝ) ≤ (59627191918533 / 100000000000000 : ℝ) := by
    have hw : (30213857040647 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (16966943073891 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (16966943073891 / 25000000000000 : ℝ) / (1 + (30213857040647 / 25000000000000 : ℝ)) = (5655647691297 / 18404619013549 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97452440760956661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 16966943073891 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 16966943073891 : ℝ) = (16966943073891 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 67867772295563 : ℝ) ≤ (55031209379189 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97452440760956661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16966943073891 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (67867772295563 / 100000000000000 : ℝ)) ≤ (55031209379189 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_436 : ∀ t : ℝ, (368482761309 / 800000000000 : ℝ) < t → t ≤ (922531203149 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-116705539663770690384935149 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (922531203149 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_437
  have hV : (21564532138231615911113290341442947 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (368482761309 / 800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_436 (Vfield_monotoneOn (show (368482761309 / 800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (368482761309 / 800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_437 : (4316276868547955210113087792895149 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (922531203149 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (922531203149 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (13583307426021 / 20000000000000 : ℝ) ≤ Real.sqrt (922531203149 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (922531203149 / 2000000000000 : ℝ) ≤ (33958268565053 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (33958268565053 / 50000000000000 : ℝ) = (50000000000000 / 33958268565053 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13583307426021 / 20000000000000 : ℝ) = (500000000000 / 4527769142007 : ℝ) := by norm_num
  have hL1 : (4741286382699 / 12500000000000 : ℝ) ≤ Real.log (1 + (922531203149 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((922531203149 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-15233206122129 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (33958268565053 / 110441409678599 : ℝ) ≤ (298302855630139 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (33958268565053 / 50000000000000 : ℝ) ≤ (298302855630139 / 500000000000000 : ℝ) := by
    have hw : (60441409678599 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (33958268565053 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (33958268565053 / 50000000000000 : ℝ) / (1 + (60441409678599 / 50000000000000 : ℝ)) = (33958268565053 / 110441409678599 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97419061553461861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 33958268565053 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 33958268565053 : ℝ) = (33958268565053 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 4527769142007 : ℝ) ≤ (109984028685801 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97419061553461861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (33958268565053 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13583307426021 / 20000000000000 : ℝ)) ≤ (109984028685801 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_437 : ∀ t : ℝ, (922531203149 / 2000000000000 : ℝ) < t → t ≤ (1847711006051 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-29135363801931967508684791 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1847711006051 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_438
  have hV : (4316276868547955210113087792895149 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (922531203149 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_437 (Vfield_monotoneOn (show (922531203149 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (922531203149 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_438 : (10799112559879197511442551651030839 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1847711006051 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1847711006051 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (33982633488031 / 50000000000000 : ℝ) ≤ Real.sqrt (1847711006051 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1847711006051 / 4000000000000 : ℝ) ≤ (67965266976063 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (67965266976063 / 100000000000000 : ℝ) = (100000000000000 / 67965266976063 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33982633488031 / 50000000000000 : ℝ) = (3750000000000 / 33982633488031 : ℝ) := by norm_num
  have hL1 : (7595118850731 / 20000000000000 : ℝ) ≤ Real.log (1 + (1847711006051 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1847711006051 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-38012154931937 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (67965266976063 / 220910204346562 : ℝ) ≤ (149234778182671 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (67965266976063 / 100000000000000 : ℝ) ≤ (149234778182671 / 250000000000000 : ℝ) := by
    have hw : (60455102173281 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (67965266976063 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (67965266976063 / 100000000000000 : ℝ) / (1 + (60455102173281 / 50000000000000 : ℝ)) = (67965266976063 / 220910204346562 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97385721406421261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 67965266976063 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 67965266976063 : ℝ) = (67965266976063 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 33982633488031 : ℝ) ≤ (109905805873129 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97385721406421261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (67965266976063 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33982633488031 / 50000000000000 : ℝ)) ≤ (109905805873129 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_438 : ∀ t : ℝ, (1847711006051 / 4000000000000 : ℝ) < t → t ≤ (462589901451 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-116378129741523110393008819 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (462589901451 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_439
  have hV : (10799112559879197511442551651030839 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1847711006051 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_438 (Vfield_monotoneOn (show (1847711006051 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1847711006051 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_439 : (135094090570924106318435105488401 / 31250000000000000000000000000000 : ℝ) ≤ Vfield (462589901451 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (462589901451 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (425087261929 / 625000000000 : ℝ) ≤ Real.sqrt (462589901451 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (462589901451 / 1000000000000 : ℝ) ≤ (68013961908641 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (68013961908641 / 100000000000000 : ℝ) = (100000000000000 / 68013961908641 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (425087261929 / 625000000000 : ℝ) = (46875000000 / 425087261929 : ℝ) := by norm_num
  have hL1 : (38020876931221 / 100000000000000 : ℝ) ≤ Real.log (1 + (462589901451 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((462589901451 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-18970697420149 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (68013961908641 / 220937583134896 : ℝ) ≤ (298636062232307 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (68013961908641 / 100000000000000 : ℝ) ≤ (298636062232307 / 500000000000000 : ℝ) := by
    have hw : (7558598945931 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (68013961908641 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (68013961908641 / 100000000000000 : ℝ) / (1 + (7558598945931 / 6250000000000 : ℝ)) = (68013961908641 / 220937583134896 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97352420233028261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 68013961908641 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 68013961908641 : ℝ) = (68013961908641 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (46875000000 / 425087261929 : ℝ) ≤ (27456937431599 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97352420233028261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (68013961908641 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (425087261929 / 625000000000 : ℝ)) ≤ (27456937431599 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_439 : ∀ t : ℝ, (462589901451 / 1000000000000 : ℝ) < t → t ≤ (1853008205557 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-116215546693062536606512611 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1853008205557 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_440
  have hV : (135094090570924106318435105488401 / 31250000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (462589901451 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_439 (Vfield_monotoneOn (show (462589901451 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (462589901451 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
