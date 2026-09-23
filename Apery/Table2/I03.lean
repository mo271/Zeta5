import Apery.Table2.U03
import Apery.Table2.U04

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_120 : (8255848645804040455713794349713157 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1894293572403 / 25600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1894293572403 / 25600000000000 : ℝ) := by norm_num
  have hs1 : (27202176874653 / 100000000000000 : ℝ) ≤ Real.sqrt (1894293572403 / 25600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1894293572403 / 25600000000000 : ℝ) ≤ (13601088437327 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13601088437327 / 50000000000000 : ℝ) = (50000000000000 / 13601088437327 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (27202176874653 / 100000000000000 : ℝ) = (2500000000000 / 9067392291551 : ℝ) := by norm_num
  have hL1 : (7138612519649 / 100000000000000 : ℝ) ≤ Real.log (1 + (1894293572403 / 25600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1894293572403 / 25600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-31630992209423 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13601088437327 / 50000000000000 : ℝ) ≤ (265595270225703 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130520105656919361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 13601088437327 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 13601088437327 : ℝ) = (13601088437327 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 9067392291551 : ℝ) ≤ (269029172493049 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130520105656919361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13601088437327 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (27202176874653 / 100000000000000 : ℝ)) ≤ (269029172493049 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_120 : ∀ t : ℝ, (1894293572403 / 25600000000000 : ℝ) < t → t ≤ (297034306573 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-49963183878705260116541519 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (297034306573 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_121
  have hV : (8255848645804040455713794349713157 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1894293572403 / 25600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_120 (Vfield_monotoneOn (show (1894293572403 / 25600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1894293572403 / 25600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_121 : (4134760763515008201358439756407653 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (297034306573 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (297034306573 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (13625213451837 / 50000000000000 : ℝ) ≤ Real.sqrt (297034306573 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (297034306573 / 4000000000000 : ℝ) ≤ (1090017076147 / 4000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1090017076147 / 4000000000000 : ℝ) = (4000000000000 / 1090017076147 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13625213451837 / 50000000000000 : ℝ) = (1250000000000 / 4541737817279 : ℝ) := by norm_num
  have hL1 : (7163072748401 / 100000000000000 : ℝ) ≤ Real.log (1 + (297034306573 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((297034306573 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-252718499519369 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1090017076147 / 4000000000000 : ℝ) ≤ (266044472429787 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130475185436510961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (4000000000000 / 1090017076147 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (4000000000000 / 1090017076147 : ℝ) = (1090017076147 / 4000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 4541737817279 : ℝ) ≤ (134287711202839 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130475185436510961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1090017076147 / 4000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13625213451837 / 50000000000000 : ℝ)) ≤ (134287711202839 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_121 : ∀ t : ℝ, (297034306573 / 4000000000000 : ℝ) < t → t ≤ (9538727758657 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-249677503671267147367474199 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9538727758657 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_122
  have hV : (4134760763515008201358439756407653 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (297034306573 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_121 (Vfield_monotoneOn (show (297034306573 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (297034306573 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_122 : (8283181159943458240272982868193159 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9538727758657 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9538727758657 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (27298591651311 / 100000000000000 : ℝ) ≤ Real.sqrt (9538727758657 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9538727758657 / 128000000000000 : ℝ) ≤ (1706161978207 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1706161978207 / 6250000000000 : ℝ) = (6250000000000 / 1706161978207 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (27298591651311 / 100000000000000 : ℝ) = (2500000000000 / 9099530550437 : ℝ) := by norm_num
  have hL1 : (1796881748897 / 25000000000000 : ℝ) ≤ Real.log (1 + (9538727758657 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9538727758657 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-63097535773919 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1706161978207 / 6250000000000 : ℝ) ≤ (133246385509551 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130430355577579461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 1706161978207 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 1706161978207 : ℝ) = (1706161978207 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 9099530550437 : ℝ) ≤ (67030990400867 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130430355577579461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1706161978207 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (27298591651311 / 100000000000000 : ℝ)) ≤ (67030990400867 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_122 : ∀ t : ℝ, (9538727758657 / 128000000000000 : ℝ) < t → t ≤ (4786178853489 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-124770315330541651855706801 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4786178853489 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_123
  have hV : (8283181159943458240272982868193159 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9538727758657 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_122 (Vfield_monotoneOn (show (9538727758657 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9538727758657 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_123 : (331873102893838308704147784532063 / 200000000000000000000000000000000 : ℝ) ≤ Vfield (4786178853489 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4786178853489 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (1093866862727 / 4000000000000 : ℝ) ≤ Real.sqrt (4786178853489 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4786178853489 / 64000000000000 : ℝ) ≤ (1709166973011 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1709166973011 / 6250000000000 : ℝ) = (6250000000000 / 1709166973011 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1093866862727 / 4000000000000 : ℝ) = (300000000000 / 1093866862727 : ℝ) := by norm_num
  have hL1 : (3605987632067 / 50000000000000 : ℝ) ≤ Real.log (1 + (4786178853489 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4786178853489 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-252062861323667 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1709166973011 / 6250000000000 : ℝ) ≤ (26694017062857 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130385615616632661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 1709166973011 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 1709166973011 : ℝ) = (1709166973011 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (300000000000 / 1093866862727 : ℝ) ≤ (1672967318073 / 6250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130385615616632661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1709166973011 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1093866862727 / 4000000000000 : ℝ)) ≤ (1672967318073 / 6250000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_123 : ∀ t : ℝ, (4786178853489 / 64000000000000 : ℝ) < t → t ≤ (9605987655299 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-249405244886935742895020033 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9605987655299 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_124
  have hV : (331873102893838308704147784532063 / 200000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4786178853489 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_123 (Vfield_monotoneOn (show (4786178853489 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4786178853489 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_124 : (207761519801805563633162460070187 / 125000000000000000000000000000000 : ℝ) ≤ Vfield (9605987655299 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9605987655299 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (684866677523 / 2500000000000 : ℝ) ≤ Real.sqrt (9605987655299 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9605987655299 / 128000000000000 : ℝ) ≤ (27394667100921 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (27394667100921 / 100000000000000 : ℝ) = (100000000000000 / 27394667100921 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (684866677523 / 2500000000000 : ℝ) = (187500000000 / 684866677523 : ℝ) := by norm_num
  have hL1 : (1809104389241 / 25000000000000 : ℝ) ≤ Real.log (1 + (9605987655299 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9605987655299 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-251736647191999 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (27394667100921 / 100000000000000 : ℝ) ≤ (267386675852903 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130340965094199361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 27394667100921 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 27394667100921 : ℝ) = (27394667100921 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (187500000000 / 684866677523 : ℝ) ≤ (267227831300269 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130340965094199361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (27394667100921 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (684866677523 / 2500000000000 : ℝ)) ≤ (267227831300269 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_124 : ∀ t : ℝ, (9605987655299 / 128000000000000 : ℝ) < t → t ≤ (481980880181 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-249271294580185520743868697 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (481980880181 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_125
  have hV : (207761519801805563633162460070187 / 125000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9605987655299 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_124 (Vfield_monotoneOn (show (9605987655299 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9605987655299 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_125 : (1664816169397592586611210957689971 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (481980880181 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (481980880181 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (5488515738459 / 20000000000000 : ℝ) ≤ Real.sqrt (481980880181 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (481980880181 / 6400000000000 : ℝ) ≤ (3430322336537 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3430322336537 / 12500000000000 : ℝ) = (12500000000000 / 3430322336537 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5488515738459 / 20000000000000 : ℝ) = (500000000000 / 1829505246153 : ℝ) := by norm_num
  have hL1 : (7260853876997 / 100000000000000 : ℝ) ≤ Real.log (1 + (481980880181 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((481980880181 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-251411493757721 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3430322336537 / 12500000000000 : ℝ) ≤ (267832291247123 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130296403554777361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 3430322336537 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 3430322336537 : ℝ) = (3430322336537 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (500000000000 / 1829505246153 : ℝ) ≤ (66695781020121 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130296403554777361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3430322336537 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5488515738459 / 20000000000000 : ℝ)) ≤ (66695781020121 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_125 : ∀ t : ℝ, (481980880181 / 6400000000000 : ℝ) < t → t ≤ (9673247551941 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-49827746265498395485769121 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9673247551941 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_126
  have hV : (1664816169397592586611210957689971 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (481980880181 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_125 (Vfield_monotoneOn (show (481980880181 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (481980880181 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_126 : (8337687764986923013311784912270879 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9673247551941 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9673247551941 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (27490406781191 / 100000000000000 : ℝ) ≤ Real.sqrt (9673247551941 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9673247551941 / 128000000000000 : ℝ) ≤ (3436300847649 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3436300847649 / 12500000000000 : ℝ) = (12500000000000 / 3436300847649 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (27490406781191 / 100000000000000 : ℝ) = (7500000000000 / 27490406781191 : ℝ) := by norm_num
  have hL1 : (7285284227151 / 100000000000000 : ℝ) ≤ Real.log (1 + (9673247551941 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9673247551941 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-62771848536347 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3436300847649 / 12500000000000 : ℝ) ≤ (134138510663521 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130251930546785461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 3436300847649 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 3436300847649 : ℝ) = (3436300847649 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 27490406781191 : ℝ) ≤ (266340630701559 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130251930546785461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3436300847649 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (27490406781191 / 100000000000000 : ℝ)) ≤ (266340630701559 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_126 : ∀ t : ℝ, (9673247551941 / 128000000000000 : ℝ) < t → t ≤ (4853438750131 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-62251877440255292728959381 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4853438750131 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_127
  have hV : (8337687764986923013311784912270879 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9673247551941 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_126 (Vfield_monotoneOn (show (9673247551941 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9673247551941 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_127 : (8351281573988253570656368980232841 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (4853438750131 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4853438750131 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (27538151802689 / 100000000000000 : ℝ) ≤ Real.sqrt (4853438750131 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4853438750131 / 64000000000000 : ℝ) ≤ (2753815180269 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2753815180269 / 10000000000000 : ℝ) = (10000000000000 / 2753815180269 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (27538151802689 / 100000000000000 : ℝ) = (7500000000000 / 27538151802689 : ℝ) := by norm_num
  have hL1 : (3654854305171 / 50000000000000 : ℝ) ≤ Real.log (1 + (4853438750131 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4853438750131 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-25076434154619 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2753815180269 / 10000000000000 : ℝ) ≤ (268720870569743 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130207545622515361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 2753815180269 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 2753815180269 : ℝ) = (2753815180269 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 27538151802689 : ℝ) ≤ (13295016642373 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130207545622515361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2753815180269 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (27538151802689 / 100000000000000 : ℝ)) ≤ (13295016642373 / 50000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_127 : ∀ t : ℝ, (4853438750131 / 64000000000000 : ℝ) < t → t ≤ (1221767174613 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-248748923832938847213987451 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1221767174613 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_128
  have hV : (8351281573988253570656368980232841 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4853438750131 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_127 (Vfield_monotoneOn (show (4853438750131 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4853438750131 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_128 : (8378429976779120180167622282800763 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1221767174613 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1221767174613 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (27633394365027 / 100000000000000 : ℝ) ≤ Real.sqrt (1221767174613 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1221767174613 / 16000000000000 : ℝ) ≤ (6908348591257 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6908348591257 / 25000000000000 : ℝ) = (25000000000000 / 6908348591257 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (27633394365027 / 100000000000000 : ℝ) = (2500000000000 / 9211131455009 : ℝ) := by norm_num
  have hL1 : (7358539487493 / 100000000000000 : ℝ) ≤ Real.log (1 + (1221767174613 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1221767174613 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-125060675239997 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6908348591257 / 25000000000000 : ℝ) ≤ (269605944260853 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130119038253404361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 6908348591257 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 6908348591257 : ℝ) = (6908348591257 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 9211131455009 : ℝ) ≤ (132513125752141 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130119038253404361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6908348591257 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (27633394365027 / 100000000000000 : ℝ)) ≤ (132513125752141 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_128 : ∀ t : ℝ, (1221767174613 / 16000000000000 : ℝ) < t → t ≤ (4920698646773 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-248495225116423016485412417 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4920698646773 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_129
  have hV : (8378429976779120180167622282800763 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1221767174613 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_128 (Vfield_monotoneOn (show (1221767174613 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1221767174613 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_129 : (8405526279100000634119290847261433 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (4920698646773 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4920698646773 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (27728309785457 / 100000000000000 : ℝ) ≤ Real.sqrt (4920698646773 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4920698646773 / 64000000000000 : ℝ) ≤ (13864154892729 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13864154892729 / 50000000000000 : ℝ) = (50000000000000 / 13864154892729 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (27728309785457 / 100000000000000 : ℝ) = (7500000000000 / 27728309785457 : ℝ) := by norm_num
  have hL1 : (1481469306347 / 20000000000000 : ℝ) ≤ Real.log (1 + (4920698646773 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4920698646773 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-124741233694529 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13864154892729 / 50000000000000 : ℝ) ≤ (270487547379793 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130030877941510361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 13864154892729 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 13864154892729 : ℝ) = (13864154892729 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 27728309785457 : ℝ) ≤ (66040184424441 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130030877941510361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13864154892729 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (27728309785457 / 100000000000000 : ℝ)) ≤ (66040184424441 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_129 : ∀ t : ℝ, (4920698646773 / 64000000000000 : ℝ) < t → t ≤ (2477164297547 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-248246136045350992819081359 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2477164297547 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_130
  have hV : (8405526279100000634119290847261433 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4920698646773 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_129 (Vfield_monotoneOn (show (4920698646773 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4920698646773 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_130 : (2108142676228114904131799351557383 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (2477164297547 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2477164297547 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (6955725353007 / 25000000000000 : ℝ) ≤ Real.sqrt (2477164297547 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2477164297547 / 32000000000000 : ℝ) ≤ (27822901412029 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (27822901412029 / 100000000000000 : ℝ) = (100000000000000 / 27822901412029 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6955725353007 / 25000000000000 : ℝ) = (625000000000 / 2318575117669 : ℝ) := by norm_num
  have hL1 : (7456129766321 / 100000000000000 : ℝ) ≤ Real.log (1 + (2477164297547 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2477164297547 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-49769528023187 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (27822901412029 / 100000000000000 : ℝ) ≤ (135682857197609 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (129943061239967861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 27822901412029 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 27822901412029 : ℝ) = (27822901412029 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (625000000000 / 2318575117669 : ℝ) ≤ (263303652312281 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (129943061239967861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (27822901412029 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6955725353007 / 25000000000000 : ℝ)) ≤ (263303652312281 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_130 : ∀ t : ℝ, (2477164297547 / 32000000000000 : ℝ) < t → t ≤ (997591708683 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-248001407922547394337805271 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (997591708683 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_131
  have hV : (2108142676228114904131799351557383 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2477164297547 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_130 (Vfield_monotoneOn (show (2477164297547 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2477164297547 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_131 : (2114890869579661347438068052204073 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (997591708683 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (997591708683 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (6979293134017 / 25000000000000 : ℝ) ≤ Real.sqrt (997591708683 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (997591708683 / 12800000000000 : ℝ) ≤ (27917172536069 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (27917172536069 / 100000000000000 : ℝ) = (100000000000000 / 27917172536069 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6979293134017 / 25000000000000 : ℝ) = (1875000000000 / 6979293134017 : ℝ) := by norm_num
  have hL1 : (938111151809 / 12500000000000 : ℝ) ≤ Real.log (1 + (997591708683 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((997591708683 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-248216817490249 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (27917172536069 / 100000000000000 : ℝ) ≤ (136120239599517 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (129855584759586261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 27917172536069 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 27917172536069 : ℝ) = (27917172536069 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 6979293134017 : ℝ) ≤ (16403428710979 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (129855584759586261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (27917172536069 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6979293134017 / 25000000000000 : ℝ)) ≤ (16403428710979 / 62500000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_131 : ∀ t : ℝ, (997591708683 / 12800000000000 : ℝ) < t → t ≤ (627698561467 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-123880408336961373827358869 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (627698561467 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_132
  have hV : (2114890869579661347438068052204073 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (997591708683 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_131 (Vfield_monotoneOn (show (997591708683 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (997591708683 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_132 : (8486504823483349790725524291531111 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (627698561467 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (627698561467 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (28011126393519 / 100000000000000 : ℝ) ≤ Real.sqrt (627698561467 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (627698561467 / 8000000000000 : ℝ) ≤ (350139079919 / 1250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (350139079919 / 1250000000000 : ℝ) = (1250000000000 / 350139079919 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (28011126393519 / 100000000000000 : ℝ) = (2500000000000 / 9337042131173 : ℝ) := by norm_num
  have hL1 : (755362489937 / 10000000000000 : ℝ) ≤ Real.log (1 + (627698561467 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((627698561467 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-247589949303947 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (350139079919 / 1250000000000 : ℝ) ≤ (273111875119903 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (129768445167499361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1250000000000 / 350139079919 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (1250000000000 / 350139079919 : ℝ) = (350139079919 / 1250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 9337042131173 : ℝ) ≤ (130807112984217 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (129768445167499361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (350139079919 / 1250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (28011126393519 / 100000000000000 : ℝ)) ≤ (130807112984217 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_132 : ∀ t : ℝ, (627698561467 / 8000000000000 : ℝ) < t → t ≤ (5055218440057 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-247524159389312553445619867 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5055218440057 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_133
  have hV : (8486504823483349790725524291531111 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (627698561467 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_132 (Vfield_monotoneOn (show (627698561467 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (627698561467 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_133 : (8513394964563148012132416560681253 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (5055218440057 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5055218440057 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (28104766166237 / 100000000000000 : ℝ) ≤ Real.sqrt (5055218440057 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5055218440057 / 64000000000000 : ℝ) ≤ (14052383083119 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (14052383083119 / 50000000000000 : ℝ) = (50000000000000 / 14052383083119 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (28104766166237 / 100000000000000 : ℝ) = (7500000000000 / 28104766166237 : ℝ) := by norm_num
  have hL1 : (7602336844169 / 100000000000000 : ℝ) ≤ Real.log (1 + (5055218440057 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5055218440057 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-246966986287317 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (14052383083119 / 50000000000000 : ℝ) ≤ (136989967468197 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (129681639185850261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 14052383083119 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 14052383083119 : ℝ) = (14052383083119 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 28104766166237 : ℝ) ≤ (130390811068087 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (129681639185850261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (14052383083119 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (28104766166237 / 100000000000000 : ℝ)) ≤ (130390811068087 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_133 : ∀ t : ℝ, (5055218440057 / 64000000000000 : ℝ) < t → t ≤ (2544424194189 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-61822812868387301520613851 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2544424194189 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_134
  have hV : (8513394964563148012132416560681253 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5055218440057 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_133 (Vfield_monotoneOn (show (5055218440057 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5055218440057 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_134 : (2135058531408686934031380286363659 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (2544424194189 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2544424194189 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (7049523745811 / 25000000000000 : ℝ) ≤ Real.sqrt (2544424194189 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2544424194189 / 32000000000000 : ℝ) ≤ (5639618996649 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5639618996649 / 20000000000000 : ℝ) = (20000000000000 / 5639618996649 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7049523745811 / 25000000000000 : ℝ) = (1875000000000 / 7049523745811 : ℝ) := by norm_num
  have hL1 : (478189066999 / 6250000000000 : ℝ) ≤ Real.log (1 + (2544424194189 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2544424194189 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-246347880085753 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5639618996649 / 20000000000000 : ℝ) ≤ (34355586361207 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (129595163590524061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 5639618996649 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 5639618996649 : ℝ) = (5639618996649 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 7049523745811 : ℝ) ≤ (129978460402517 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (129595163590524061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5639618996649 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7049523745811 / 25000000000000 : ℝ)) ≤ (129978460402517 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_134 : ∀ t : ℝ, (2544424194189 / 32000000000000 : ℝ) < t → t ≤ (5122478336699 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-49412384856229445149178749 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5122478336699 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_135
  have hV : (2135058531408686934031380286363659 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2544424194189 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_134 (Vfield_monotoneOn (show (2544424194189 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2544424194189 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_135 : (171340450612617473888940517294591 / 100000000000000000000000000000000 : ℝ) ≤ Vfield (5122478336699 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5122478336699 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (565822318439 / 2000000000000 : ℝ) ≤ Real.sqrt (5122478336699 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5122478336699 / 64000000000000 : ℝ) ≤ (28291115921951 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (28291115921951 / 100000000000000 : ℝ) = (100000000000000 / 28291115921951 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (565822318439 / 2000000000000 : ℝ) = (150000000000 / 565822318439 : ℝ) := by norm_num
  have hL1 : (76996896059 / 1000000000000 : ℝ) ≤ Real.log (1 + (5122478336699 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5122478336699 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-61433145809307 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (28291115921951 / 100000000000000 : ℝ) ≤ (8615817959243 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (129509015209912061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 28291115921951 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 28291115921951 : ℝ) = (28291115921951 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (150000000000 / 565822318439 : ℝ) ≤ (32392499712513 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (129509015209912061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (28291115921951 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (565822318439 / 2000000000000 : ℝ)) ≤ (32392499712513 / 125000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_135 : ∀ t : ℝ, (5122478336699 / 64000000000000 : ℝ) < t → t ≤ (257805414251 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-246836023137311811942994077 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (257805414251 / 3200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_136
  have hV : (171340450612617473888940517294591 / 100000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5122478336699 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_135 (Vfield_monotoneOn (show (5122478336699 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5122478336699 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_136 : (4296880201639376465420864571655461 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (257805414251 / 3200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (257805414251 / 3200000000000 : ℝ) := by norm_num
  have hs1 : (14191916004669 / 50000000000000 : ℝ) ≤ Real.sqrt (257805414251 / 3200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (257805414251 / 3200000000000 : ℝ) ≤ (28383832009339 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (28383832009339 / 100000000000000 : ℝ) = (100000000000000 / 28383832009339 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14191916004669 / 50000000000000 : ℝ) = (1250000000000 / 4730638668223 : ℝ) := by norm_num
  have hL1 : (3874165234483 / 50000000000000 : ℝ) ≤ Real.log (1 + (257805414251 / 3200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((257805414251 / 3200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-49024209830093 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (28383832009339 / 100000000000000 : ℝ) ≤ (276564417557777 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (129423190923711961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 28383832009339 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 28383832009339 : ℝ) = (28383832009339 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 4730638668223 : ℝ) ≤ (64582682816651 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (129423190923711961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (28383832009339 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14191916004669 / 50000000000000 : ℝ)) ≤ (64582682816651 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_136 : ∀ t : ℝ, (257805414251 / 3200000000000 : ℝ) < t → t ≤ (2611684090831 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-246393940397127586446417283 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2611684090831 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_137
  have hV : (4296880201639376465420864571655461 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (257805414251 / 3200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_136 (Vfield_monotoneOn (show (257805414251 / 3200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (257805414251 / 3200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_137 : (1080885680633368657831584379052707 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (2611684090831 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2611684090831 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (3571045186603 / 12500000000000 : ℝ) ≤ Real.sqrt (2611684090831 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2611684090831 / 32000000000000 : ℝ) ≤ (1142734459713 / 4000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1142734459713 / 4000000000000 : ℝ) = (4000000000000 / 1142734459713 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3571045186603 / 12500000000000 : ℝ) = (937500000000 / 3571045186603 : ℝ) := by norm_num
  have hL1 : (7845541274579 / 100000000000000 : ℝ) ≤ Real.log (1 + (2611684090831 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2611684090831 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24390908712447 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1142734459713 / 4000000000000 : ℝ) ≤ (139135651382827 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (129252502402924261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (4000000000000 / 1142734459713 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (4000000000000 / 1142734459713 : ℝ) = (1142734459713 / 4000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (937500000000 / 3571045186603 : ℝ) ≤ (128367347670667 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (129252502402924261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1142734459713 / 4000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3571045186603 / 12500000000000 : ℝ)) ≤ (128367347670667 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_137 : ∀ t : ℝ, (2611684090831 / 32000000000000 : ℝ) < t → t ≤ (165332127447 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-15372749241912602296996611 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (165332127447 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_138
  have hV : (1080885680633368657831584379052707 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2611684090831 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_137 (Vfield_monotoneOn (show (2611684090831 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2611684090831 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_138 : (1087526379321051453729565793141427 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (165332127447 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (165332127447 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (3593963335483 / 12500000000000 : ℝ) ≤ Real.sqrt (165332127447 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (165332127447 / 2000000000000 : ℝ) ≤ (5750341336773 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5750341336773 / 20000000000000 : ℝ) = (20000000000000 / 5750341336773 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3593963335483 / 12500000000000 : ℝ) = (937500000000 / 3593963335483 : ℝ) := by norm_num
  have hL1 : (7942657672553 / 100000000000000 : ℝ) ≤ Real.log (1 + (165332127447 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((165332127447 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-15169477368989 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5750341336773 / 20000000000000 : ℝ) ≤ (139982793154833 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (129083074048523061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 5750341336773 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 5750341336773 : ℝ) = (5750341336773 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (937500000000 / 3593963335483 : ℝ) ≤ (127583946082753 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (129083074048523061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5750341336773 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3593963335483 / 12500000000000 : ℝ)) ≤ (127583946082753 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_138 : ∀ t : ℝ, (165332127447 / 2000000000000 : ℝ) < t → t ≤ (2678943987473 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-122772644821086169472119217 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2678943987473 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_139
  have hV : (1087526379321051453729565793141427 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (165332127447 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_138 (Vfield_monotoneOn (show (165332127447 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (165332127447 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_139 : (8753138948652169285522824891250547 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2678943987473 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2678943987473 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (28933890095963 / 100000000000000 : ℝ) ≤ Real.sqrt (2678943987473 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2678943987473 / 32000000000000 : ℝ) ≤ (7233472523991 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7233472523991 / 25000000000000 : ℝ) = (25000000000000 / 7233472523991 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (28933890095963 / 100000000000000 : ℝ) = (7500000000000 / 28933890095963 : ℝ) := by norm_num
  have hL1 : (8039679846079 / 100000000000000 : ℝ) ≤ Real.log (1 + (2678943987473 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2678943987473 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-60382089506539 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7233472523991 / 25000000000000 : ℝ) ≤ (281647500487393 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (128914882630750361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 7233472523991 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 7233472523991 : ℝ) = (7233472523991 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 28933890095963 : ℝ) ≤ (253629439786939 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (128914882630750361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7233472523991 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (28933890095963 / 100000000000000 : ℝ)) ≤ (253629439786939 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_139 : ∀ t : ℝ, (2678943987473 / 32000000000000 : ℝ) < t → t ≤ (1356286967897 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-9805483288477005418422551 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1356286967897 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_140
  have hV : (8753138948652169285522824891250547 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2678943987473 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_139 (Vfield_monotoneOn (show (2678943987473 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2678943987473 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_140 : (8805870956040494406524420712334639 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1356286967897 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1356286967897 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (29114933538231 / 100000000000000 : ℝ) ≤ Real.sqrt (1356286967897 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1356286967897 / 16000000000000 : ℝ) ≤ (3639366692279 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3639366692279 / 12500000000000 : ℝ) = (12500000000000 / 3639366692279 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (29114933538231 / 100000000000000 : ℝ) = (2500000000000 / 9704977846077 : ℝ) := by norm_num
  have hL1 : (8136607977817 / 100000000000000 : ℝ) ≤ Real.log (1 + (1356286967897 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1356286967897 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-120179458039649 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3639366692279 / 12500000000000 : ℝ) ≤ (283317270424253 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (128747905637064361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 3639366692279 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 3639366692279 : ℝ) = (3639366692279 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 9704977846077 : ℝ) ≤ (252118493075443 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (128747905637064361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3639366692279 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (29114933538231 / 100000000000000 : ℝ)) ≤ (252118493075443 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_140 : ∀ t : ℝ, (1356286967897 / 16000000000000 : ℝ) < t → t ≤ (694958458109 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-244349529556125521967906807 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (694958458109 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_141
  have hV : (8805870956040494406524420712334639 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1356286967897 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_140 (Vfield_monotoneOn (show (1356286967897 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1356286967897 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_141 : (8910754277329386803356343588459097 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (694958458109 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (694958458109 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (29473684408913 / 100000000000000 : ℝ) ≤ Real.sqrt (694958458109 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (694958458109 / 8000000000000 : ℝ) ≤ (14736842204457 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (14736842204457 / 50000000000000 : ℝ) = (50000000000000 / 14736842204457 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (29473684408913 / 100000000000000 : ℝ) = (7500000000000 / 29473684408913 : ℝ) := by norm_num
  have hL1 : (104127285549 / 1250000000000 : ℝ) ≤ Real.log (1 + (694958458109 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((694958458109 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-238060277269029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (14736842204457 / 50000000000000 : ℝ) ≤ (57324248810153 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (128417508274413161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 14736842204457 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 14736842204457 : ℝ) = (14736842204457 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 29473684408913 : ℝ) ≤ (7786747145123 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (128417508274413161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (14736842204457 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (29473684408913 / 100000000000000 : ℝ)) ≤ (7786747145123 / 31250000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_141 : ∀ t : ℝ, (694958458109 / 8000000000000 : ℝ) < t → t ≤ (1423546864539 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-30449599884199640514046187 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1423546864539 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_142
  have hV : (8910754277329386803356343588459097 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (694958458109 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_141 (Vfield_monotoneOn (show (694958458109 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (694958458109 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_142 : (4507437470006386305024591833715237 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1423546864539 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1423546864539 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (14914060398973 / 50000000000000 : ℝ) ≤ Real.sqrt (1423546864539 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1423546864539 / 16000000000000 : ℝ) ≤ (29828120797947 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (29828120797947 / 100000000000000 : ℝ) = (100000000000000 / 29828120797947 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14914060398973 / 50000000000000 : ℝ) = (3750000000000 / 14914060398973 : ℝ) := by norm_num
  have hL1 : (8523383721567 / 100000000000000 : ℝ) ≤ Real.log (1 + (1423546864539 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1423546864539 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-235813290785287 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (29828120797947 / 100000000000000 : ℝ) ≤ (289879176061393 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (128091715073350361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 29828120797947 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 29828120797947 : ℝ) = (29828120797947 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 14914060398973 : ℝ) ≤ (246334043074307 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (128091715073350361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (29828120797947 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14914060398973 / 50000000000000 : ℝ)) ≤ (246334043074307 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_142 : ∀ t : ℝ, (1423546864539 / 16000000000000 : ℝ) < t → t ≤ (72858840643 / 800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-242875238468221463778742269 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (72858840643 / 800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_143
  have hV : (4507437470006386305024591833715237 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1423546864539 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_142 (Vfield_monotoneOn (show (1423546864539 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1423546864539 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_143 : (9118246687057754609603406156940537 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (72858840643 / 800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (72858840643 / 800000000000 : ℝ) := by norm_num
  have hs1 : (30178394722673 / 100000000000000 : ℝ) ≤ Real.sqrt (72858840643 / 800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (72858840643 / 800000000000 : ℝ) ≤ (15089197361337 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (15089197361337 / 50000000000000 : ℝ) = (50000000000000 / 15089197361337 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (30178394722673 / 100000000000000 : ℝ) = (7500000000000 / 30178394722673 : ℝ) := by norm_num
  have hL1 : (2179053013267 / 25000000000000 : ℝ) ≤ Real.log (1 + (72858840643 / 800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((72858840643 / 800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-116807843105649 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (15089197361337 / 50000000000000 : ℝ) ≤ (58618527731823 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (127770368813578161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 15089197361337 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 15089197361337 : ℝ) = (15089197361337 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 30178394722673 : ℝ) ≤ (243587276901669 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (127770368813578161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (15089197361337 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (30178394722673 / 100000000000000 : ℝ)) ≤ (243587276901669 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_143 : ∀ t : ℝ, (72858840643 / 800000000000 : ℝ) < t → t ≤ (762218354751 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-7547314892505408259154389 / 3125000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (762218354751 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_144
  have hV : (9118246687057754609603406156940537 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (72858840643 / 800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_143 (Vfield_monotoneOn (show (72858840643 / 800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (72858840643 / 800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_144 : (1864559455401154829226570893559459 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (762218354751 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (762218354751 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (6173404064011 / 20000000000000 : ℝ) ≤ Real.sqrt (762218354751 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (762218354751 / 8000000000000 : ℝ) ≤ (3858377540007 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3858377540007 / 12500000000000 : ℝ) = (12500000000000 / 3858377540007 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6173404064011 / 20000000000000 : ℝ) = (1500000000000 / 6173404064011 : ℝ) := by norm_num
  have hL1 : (4550378402657 / 50000000000000 : ℝ) ≤ Real.log (1 + (762218354751 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((762218354751 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-229360261205167 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3858377540007 / 12500000000000 : ℝ) ≤ (299392006632587 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (127140432016230961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 3858377540007 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 3858377540007 : ℝ) = (3858377540007 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 6173404064011 : ℝ) ≤ (59589667773757 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (127140432016230961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3858377540007 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6173404064011 / 20000000000000 : ℝ)) ≤ (59589667773757 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_144 : ∀ t : ℝ, (762218354751 / 8000000000000 : ℝ) < t → t ≤ (24870259471 / 250000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-240247173354219966584018127 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (24870259471 / 250000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_145
  have hV : (1864559455401154829226570893559459 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (762218354751 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_144 (Vfield_monotoneOn (show (762218354751 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (762218354751 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_145 : (2381127813770728583078545790880163 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (24870259471 / 250000000000 : ℝ) := by
  have hp : (0 : ℝ) < (24870259471 / 250000000000 : ℝ) := by norm_num
  have hs1 : (7885153687627 / 25000000000000 : ℝ) ≤ Real.sqrt (24870259471 / 250000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (24870259471 / 250000000000 : ℝ) ≤ (31540614750509 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (31540614750509 / 100000000000000 : ℝ) = (100000000000000 / 31540614750509 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7885153687627 / 25000000000000 : ℝ) = (1875000000000 / 7885153687627 : ℝ) := by norm_num
  have hL1 : (4741914236877 / 50000000000000 : ℝ) ≤ Real.log (1 + (24870259471 / 250000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((24870259471 / 250000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-225278555276571 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (31540614750509 / 100000000000000 : ℝ) ≤ (305530266924277 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (126526605987061961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 31540614750509 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 31540614750509 : ℝ) = (31540614750509 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 7885153687627 : ℝ) ≤ (116726507271969 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (126526605987061961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (31540614750509 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7885153687627 / 25000000000000 : ℝ)) ≤ (116726507271969 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_145 : ∀ t : ℝ, (24870259471 / 250000000000 : ℝ) < t → t ≤ (1614118950931 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-47594328496008753257235463 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1614118950931 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_146
  have hV : (2381127813770728583078545790880163 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (24870259471 / 250000000000 : ℝ) := by norm_num
    refine le_trans V_pt_145 (Vfield_monotoneOn (show (24870259471 / 250000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (24870259471 / 250000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_146 : (9591143529853484160946703334733631 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1614118950931 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1614118950931 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (31761995282599 / 100000000000000 : ℝ) ≤ Real.sqrt (1614118950931 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1614118950931 / 16000000000000 : ℝ) ≤ (158809976413 / 500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (158809976413 / 500000000000 : ℝ) = (500000000000 / 158809976413 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (31761995282599 / 100000000000000 : ℝ) = (7500000000000 / 31761995282599 : ℝ) := by norm_num
  have hL1 : (2402801783111 / 25000000000000 : ℝ) ≤ Real.log (1 + (1614118950931 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1614118950931 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-223954048834487 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (158809976413 / 500000000000 : ℝ) ≤ (3075424865341 / 10000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (126325384026079661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (500000000000 / 158809976413 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (500000000000 / 158809976413 : ℝ) = (158809976413 / 500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 31761995282599 : ℝ) ≤ (115941873352417 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (126325384026079661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (158809976413 / 500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (31761995282599 / 100000000000000 : ℝ)) ≤ (115941873352417 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_146 : ∀ t : ℝ, (1614118950931 / 16000000000000 : ℝ) < t → t ≤ (818270647859 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23680709076845664046206459 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (818270647859 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_147
  have hV : (9591143529853484160946703334733631 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1614118950931 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_146 (Vfield_monotoneOn (show (1614118950931 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1614118950931 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_147 : (603592216134282856639771504692307 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (818270647859 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (818270647859 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (1998865215003 / 6250000000000 : ℝ) ≤ Real.sqrt (818270647859 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (818270647859 / 8000000000000 : ℝ) ≤ (31981843440049 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (31981843440049 / 100000000000000 : ℝ) = (100000000000000 / 31981843440049 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1998865215003 / 6250000000000 : ℝ) = (156250000000 / 666288405001 : ℝ) := by norm_num
  have hL1 : (4869211872149 / 50000000000000 : ℝ) ≤ Real.log (1 + (818270647859 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((818270647859 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-111323428244519 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (31981843440049 / 100000000000000 : ℝ) ≤ (154769117786639 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (126125809122161861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 31981843440049 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 31981843440049 : ℝ) = (31981843440049 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (156250000000 / 666288405001 : ℝ) ≤ (230345713154469 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (126125809122161861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (31981843440049 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1998865215003 / 6250000000000 : ℝ)) ≤ (230345713154469 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_147 : ∀ t : ℝ, (818270647859 / 8000000000000 : ℝ) < t → t ≤ (331792728101 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-117916831989837785656836073 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (331792728101 / 3200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_148
  have hV : (603592216134282856639771504692307 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (818270647859 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_147 (Vfield_monotoneOn (show (818270647859 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (818270647859 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_148 : (4861755310871677491898206123971547 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (331792728101 / 3200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (331792728101 / 3200000000000 : ℝ) := by norm_num
  have hs1 : (16100095304963 / 50000000000000 : ℝ) ≤ Real.sqrt (331792728101 / 3200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (331792728101 / 3200000000000 : ℝ) ≤ (32200190609927 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (32200190609927 / 100000000000000 : ℝ) = (100000000000000 / 32200190609927 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16100095304963 / 50000000000000 : ℝ) = (3750000000000 / 16100095304963 : ℝ) := by norm_num
  have hL1 : (4932739360547 / 50000000000000 : ℝ) ≤ Real.log (1 + (331792728101 / 3200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((331792728101 / 3200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-110678265705659 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (32200190609927 / 100000000000000 : ℝ) ≤ (311517840461263 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125927848633363361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 32200190609927 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 32200190609927 : ℝ) = (32200190609927 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 16100095304963 : ℝ) ≤ (28604736382813 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125927848633363361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (32200190609927 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16100095304963 / 50000000000000 : ℝ)) ≤ (28604736382813 / 125000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_148 : ∀ t : ℝ, (331792728101 / 3200000000000 : ℝ) < t → t ≤ (3340349625797 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-117694164753853826139525513 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3340349625797 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_149
  have hV : (4861755310871677491898206123971547 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (331792728101 / 3200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_148 (Vfield_monotoneOn (show (331792728101 / 3200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (331792728101 / 3200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_149 : (9756418021222272742148958305458251 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3340349625797 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3340349625797 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (32308810842579 / 100000000000000 : ℝ) ≤ Real.sqrt (3340349625797 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3340349625797 / 32000000000000 : ℝ) ≤ (1615440542129 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1615440542129 / 5000000000000 : ℝ) = (5000000000000 / 1615440542129 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (32308810842579 / 100000000000000 : ℝ) = (2500000000000 / 10769603614193 : ℝ) := by norm_num
  have hL1 : (9928945724597 / 100000000000000 : ℝ) ≤ Real.log (1 + (3340349625797 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3340349625797 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-55179389789297 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1615440542129 / 5000000000000 : ℝ) ≤ (156250843941881 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125829463891113461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 1615440542129 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 1615440542129 : ℝ) = (1615440542129 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 10769603614193 : ℝ) ≤ (1824760019301 / 8000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125829463891113461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1615440542129 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (32308810842579 / 100000000000000 : ℝ)) ≤ (1824760019301 / 8000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_149 : ∀ t : ℝ, (3340349625797 / 32000000000000 : ℝ) < t → t ≤ (420346496323 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-58740825131334859605955899 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (420346496323 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_150
  have hV : (9756418021222272742148958305458251 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3340349625797 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_149 (Vfield_monotoneOn (show (3340349625797 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3340349625797 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_150 : (1957850509613004897475238756594743 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (420346496323 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (420346496323 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (6483413424447 / 20000000000000 : ℝ) ≤ Real.sqrt (420346496323 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (420346496323 / 4000000000000 : ℝ) ≤ (8104266780559 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8104266780559 / 25000000000000 : ℝ) = (25000000000000 / 8104266780559 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6483413424447 / 20000000000000 : ℝ) = (500000000000 / 2161137808149 : ℝ) := by norm_num
  have hL1 : (9992372473041 / 100000000000000 : ℝ) ≤ Real.log (1 + (420346496323 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((420346496323 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-110041321924713 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8104266780559 / 25000000000000 : ℝ) ≤ (313481616803279 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125731470999161761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 8104266780559 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 8104266780559 : ℝ) = (8104266780559 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (500000000000 / 2161137808149 : ℝ) ≤ (227359303896699 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125731470999161761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8104266780559 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6483413424447 / 20000000000000 : ℝ)) ≤ (227359303896699 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_150 : ∀ t : ℝ, (420346496323 / 4000000000000 : ℝ) < t → t ≤ (3385194315371 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-234555210700152713759761383 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3385194315371 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_151
  have hV : (1957850509613004897475238756594743 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (420346496323 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_150 (Vfield_monotoneOn (show (420346496323 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (420346496323 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_151 : (2455503658678598902844018076100209 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (3385194315371 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3385194315371 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (8131240770761 / 25000000000000 : ℝ) ≤ Real.sqrt (3385194315371 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3385194315371 / 32000000000000 : ℝ) ≤ (6504992616609 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6504992616609 / 20000000000000 : ℝ) = (20000000000000 / 6504992616609 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8131240770761 / 25000000000000 : ℝ) = (1875000000000 / 8131240770761 : ℝ) := by norm_num
  have hL1 : (502787950873 / 5000000000000 : ℝ) ≤ Real.log (1 + (3385194315371 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3385194315371 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-219451734296367 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6504992616609 / 20000000000000 : ℝ) ≤ (157228832531343 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125633866173221061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 6504992616609 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 6504992616609 : ℝ) = (6504992616609 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 8131240770761 : ℝ) ≤ (113315340122903 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125633866173221061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6504992616609 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8131240770761 / 25000000000000 : ℝ)) ≤ (113315340122903 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_151 : ∀ t : ℝ, (3385194315371 / 32000000000000 : ℝ) < t → t ≤ (1703808330079 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-58540398987529972449391193 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1703808330079 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_152
  have hV : (2455503658678598902844018076100209 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3385194315371 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_151 (Vfield_monotoneOn (show (3385194315371 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3385194315371 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_152 : (4927352355114364495844159804910491 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1703808330079 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1703808330079 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (16316251149539 / 50000000000000 : ℝ) ≤ Real.sqrt (1703808330079 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1703808330079 / 16000000000000 : ℝ) ≤ (32632502299079 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (32632502299079 / 100000000000000 : ℝ) = (100000000000000 / 32632502299079 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16316251149539 / 50000000000000 : ℝ) = (3750000000000 / 16316251149539 : ℝ) := by norm_num
  have hL1 : (1011910540879 / 10000000000000 : ℝ) ≤ Real.log (1 + (1703808330079 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1703808330079 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-109412390134599 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (32632502299079 / 100000000000000 : ℝ) ≤ (31542986988981 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125536645690508661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 32632502299079 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 32632502299079 : ℝ) = (32632502299079 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 16316251149539 : ℝ) ≤ (22590901876227 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125536645690508661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (32632502299079 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16316251149539 / 50000000000000 : ℝ)) ≤ (22590901876227 / 100000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_152 : ∀ t : ℝ, (1703808330079 / 16000000000000 : ℝ) < t → t ≤ (686007800989 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-233780585210702930188931863 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (686007800989 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_153
  have hV : (4927352355114364495844159804910491 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1703808330079 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_152 (Vfield_monotoneOn (show (1703808330079 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1703808330079 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_153 : (9887323200287285776082628310003683 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (686007800989 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (686007800989 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (32739688285707 / 100000000000000 : ℝ) ≤ Real.sqrt (686007800989 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (686007800989 / 6400000000000 : ℝ) ≤ (8184922071427 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8184922071427 / 25000000000000 : ℝ) = (25000000000000 / 8184922071427 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (32739688285707 / 100000000000000 : ℝ) = (2500000000000 / 10913229428569 : ℝ) := by norm_num
  have hL1 : (2545602924467 / 25000000000000 : ℝ) ≤ Real.log (1 + (686007800989 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((686007800989 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-218201732477961 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8184922071427 / 25000000000000 : ℝ) ≤ (316398267911413 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125439805888348361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 8184922071427 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 8184922071427 : ℝ) = (8184922071427 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 10913229428569 : ℝ) ≤ (140746380779 / 625000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125439805888348361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8184922071427 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (32739688285707 / 100000000000000 : ℝ)) ≤ (140746380779 / 625000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_153 : ∀ t : ℝ, (686007800989 / 6400000000000 : ℝ) < t → t ≤ (863115337433 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-233410715640457115818501957 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (863115337433 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_154
  have hV : (9887323200287285776082628310003683 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (686007800989 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_153 (Vfield_monotoneOn (show (686007800989 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (686007800989 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_154 : (4959935263601142499012720605818737 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (863115337433 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (863115337433 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (16423262250473 / 50000000000000 : ℝ) ≤ Real.sqrt (863115337433 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (863115337433 / 8000000000000 : ℝ) ≤ (32846524500947 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (32846524500947 / 100000000000000 : ℝ) = (100000000000000 / 32846524500947 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16423262250473 / 50000000000000 : ℝ) = (3750000000000 / 16423262250473 : ℝ) := by norm_num
  have hL1 : (5122838967719 / 50000000000000 : ℝ) ≤ Real.log (1 + (863115337433 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((863115337433 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-54395635637077 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (32846524500947 / 100000000000000 : ℝ) ≤ (317362895166881 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125343343162801561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 32846524500947 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 32846524500947 : ℝ) = (32846524500947 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 16423262250473 : ℝ) ≤ (224486143925693 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125343343162801561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (32846524500947 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16423262250473 / 50000000000000 : ℝ)) ≤ (224486143925693 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_154 : ∀ t : ℝ, (863115337433 / 8000000000000 : ℝ) < t → t ≤ (6927345044251 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-14576848980634138752668123 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (6927345044251 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_155
  have hV : (4959935263601142499012720605818737 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (863115337433 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_154 (Vfield_monotoneOn (show (863115337433 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (863115337433 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_155 : (248402940888360154042628456111291 / 125000000000000000000000000000000 : ℝ) ≤ Vfield (6927345044251 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (6927345044251 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (822495312739 / 2500000000000 : ℝ) ≤ Real.sqrt (6927345044251 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (6927345044251 / 64000000000000 : ℝ) ≤ (32899812509561 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (32899812509561 / 100000000000000 : ℝ) = (100000000000000 / 32899812509561 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (822495312739 / 2500000000000 : ℝ) = (187500000000 / 822495312739 : ℝ) := by norm_num
  have hL1 : (5138648025369 / 50000000000000 : ℝ) ≤ Real.log (1 + (6927345044251 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((6927345044251 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-21727437940939 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (32899812509561 / 100000000000000 : ℝ) ≤ (317843805862257 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125295252093263961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 32899812509561 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 32899812509561 : ℝ) = (32899812509561 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (187500000000 / 822495312739 : ℝ) ≤ (44826921461291 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125295252093263961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (32899812509561 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (822495312739 / 2500000000000 : ℝ)) ≤ (44826921461291 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_155 : ∀ t : ℝ, (6927345044251 / 64000000000000 : ℝ) < t → t ≤ (3474883694519 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-46610163203430804374506211 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3474883694519 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_156
  have hV : (248402940888360154042628456111291 / 125000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (6927345044251 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_155 (Vfield_monotoneOn (show (6927345044251 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (6927345044251 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_156 : (9952347109926522629931880353886519 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3474883694519 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3474883694519 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (32953014346751 / 100000000000000 : ℝ) ≤ Real.sqrt (3474883694519 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3474883694519 / 32000000000000 : ℝ) ≤ (32180678073 / 97656250000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (32180678073 / 97656250000 : ℝ) = (97656250000 / 32180678073 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (32953014346751 / 100000000000000 : ℝ) = (7500000000000 / 32953014346751 : ℝ) := by norm_num
  have hL1 : (2061780834429 / 20000000000000 : ℝ) ≤ Real.log (1 + (3474883694519 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3474883694519 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-216967162998953 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (32180678073 / 97656250000 : ℝ) ≤ (318323787121403 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125247253967349361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (97656250000 / 32180678073 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (97656250000 / 32180678073 : ℝ) = (32180678073 / 97656250000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 32953014346751 : ℝ) ≤ (27973089673319 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125247253967349361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (32180678073 / 97656250000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (32953014346751 / 100000000000000 : ℝ)) ≤ (27973089673319 / 125000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_156 : ∀ t : ℝ, (3474883694519 / 32000000000000 : ℝ) < t → t ≤ (278887589353 / 2560000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-232874299206989585613720537 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (278887589353 / 2560000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_157
  have hV : (9952347109926522629931880353886519 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3474883694519 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_156 (Vfield_monotoneOn (show (3474883694519 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3474883694519 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_157 : (2492139750556249000383991469671007 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (278887589353 / 2560000000000 : ℝ) := by
  have hp : (0 : ℝ) < (278887589353 / 2560000000000 : ℝ) := by norm_num
  have hs1 : (8251532607303 / 25000000000000 : ℝ) ≤ Real.sqrt (278887589353 / 2560000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (278887589353 / 2560000000000 : ℝ) ≤ (33006130429213 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (33006130429213 / 100000000000000 : ℝ) = (100000000000000 / 33006130429213 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8251532607303 / 25000000000000 : ℝ) = (625000000000 / 2750510869101 : ℝ) := by norm_num
  have hL1 : (1292562788247 / 12500000000000 : ℝ) ≤ Real.log (1 + (278887589353 / 2560000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((278887589353 / 2560000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-216660887517793 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (33006130429213 / 100000000000000 : ℝ) ≤ (15940142164493 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125199348350503661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 33006130429213 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 33006130429213 : ℝ) = (33006130429213 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (625000000000 / 2750510869101 : ℝ) ≤ (55859115336759 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125199348350503661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (33006130429213 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8251532607303 / 25000000000000 : ℝ)) ≤ (55859115336759 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_157 : ∀ t : ℝ, (278887589353 / 2560000000000 : ℝ) < t → t ≤ (1748653019653 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-116349964932861243308523341 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1748653019653 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_158
  have hV : (2492139750556249000383991469671007 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (278887589353 / 2560000000000 : ℝ) := by norm_num
    refine le_trans V_pt_157 (Vfield_monotoneOn (show (278887589353 / 2560000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (278887589353 / 2560000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_158 : (624047085254223283120361539801967 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (1748653019653 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1748653019653 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (2066197573143 / 6250000000000 : ℝ) ≤ Real.sqrt (1748653019653 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1748653019653 / 16000000000000 : ℝ) ≤ (33059161170289 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (33059161170289 / 100000000000000 : ℝ) = (100000000000000 / 33059161170289 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (2066197573143 / 6250000000000 : ℝ) = (156250000000 / 688732524381 : ℝ) := by norm_num
  have hL1 : (518604522927 / 5000000000000 : ℝ) ≤ Real.log (1 + (1748653019653 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1748653019653 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-54088886804957 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (33059161170289 / 100000000000000 : ℝ) ≤ (19955061167429 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125151534811603261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 33059161170289 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 33059161170289 : ℝ) = (33059161170289 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (156250000000 / 688732524381 : ℝ) ≤ (223089826508267 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125151534811603261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (33059161170289 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (2066197573143 / 6250000000000 : ℝ)) ≤ (223089826508267 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_158 : ∀ t : ℝ, (1748653019653 / 16000000000000 : ℝ) < t → t ≤ (7017034423399 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-232527613388328458353890169 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7017034423399 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_159
  have hV : (624047085254223283120361539801967 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1748653019653 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_158 (Vfield_monotoneOn (show (1748653019653 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1748653019653 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_159 : (10000930246885375615396894656678073 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (7017034423399 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7017034423399 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (33112106980017 / 100000000000000 : ℝ) ≤ Real.sqrt (7017034423399 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7017034423399 / 64000000000000 : ℝ) ≤ (16556053490009 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16556053490009 / 50000000000000 : ℝ) = (50000000000000 / 16556053490009 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33112106980017 / 100000000000000 : ℝ) = (2500000000000 / 11037368993339 : ℝ) := by norm_num
  have hL1 : (10403668636141 / 100000000000000 : ℝ) ≤ Real.log (1 + (7017034423399 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7017034423399 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-54012784102863 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16556053490009 / 50000000000000 : ℝ) ≤ (319758197565761 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125103812922913561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 16556053490009 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 16556053490009 : ℝ) = (16556053490009 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 11037368993339 : ℝ) ≤ (4454896006559 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125103812922913561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16556053490009 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33112106980017 / 100000000000000 : ℝ)) ≤ (4454896006559 / 20000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_159 : ∀ t : ℝ, (7017034423399 / 64000000000000 : ℝ) < t → t ≤ (3519728384093 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-232357262916179290372522937 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3519728384093 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_160
  have hV : (10000930246885375615396894656678073 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7017034423399 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_159 (Vfield_monotoneOn (show (7017034423399 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7017034423399 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
