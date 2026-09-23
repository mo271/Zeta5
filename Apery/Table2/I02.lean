import Apery.Table2.U02
import Apery.Table2.U03

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_80 : (413185401665723947356628255046369 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (1412931037823 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1412931037823 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (1313304737401 / 6250000000000 : ℝ) ≤ Real.sqrt (1412931037823 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1412931037823 / 32000000000000 : ℝ) ≤ (21012875798417 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (21012875798417 / 100000000000000 : ℝ) = (100000000000000 / 21012875798417 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1313304737401 / 6250000000000 : ℝ) = (468750000000 / 1313304737401 : ℝ) := by norm_num
  have hL1 : (4320707907811 / 100000000000000 : ℝ) ≤ Real.log (1 + (1412931037823 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1412931037823 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-60003203245337 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (21012875798417 / 100000000000000 : ℝ) ≤ (103557755307949 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (136368081617899861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 21012875798417 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 21012875798417 : ℝ) = (21012875798417 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (468750000000 / 1313304737401 : ℝ) ≤ (342829840865177 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (136368081617899861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (21012875798417 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1313304737401 / 6250000000000 : ℝ)) ≤ (342829840865177 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_80 : ∀ t : ℝ, (1412931037823 / 32000000000000 : ℝ) < t → t ≤ (71843627457 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-266210277587880610566474171 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (71843627457 / 1600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_81
  have hV : (413185401665723947356628255046369 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1412931037823 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_80 (Vfield_monotoneOn (show (1412931037823 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1412931037823 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_81 : (6654495912765821958094632619334241 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (71843627457 / 1600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (71843627457 / 1600000000000 : ℝ) := by norm_num
  have hs1 : (21190155063289 / 100000000000000 : ℝ) ≤ Real.sqrt (71843627457 / 1600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (71843627457 / 1600000000000 : ℝ) ≤ (2119015506329 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2119015506329 / 10000000000000 : ℝ) = (10000000000000 / 2119015506329 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21190155063289 / 100000000000000 : ℝ) = (7500000000000 / 21190155063289 : ℝ) := by norm_num
  have hL1 : (439233567949 / 10000000000000 : ℝ) ≤ Real.log (1 + (71843627457 / 1600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((71843627457 / 1600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-298524214334353 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2119015506329 / 10000000000000 : ℝ) ≤ (52203182532889 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (136198359666334061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 2119015506329 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 2119015506329 : ℝ) = (2119015506329 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 21190155063289 : ℝ) ≤ (170089348451157 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (136198359666334061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2119015506329 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21190155063289 / 100000000000000 : ℝ)) ≤ (170089348451157 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_81 : ∀ t : ℝ, (71843627457 / 1600000000000 : ℝ) < t → t ≤ (2897686609597 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-13296510485435766534295287 / 5000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2897686609597 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_82
  have hV : (6654495912765821958094632619334241 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (71843627457 / 1600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_81 (Vfield_monotoneOn (show (71843627457 / 1600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (71843627457 / 1600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_82 : (1669054455648495708386411440316441 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (2897686609597 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2897686609597 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (5319560207089 / 25000000000000 : ℝ) ≤ Real.sqrt (2897686609597 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2897686609597 / 64000000000000 : ℝ) ≤ (21278240828357 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (21278240828357 / 100000000000000 : ℝ) = (100000000000000 / 21278240828357 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5319560207089 / 25000000000000 : ℝ) = (1875000000000 / 5319560207089 : ℝ) := by norm_num
  have hL1 : (1107032583749 / 25000000000000 : ℝ) ≤ Real.log (1 + (2897686609597 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2897686609597 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-297786576754511 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (21278240828357 / 100000000000000 : ℝ) ≤ (20965558419241 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (136114074260248661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 21278240828357 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 21278240828357 : ℝ) = (21278240828357 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 5319560207089 : ℝ) ≤ (338876011495969 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (136114074260248661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (21278240828357 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5319560207089 / 25000000000000 : ℝ)) ≤ (338876011495969 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_82 : ∀ t : ℝ, (2897686609597 / 64000000000000 : ℝ) < t → t ≤ (1460814060457 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-33207751205360081762624789 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1460814060457 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_83
  have hV : (1669054455648495708386411440316441 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2897686609597 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_82 (Vfield_monotoneOn (show (2897686609597 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2897686609597 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_83 : (6697910975640240669688676374124833 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1460814060457 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1460814060457 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (21365963444057 / 100000000000000 : ℝ) ≤ Real.sqrt (1460814060457 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1460814060457 / 32000000000000 : ℝ) ≤ (10682981722029 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (10682981722029 / 50000000000000 : ℝ) = (50000000000000 / 10682981722029 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21365963444057 / 100000000000000 : ℝ) = (7500000000000 / 21365963444057 : ℝ) := by norm_num
  have hL1 : (4463912182513 / 100000000000000 : ℝ) ≤ Real.log (1 + (1460814060457 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1460814060457 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-148527170224571 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (10682981722029 / 50000000000000 : ℝ) ≤ (210494663089923 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (136030166370497361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 10682981722029 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 10682981722029 : ℝ) = (10682981722029 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 21365963444057 : ℝ) ≤ (337588196147837 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (136030166370497361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (10682981722029 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21365963444057 / 100000000000000 : ℝ)) ≤ (337588196147837 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_83 : ∀ t : ℝ, (1460814060457 / 32000000000000 : ℝ) < t → t ≤ (2945569632231 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-53080820996656203829591491 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2945569632231 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_84
  have hV : (6697910975640240669688676374124833 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1460814060457 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_83 (Vfield_monotoneOn (show (1460814060457 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1460814060457 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_84 : (1343915046793919569891247284624301 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (2945569632231 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2945569632231 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (4290665473029 / 20000000000000 : ℝ) ≤ Real.sqrt (2945569632231 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2945569632231 / 64000000000000 : ℝ) ≤ (10726663682573 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (10726663682573 / 50000000000000 : ℝ) = (50000000000000 / 10726663682573 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4290665473029 / 20000000000000 : ℝ) = (500000000000 / 1430221824343 : ℝ) := by norm_num
  have hL1 : (4499681231203 / 100000000000000 : ℝ) ≤ Real.log (1 + (2945569632231 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2945569632231 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-148163713446177 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (10726663682573 / 50000000000000 : ℝ) ≤ (211330012119883 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (135946631467501361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 10726663682573 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 10726663682573 : ℝ) = (10726663682573 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (500000000000 / 1430221824343 : ℝ) ≤ (67262993949407 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (135946631467501361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (10726663682573 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4290665473029 / 20000000000000 : ℝ)) ≤ (67262993949407 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_84 : ∀ t : ℝ, (2945569632231 / 64000000000000 : ℝ) < t → t ≤ (742377785887 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-26515526631480464005573781 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (742377785887 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_85
  have hV : (1343915046793919569891247284624301 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2945569632231 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_84 (Vfield_monotoneOn (show (2945569632231 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2945569632231 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_85 : (6741210469529576203721519886622839 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (742377785887 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (742377785887 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (21540336956031 / 100000000000000 : ℝ) ≤ Real.sqrt (742377785887 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (742377785887 / 16000000000000 : ℝ) ≤ (168283882469 / 781250000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (168283882469 / 781250000000 : ℝ) = (781250000000 / 168283882469 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21540336956031 / 100000000000000 : ℝ) = (2500000000000 / 7180112318677 : ℝ) := by norm_num
  have hL1 : (4535437490219 / 100000000000000 : ℝ) ≤ Real.log (1 + (742377785887 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((742377785887 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-59121151851673 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (168283882469 / 781250000000 : ℝ) ≤ (212161675665971 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (135863465112892561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (781250000000 / 168283882469 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (781250000000 / 168283882469 : ℝ) = (168283882469 / 781250000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 7180112318677 : ℝ) ≤ (67011211715197 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (135863465112892561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (168283882469 / 781250000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21540336956031 / 100000000000000 : ℝ)) ≤ (67011211715197 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_85 : ∀ t : ℝ, (742377785887 / 16000000000000 : ℝ) < t → t ≤ (598690530973 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-33114313667328848692670889 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (598690530973 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_86
  have hV : (6741210469529576203721519886622839 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (742377785887 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_85 (Vfield_monotoneOn (show (742377785887 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (742377785887 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_86 : (6762816563722232635275538640978077 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (598690530973 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (598690530973 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (21626996493333 / 100000000000000 : ℝ) ≤ Real.sqrt (598690530973 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (598690530973 / 12800000000000 : ℝ) ≤ (10813498246667 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (10813498246667 / 50000000000000 : ℝ) = (50000000000000 / 10813498246667 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21626996493333 / 100000000000000 : ℝ) = (2500000000000 / 7208998831111 : ℝ) := by norm_num
  have hL1 : (914236193741 / 20000000000000 : ℝ) ≤ Real.log (1 + (598690530973 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((598690530973 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-294889262372779 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (10813498246667 / 50000000000000 : ℝ) ≤ (13311856076589 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (135780662956947261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 10813498246667 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 10813498246667 : ℝ) = (10813498246667 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 7208998831111 : ℝ) ≤ (333811196061899 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (135780662956947261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (10813498246667 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21626996493333 / 100000000000000 : ℝ)) ≤ (333811196061899 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_86 : ∀ t : ℝ, (598690530973 / 12800000000000 : ℝ) < t → t ≤ (1508697083091 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-132340515161362792836399933 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1508697083091 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_87
  have hV : (6762816563722232635275538640978077 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (598690530973 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_86 (Vfield_monotoneOn (show (598690530973 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (598690530973 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_87 : (3392196703496203565935167541276347 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1508697083091 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1508697083091 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (10856655084163 / 50000000000000 : ℝ) ≤ Real.sqrt (1508697083091 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1508697083091 / 32000000000000 : ℝ) ≤ (21713310168327 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (21713310168327 / 100000000000000 : ℝ) = (100000000000000 / 21713310168327 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10856655084163 / 50000000000000 : ℝ) = (3750000000000 / 10856655084163 : ℝ) := by norm_num
  have hL1 : (287931979737 / 6250000000000 : ℝ) ≤ Real.log (1 + (1508697083091 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1508697083091 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-294177862665589 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (21713310168327 / 100000000000000 : ℝ) ≤ (106907059716851 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (135698220736119461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 21713310168327 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 21713310168327 : ℝ) = (21713310168327 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 10856655084163 : ℝ) ≤ (166290061269259 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (135698220736119461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (21713310168327 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10856655084163 / 50000000000000 : ℝ)) ≤ (166290061269259 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_87 : ∀ t : ℝ, (1508697083091 / 32000000000000 : ℝ) < t → t ≤ (3041335677499 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-66113540493832765277969343 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3041335677499 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_88
  have hV : (3392196703496203565935167541276347 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1508697083091 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_87 (Vfield_monotoneOn (show (1508697083091 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1508697083091 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_88 : (6805940898436533501607679716772083 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3041335677499 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3041335677499 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (21799282089307 / 100000000000000 : ℝ) ≤ Real.sqrt (3041335677499 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3041335677499 / 64000000000000 : ℝ) ≤ (5449820522327 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5449820522327 / 25000000000000 : ℝ) = (25000000000000 / 5449820522327 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21799282089307 / 100000000000000 : ℝ) = (7500000000000 / 21799282089307 : ℝ) := by norm_num
  have hL1 : (2321314810303 / 50000000000000 : ℝ) ≤ Real.log (1 + (3041335677499 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3041335677499 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-5869429762517 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5449820522327 / 25000000000000 : ℝ) ≤ (214634984088299 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (135616134270659761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 5449820522327 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 5449820522327 : ℝ) = (5449820522327 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 21799282089307 : ℝ) ≤ (33136258501747 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (135616134270659761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5449820522327 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21799282089307 / 100000000000000 : ℝ)) ≤ (33136258501747 / 100000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_88 : ∀ t : ℝ, (3041335677499 / 64000000000000 : ℝ) < t → t ≤ (191579824301 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-264233342347488651003523429 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (191579824301 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_89
  have hV : (6805940898436533501607679716772083 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3041335677499 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_88 (Vfield_monotoneOn (show (3041335677499 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3041335677499 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_89 : (6827458945429993242380843184889489 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (191579824301 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (191579824301 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (21884916283881 / 100000000000000 : ℝ) ≤ Real.sqrt (191579824301 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (191579824301 / 4000000000000 : ℝ) ≤ (10942458141941 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (10942458141941 / 50000000000000 : ℝ) = (50000000000000 / 10942458141941 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21884916283881 / 100000000000000 : ℝ) = (2500000000000 / 7294972094627 : ℝ) := by norm_num
  have hL1 : (2339167406129 / 50000000000000 : ℝ) ≤ Real.log (1 + (191579824301 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((191579824301 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-73192517064483 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (10942458141941 / 50000000000000 : ℝ) ≤ (107726166085881 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (135534399462313461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 10942458141941 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 10942458141941 : ℝ) = (10942458141941 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 7294972094627 : ℝ) ≤ (8253958424219 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (135534399462313461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (10942458141941 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21884916283881 / 100000000000000 : ℝ)) ≤ (8253958424219 / 25000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_89 : ∀ t : ℝ, (191579824301 / 4000000000000 : ℝ) < t → t ≤ (3089218700133 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2640180923447080926450697 / 1000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3089218700133 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_90
  have hV : (6827458945429993242380843184889489 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (191579824301 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_89 (Vfield_monotoneOn (show (191579824301 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (191579824301 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_90 : (1712236865816995701434037427662241 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (3089218700133 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3089218700133 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (5492554175289 / 25000000000000 : ℝ) ≤ Real.sqrt (3089218700133 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3089218700133 / 64000000000000 : ℝ) ≤ (21970216701157 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (21970216701157 / 100000000000000 : ℝ) = (100000000000000 / 21970216701157 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5492554175289 / 25000000000000 : ℝ) = (625000000000 / 1830851391763 : ℝ) := by norm_num
  have hL1 : (2357013629927 / 50000000000000 : ℝ) ≤ Real.log (1 + (3089218700133 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3089218700133 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-146036767019651 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (21970216701157 / 100000000000000 : ℝ) ≤ (108133101936897 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (135453012292110261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 21970216701157 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 21970216701157 : ℝ) = (21970216701157 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (625000000000 / 1830851391763 : ℝ) ≤ (328967138110173 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (135453012292110261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (21970216701157 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5492554175289 / 25000000000000 : ℝ)) ≤ (328967138110173 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_90 : ∀ t : ℝ, (3089218700133 / 64000000000000 : ℝ) < t → t ≤ (62263204229 / 1280000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-263807999098039104179613067 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (62263204229 / 1280000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_91
  have hV : (1712236865816995701434037427662241 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3089218700133 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_90 (Vfield_monotoneOn (show (3089218700133 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3089218700133 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_91 : (3435203187413316042805943604979553 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (62263204229 / 1280000000000 : ℝ) := by
  have hp : (0 : ℝ) < (62263204229 / 1280000000000 : ℝ) := by norm_num
  have hs1 : (11027593606937 / 50000000000000 : ℝ) ≤ Real.sqrt (62263204229 / 1280000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (62263204229 / 1280000000000 : ℝ) ≤ (176441497711 / 800000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (176441497711 / 800000000000 : ℝ) = (800000000000 / 176441497711 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (11027593606937 / 50000000000000 : ℝ) = (3750000000000 / 11027593606937 : ℝ) := by norm_num
  have hL1 : (4749706972487 / 100000000000000 : ℝ) ≤ Real.log (1 + (62263204229 / 1280000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((62263204229 / 1280000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-291381817879763 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (176441497711 / 800000000000 : ℝ) ≤ (43415327722543 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (135371968818218161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (800000000000 / 176441497711 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (800000000000 / 176441497711 : ℝ) = (176441497711 / 800000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 11027593606937 : ℝ) ≤ (327788754204851 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (135371968818218161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (176441497711 / 800000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (11027593606937 / 50000000000000 : ℝ)) ≤ (327788754204851 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_91 : ∀ t : ℝ, (62263204229 / 1280000000000 : ℝ) < t → t ≤ (3137101722767 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-5272054068532595295287093 / 2000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3137101722767 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_92
  have hV : (3435203187413316042805943604979553 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (62263204229 / 1280000000000 : ℝ) := by norm_num
    refine le_trans V_pt_91 (Vfield_monotoneOn (show (62263204229 / 1280000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (62263204229 / 1280000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_92 : (344591780511829398198365703461687 / 250000000000000000000000000000000 : ℝ) ≤ Vfield (3137101722767 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3137101722767 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (1106991581023 / 5000000000000 : ℝ) ≤ Real.sqrt (3137101722767 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3137101722767 / 64000000000000 : ℝ) ≤ (22139831620461 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (22139831620461 / 100000000000000 : ℝ) = (100000000000000 / 22139831620461 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1106991581023 / 5000000000000 : ℝ) = (375000000000 / 1106991581023 : ℝ) := by norm_num
  have hL1 : (4785373959241 / 100000000000000 : ℝ) ≤ Real.log (1 + (3137101722767 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3137101722767 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-145347426791049 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (22139831620461 / 100000000000000 : ℝ) ≤ (54470918764023 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (135291265173880461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 22139831620461 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 22139831620461 : ℝ) = (22139831620461 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (375000000000 / 1106991581023 : ℝ) ≤ (81655739216737 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (135291265173880461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (22139831620461 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1106991581023 / 5000000000000 : ℝ)) ≤ (81655739216737 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_92 : ∀ t : ℝ, (3137101722767 / 64000000000000 : ℝ) < t → t ≤ (790260808521 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-65850472555529090042660049 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (790260808521 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_93
  have hV : (344591780511829398198365703461687 / 250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3137101722767 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_92 (Vfield_monotoneOn (show (3137101722767 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3137101722767 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_93 : (6913235106571597710368962714700307 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (790260808521 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (790260808521 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (22224153647003 / 100000000000000 : ℝ) ≤ Real.sqrt (790260808521 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (790260808521 / 16000000000000 : ℝ) ≤ (5556038411751 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5556038411751 / 25000000000000 : ℝ) = (25000000000000 / 5556038411751 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (22224153647003 / 100000000000000 : ℝ) = (7500000000000 / 22224153647003 : ℝ) := by norm_num
  have hL1 : (4821028229191 / 100000000000000 : ℝ) ≤ Real.log (1 + (790260808521 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((790260808521 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-290012576304051 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5556038411751 / 25000000000000 : ℝ) ≤ (2186873511407 / 10000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (135210897565419661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 5556038411751 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 5556038411751 : ℝ) = (5556038411751 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 22224153647003 : ℝ) ≤ (325469523374851 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (135210897565419661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5556038411751 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (22224153647003 / 100000000000000 : ℝ)) ≤ (325469523374851 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_93 : ∀ t : ℝ, (790260808521 / 16000000000000 : ℝ) < t → t ≤ (3184984745401 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-263205280961222679700824321 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3184984745401 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_94
  have hV : (6913235106571597710368962714700307 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (790260808521 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_93 (Vfield_monotoneOn (show (790260808521 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (790260808521 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_94 : (1733651201888012783500557170283317 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (3184984745401 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3184984745401 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (5577039237293 / 25000000000000 : ℝ) ≤ Real.sqrt (3184984745401 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3184984745401 / 64000000000000 : ℝ) ≤ (22308156949173 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (22308156949173 / 100000000000000 : ℝ) = (100000000000000 / 22308156949173 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5577039237293 / 25000000000000 : ℝ) = (1875000000000 / 5577039237293 : ℝ) := by norm_num
  have hL1 : (4856669791403 / 100000000000000 : ℝ) ≤ Real.log (1 + (3184984745401 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3184984745401 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-11302145411 / 3906250000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (22308156949173 / 100000000000000 : ℝ) ≤ (6858990752869 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (135130862270308861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 22308156949173 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 22308156949173 : ℝ) = (22308156949173 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 5577039237293 : ℝ) ≤ (40541029561451 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (135130862270308861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (22308156949173 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5577039237293 / 25000000000000 : ℝ)) ≤ (40541029561451 / 125000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_94 : ∀ t : ℝ, (3184984745401 / 64000000000000 : ℝ) < t → t ≤ (1604463128359 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-32876578474501924940497333 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1604463128359 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_95
  have hV : (1733651201888012783500557170283317 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3184984745401 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_94 (Vfield_monotoneOn (show (3184984745401 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3184984745401 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_95 : (6955944663259400931258342563569447 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1604463128359 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1604463128359 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (22391845114063 / 100000000000000 : ℝ) ≤ Real.sqrt (1604463128359 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1604463128359 / 32000000000000 : ℝ) ≤ (1399490319629 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1399490319629 / 6250000000000 : ℝ) = (6250000000000 / 1399490319629 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (22391845114063 / 100000000000000 : ℝ) = (7500000000000 / 22391845114063 : ℝ) := by norm_num
  have hL1 : (489229865493 / 10000000000000 : ℝ) ≤ Real.log (1 + (1604463128359 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1604463128359 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-144330914996731 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1399490319629 / 6250000000000 : ℝ) ≤ (110142385220897 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (135051155635310261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 1399490319629 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 1399490319629 : ℝ) = (1399490319629 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 22391845114063 : ℝ) ≤ (64639776858467 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (135051155635310261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1399490319629 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (22391845114063 / 100000000000000 : ℝ)) ≤ (64639776858467 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_95 : ∀ t : ℝ, (1604463128359 / 32000000000000 : ℝ) < t → t ≤ (646573553607 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-262823708832220094544305989 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (646573553607 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_96
  have hV : (6955944663259400931258342563569447 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1604463128359 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_95 (Vfield_monotoneOn (show (1604463128359 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1604463128359 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_96 : (6977254629865111258271318022463003 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (646573553607 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (646573553607 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (22475221661987 / 100000000000000 : ℝ) ≤ Real.sqrt (646573553607 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (646573553607 / 12800000000000 : ℝ) ≤ (5618805415497 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5618805415497 / 25000000000000 : ℝ) = (25000000000000 / 5618805415497 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (22475221661987 / 100000000000000 : ℝ) = (7500000000000 / 22475221661987 : ℝ) := by norm_num
  have hL1 : (246395741441 / 5000000000000 : ℝ) ≤ Real.log (1 + (646573553607 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((646573553607 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-287993237726791 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5618805415497 / 25000000000000 : ℝ) ≤ (4421571720963 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (134971774074674661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 5618805415497 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 5618805415497 : ℝ) = (5618805415497 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 22475221661987 : ℝ) ≤ (322081259998179 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (134971774074674661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5618805415497 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (22475221661987 / 100000000000000 : ℝ)) ≤ (322081259998179 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_96 : ∀ t : ℝ, (646573553607 / 12800000000000 : ℝ) < t → t ≤ (407101159919 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-26263832431500417346508399 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (407101159919 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_97
  have hV : (6977254629865111258271318022463003 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (646573553607 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_96 (Vfield_monotoneOn (show (646573553607 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (646573553607 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_97 : (34992673346855322818676995820329 / 25000000000000000000000000000000 : ℝ) ≤ Vfield (407101159919 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (407101159919 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (112791450241 / 500000000000 : ℝ) ≤ Real.sqrt (407101159919 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (407101159919 / 8000000000000 : ℝ) ≤ (22558290048201 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (22558290048201 / 100000000000000 : ℝ) = (100000000000000 / 22558290048201 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (112791450241 / 500000000000 : ℝ) = (37500000000 / 112791450241 : ℝ) := by norm_num
  have hL1 : (4963518322107 / 100000000000000 : ℝ) ≤ Real.log (1 + (407101159919 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((407101159919 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-287329085944011 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (22558290048201 / 100000000000000 : ℝ) ≤ (55467296527727 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (134892714068398861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 22558290048201 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 22558290048201 : ℝ) = (22558290048201 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (37500000000 / 112791450241 : ℝ) ≤ (32097516181657 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (134892714068398861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (22558290048201 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (112791450241 / 500000000000 : ℝ)) ≤ (32097516181657 / 100000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_97 : ∀ t : ℝ, (407101159919 / 8000000000000 : ℝ) < t → t ≤ (1652346150993 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-262277452174722377792904327 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1652346150993 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_98
  have hV : (34992673346855322818676995820329 / 25000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (407101159919 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_97 (Vfield_monotoneOn (show (407101159919 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (407101159919 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_98 : (17602512106894479142009056959707 / 12500000000000000000000000000000 : ℝ) ≤ Vfield (1652346150993 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1652346150993 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (56808789603 / 250000000000 : ℝ) ≤ Real.sqrt (1652346150993 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1652346150993 / 32000000000000 : ℝ) ≤ (22723515841201 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (22723515841201 / 100000000000000 : ℝ) = (100000000000000 / 22723515841201 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (56808789603 / 250000000000 : ℝ) = (6250000000 / 18936263201 : ℝ) := by norm_num
  have hL1 : (5034687302971 / 100000000000000 : ℝ) ≤ Real.log (1 + (1652346150993 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1652346150993 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-71503467651193 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (22723515841201 / 100000000000000 : ℝ) ≤ (55860219304701 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (134735544957609261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 22723515841201 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 22723515841201 : ℝ) = (22723515841201 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (6250000000 / 18936263201 : ℝ) ≤ (7969919015897 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (134735544957609261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (22723515841201 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (56808789603 / 250000000000 : ℝ)) ≤ (7969919015897 / 25000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_98 : ∀ t : ℝ, (1652346150993 / 32000000000000 : ℝ) < t → t ≤ (167628766231 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-261928750710786828180321017 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (167628766231 / 3200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_99
  have hV : (17602512106894479142009056959707 / 12500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1652346150993 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_98 (Vfield_monotoneOn (show (1652346150993 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1652346150993 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_99 : (7083354986843348473028220622944359 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (167628766231 / 3200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (167628766231 / 3200000000000 : ℝ) := by norm_num
  have hs1 : (22887548896111 / 100000000000000 : ℝ) ≤ Real.sqrt (167628766231 / 3200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (167628766231 / 3200000000000 : ℝ) ≤ (1430471806007 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1430471806007 / 6250000000000 : ℝ) = (6250000000000 / 1430471806007 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (22887548896111 / 100000000000000 : ℝ) = (7500000000000 / 22887548896111 : ℝ) := by norm_num
  have hL1 : (319112854351 / 6250000000000 : ℝ) ≤ Real.log (1 + (167628766231 / 3200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((167628766231 / 3200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-142357864433851 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1430471806007 / 6250000000000 : ℝ) ≤ (225000112842239 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (134579621395265761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 1430471806007 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 1430471806007 : ℝ) = (1430471806007 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 22887548896111 : ℝ) ≤ (316662160437361 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (134579621395265761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1430471806007 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (22887548896111 / 100000000000000 : ℝ)) ≤ (316662160437361 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_99 : ∀ t : ℝ, (167628766231 / 3200000000000 : ℝ) < t → t ≤ (1700229173627 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-261591162414477307818339749 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1700229173627 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_100
  have hV : (7083354986843348473028220622944359 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (167628766231 / 3200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_99 (Vfield_monotoneOn (show (167628766231 / 3200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (167628766231 / 3200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_100 : (445349061467702592766583614374089 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (1700229173627 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1700229173627 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (1440650917281 / 6250000000000 : ℝ) ≤ Real.sqrt (1700229173627 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1700229173627 / 32000000000000 : ℝ) ≤ (23050414676497 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (23050414676497 / 100000000000000 : ℝ) = (100000000000000 / 23050414676497 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1440650917281 / 6250000000000 : ℝ) = (156250000000 / 480216972427 : ℝ) := by norm_num
  have hL1 : (2588436746991 / 50000000000000 : ℝ) ≤ Real.log (1 + (1700229173627 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1700229173627 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-141717111561101 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (23050414676497 / 100000000000000 : ℝ) ≤ (113273576280113 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (134424917423467061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 23050414676497 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 23050414676497 : ℝ) = (23050414676497 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (156250000000 / 480216972427 : ℝ) ≤ (314569911429407 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (134424917423467061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (23050414676497 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1440650917281 / 6250000000000 : ℝ)) ≤ (314569911429407 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_100 : ∀ t : ℝ, (1700229173627 / 32000000000000 : ℝ) < t → t ≤ (107760667809 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-261263787803947779955024661 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (107760667809 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_101
  have hV : (445349061467702592766583614374089 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1700229173627 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_100 (Vfield_monotoneOn (show (1700229173627 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1700229173627 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_101 : (1433538957284700489328142317392573 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (107760667809 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (107760667809 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (4642427550517 / 20000000000000 : ℝ) ≤ Real.sqrt (107760667809 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (107760667809 / 2000000000000 : ℝ) ≤ (11606068876293 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (11606068876293 / 50000000000000 : ℝ) = (50000000000000 / 11606068876293 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4642427550517 / 20000000000000 : ℝ) = (1500000000000 / 4642427550517 : ℝ) := by norm_num
  have hL1 : (5247890847859 / 100000000000000 : ℝ) ≤ Real.log (1 + (107760667809 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((107760667809 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-56433786473899 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (11606068876293 / 50000000000000 : ℝ) ≤ (28510280864887 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (134271407987580061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 11606068876293 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 11606068876293 : ℝ) = (11606068876293 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 4642427550517 : ℝ) ≤ (62503726037371 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (134271407987580061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (11606068876293 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4642427550517 / 20000000000000 : ℝ)) ≤ (62503726037371 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_101 : ∀ t : ℝ, (107760667809 / 2000000000000 : ℝ) < t → t ≤ (886026853789 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-130318341808415576749657447 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (886026853789 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_102
  have hV : (1433538957284700489328142317392573 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (107760667809 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_101 (Vfield_monotoneOn (show (107760667809 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (107760667809 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_102 : (7251553950102026364406367161908137 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (886026853789 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (886026853789 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (23532249863073 / 100000000000000 : ℝ) ≤ Real.sqrt (886026853789 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (886026853789 / 16000000000000 : ℝ) ≤ (11766124931537 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (11766124931537 / 50000000000000 : ℝ) = (50000000000000 / 11766124931537 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (23532249863073 / 100000000000000 : ℝ) = (2500000000000 / 7844083287691 : ℝ) := by norm_num
  have hL1 : (2694887215263 / 50000000000000 : ℝ) ≤ Real.log (1 + (886026853789 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((886026853789 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-17480336873497 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (11766124931537 / 50000000000000 : ℝ) ≤ (231117559170923 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (133967876762397361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 11766124931537 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 11766124931537 : ℝ) = (11766124931537 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 7844083287691 : ℝ) ≤ (308533746245841 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (133967876762397361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (11766124931537 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (23532249863073 / 100000000000000 : ℝ)) ≤ (308533746245841 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_102 : ∀ t : ℝ, (886026853789 / 16000000000000 : ℝ) < t → t ≤ (454984182553 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-260042348653150003796860641 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (454984182553 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_103
  have hV : (7251553950102026364406367161908137 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (886026853789 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_102 (Vfield_monotoneOn (show (886026853789 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (886026853789 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_103 : (3667466664725696895539884731892453 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (454984182553 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (454984182553 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (11924032751037 / 50000000000000 : ℝ) ≤ Real.sqrt (454984182553 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (454984182553 / 8000000000000 : ℝ) ≤ (953922620083 / 4000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (953922620083 / 4000000000000 : ℝ) = (4000000000000 / 953922620083 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (11924032751037 / 50000000000000 : ℝ) = (1250000000000 / 3974677583679 : ℝ) := by norm_num
  have hL1 : (553145698887 / 10000000000000 : ℝ) ≤ Real.log (1 + (454984182553 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((454984182553 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-277262035633443 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (953922620083 / 4000000000000 : ℝ) ≤ (46821577846447 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (133668843756266161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (4000000000000 / 953922620083 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (4000000000000 / 953922620083 : ℝ) = (953922620083 / 4000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 3974677583679 : ℝ) ≤ (152348814247139 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (133668843756266161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (953922620083 / 4000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (11924032751037 / 50000000000000 : ℝ)) ≤ (152348814247139 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_103 : ∀ t : ℝ, (454984182553 / 8000000000000 : ℝ) < t → t ≤ (47892569387 / 800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-129468440703463830543582073 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (47892569387 / 800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_104
  have hV : (3667466664725696895539884731892453 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (454984182553 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_103 (Vfield_monotoneOn (show (454984182553 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (454984182553 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_104 : (1500052015517152306731862836729827 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (47892569387 / 800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (47892569387 / 800000000000 : ℝ) := by norm_num
  have hs1 : (4893494119083 / 20000000000000 : ℝ) ≤ Real.sqrt (47892569387 / 800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (47892569387 / 800000000000 : ℝ) ≤ (3058433824427 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3058433824427 / 12500000000000 : ℝ) = (12500000000000 / 3058433824427 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4893494119083 / 20000000000000 : ℝ) = (500000000000 / 1631164706361 : ℝ) := by norm_num
  have hL1 : (2907110652743 / 50000000000000 : ℝ) ≤ Real.log (1 + (47892569387 / 800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((47892569387 / 800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-272584695094811 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3058433824427 / 12500000000000 : ℝ) ≤ (119980187889533 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (133083595101583061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 3058433824427 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 3058433824427 : ℝ) = (3058433824427 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (500000000000 / 1631164706361 : ℝ) ≤ (297436287064081 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (133083595101583061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3058433824427 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4893494119083 / 20000000000000 : ℝ)) ≤ (297436287064081 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_104 : ∀ t : ℝ, (47892569387 / 800000000000 : ℝ) < t → t ≤ (502867205187 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-257923836930178654863566571 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (502867205187 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_105
  have hV : (1500052015517152306731862836729827 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (47892569387 / 800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_104 (Vfield_monotoneOn (show (47892569387 / 800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (47892569387 / 800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_105 : (7663695873249381456692801285230591 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (502867205187 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (502867205187 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (25071577662439 / 100000000000000 : ℝ) ≤ Real.sqrt (502867205187 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (502867205187 / 8000000000000 : ℝ) ≤ (626789441561 / 2500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (626789441561 / 2500000000000 : ℝ) = (2500000000000 / 626789441561 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (25071577662439 / 100000000000000 : ℝ) = (7500000000000 / 25071577662439 : ℝ) := by norm_num
  have hL1 : (6096188319471 / 100000000000000 : ℝ) ≤ Real.log (1 + (502867205187 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((502867205187 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-268116388834103 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (626789441561 / 2500000000000 : ℝ) ≤ (122826110851331 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (132514410509223461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (2500000000000 / 626789441561 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (2500000000000 / 626789441561 : ℝ) = (626789441561 / 2500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 25071577662439 : ℝ) ≤ (290670848125297 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (132514410509223461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (626789441561 / 2500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (25071577662439 / 100000000000000 : ℝ)) ≤ (290670848125297 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_105 : ∀ t : ℝ, (502867205187 / 8000000000000 : ℝ) < t → t ≤ (65851089563 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-64246736312849356598865957 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (65851089563 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_106
  have hV : (7663695873249381456692801285230591 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (502867205187 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_105 (Vfield_monotoneOn (show (502867205187 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (502867205187 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_106 : (7825269264226751834501611908617201 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (65851089563 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (65851089563 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (25661467137129 / 100000000000000 : ℝ) ≤ Real.sqrt (65851089563 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (65851089563 / 1000000000000 : ℝ) ≤ (2566146713713 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2566146713713 / 10000000000000 : ℝ) = (10000000000000 / 2566146713713 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (25661467137129 / 100000000000000 : ℝ) = (2500000000000 / 8553822379043 : ℝ) := by norm_num
  have hL1 : (6377362514451 / 100000000000000 : ℝ) ≤ Real.log (1 + (65851089563 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((65851089563 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-10553569183507 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2566146713713 / 10000000000000 : ℝ) ≤ (251194481745859 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (131960184504903761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 2566146713713 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 2566146713713 : ℝ) = (2566146713713 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 8553822379043 : ℝ) ≤ (142173643259861 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (131960184504903761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2566146713713 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (25661467137129 / 100000000000000 : ℝ)) ≤ (142173643259861 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_106 : ∀ t : ℝ, (65851089563 / 1000000000000 : ℝ) < t → t ≤ (2140864814337 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-63731587659252223590190073 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2140864814337 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_107
  have hV : (7825269264226751834501611908617201 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (65851089563 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_106 (Vfield_monotoneOn (show (65851089563 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (65851089563 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_107 : (1970393238929709494549496491168951 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (2140864814337 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2140864814337 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (6466356462879 / 25000000000000 : ℝ) ≤ Real.sqrt (2140864814337 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2140864814337 / 32000000000000 : ℝ) ≤ (25865425851517 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (25865425851517 / 100000000000000 : ℝ) = (100000000000000 / 25865425851517 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6466356462879 / 25000000000000 : ℝ) = (625000000000 / 2155452154293 : ℝ) := by norm_num
  have hL1 : (1618978641393 / 25000000000000 : ℝ) ≤ Real.log (1 + (2140864814337 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2140864814337 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-262379602074083 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (25865425851517 / 100000000000000 : ℝ) ≤ (126553558142219 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (131768921051045861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 25865425851517 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 25865425851517 : ℝ) = (25865425851517 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (625000000000 / 2155452154293 : ℝ) ≤ (141111352179143 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (131768921051045861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (25865425851517 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6466356462879 / 25000000000000 : ℝ)) ≤ (141111352179143 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_107 : ∀ t : ℝ, (2140864814337 / 32000000000000 : ℝ) < t → t ≤ (1087247381329 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-253903311022885761071796077 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1087247381329 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_108
  have hV : (1970393238929709494549496491168951 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2140864814337 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_107 (Vfield_monotoneOn (show (2140864814337 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2140864814337 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_108 : (7937652697399954871219536978200881 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1087247381329 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1087247381329 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (26067788807849 / 100000000000000 : ℝ) ≤ Real.sqrt (1087247381329 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1087247381329 / 16000000000000 : ℝ) ≤ (521355776157 / 2000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (521355776157 / 2000000000000 : ℝ) = (2000000000000 / 521355776157 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (26067788807849 / 100000000000000 : ℝ) = (7500000000000 / 26067788807849 : ℝ) := by norm_num
  have hL1 : (6574369587241 / 100000000000000 : ℝ) ≤ Real.log (1 + (1087247381329 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1087247381329 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-260940973545763 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (521355776157 / 2000000000000 : ℝ) ≤ (255002918138179 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (131579340865671761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (2000000000000 / 521355776157 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (2000000000000 / 521355776157 : ℝ) = (521355776157 / 2000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 26067788807849 : ℝ) ≤ (140072535802999 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (131579340865671761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (521355776157 / 2000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (26067788807849 / 100000000000000 : ℝ)) ≤ (140072535802999 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_108 : ∀ t : ℝ, (1087247381329 / 16000000000000 : ℝ) < t → t ≤ (2208124710979 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-12652928877912746076026473 / 5000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2208124710979 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_109
  have hV : (7937652697399954871219536978200881 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1087247381329 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_108 (Vfield_monotoneOn (show (1087247381329 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1087247381329 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_109 : (7993510114286172491320333582117591 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2208124710979 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2208124710979 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (26268592885439 / 100000000000000 : ℝ) ≤ Real.sqrt (2208124710979 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2208124710979 / 32000000000000 : ℝ) ≤ (82089352767 / 312500000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (82089352767 / 312500000000 : ℝ) = (312500000000 / 82089352767 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (26268592885439 / 100000000000000 : ℝ) = (7500000000000 / 26268592885439 : ℝ) := by norm_num
  have hL1 : (1668181942583 / 25000000000000 : ℝ) ≤ Real.log (1 + (2208124710979 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2208124710979 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-51904549671303 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (82089352767 / 312500000000 : ℝ) ≤ (64220566394551 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (131391406121669261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (312500000000 / 82089352767 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (312500000000 / 82089352767 : ℝ) = (82089352767 / 312500000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 26268592885439 : ℝ) ≤ (278112683228959 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (131391406121669261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (82089352767 / 312500000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (26268592885439 / 100000000000000 : ℝ)) ≤ (278112683228959 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_109 : ∀ t : ℝ, (2208124710979 / 32000000000000 : ℝ) < t → t ≤ (4449879370279 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-63168689559923259817878423 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4449879370279 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_110
  have hV : (7993510114286172491320333582117591 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2208124710979 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_109 (Vfield_monotoneOn (show (2208124710979 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2208124710979 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_110 : (4010677984630017727675784260894433 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (4449879370279 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4449879370279 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (13184210742457 / 50000000000000 : ℝ) ≤ Real.sqrt (4449879370279 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4449879370279 / 64000000000000 : ℝ) ≤ (5273684296983 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5273684296983 / 20000000000000 : ℝ) = (20000000000000 / 5273684296983 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13184210742457 / 50000000000000 : ℝ) = (3750000000000 / 13184210742457 : ℝ) := by norm_num
  have hL1 : (1344374121381 / 20000000000000 : ℝ) ≤ Real.log (1 + (4449879370279 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4449879370279 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-258821107746077 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5273684296983 / 20000000000000 : ℝ) ≤ (16113492700037 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (131298044359430461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 5273684296983 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 5273684296983 : ℝ) = (5273684296983 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 13184210742457 : ℝ) ≤ (277112946387479 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (131298044359430461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5273684296983 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13184210742457 / 50000000000000 : ℝ)) ≤ (277112946387479 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_110 : ∀ t : ℝ, (4449879370279 / 64000000000000 : ℝ) < t → t ≤ (22417546593 / 320000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-50461965646579349755061517 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (22417546593 / 320000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_111
  have hV : (4010677984630017727675784260894433 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4449879370279 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_110 (Vfield_monotoneOn (show (4449879370279 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4449879370279 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_111 : (503071679325790659525169913793203 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (22417546593 / 320000000000 : ℝ) := by
  have hp : (0 : ℝ) < (22417546593 / 320000000000 : ℝ) := by norm_num
  have hs1 : (1654242097787 / 6250000000000 : ℝ) ≤ Real.sqrt (22417546593 / 320000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (22417546593 / 320000000000 : ℝ) ≤ (26467873564593 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (26467873564593 / 100000000000000 : ℝ) = (100000000000000 / 26467873564593 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1654242097787 / 6250000000000 : ℝ) = (468750000000 / 1654242097787 : ℝ) := by norm_num
  have hL1 : (1692747326289 / 25000000000000 : ℝ) ≤ Real.log (1 + (22417546593 / 320000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((22417546593 / 320000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-258124355849813 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (26467873564593 / 100000000000000 : ℝ) ≤ (64686380669979 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (131205080411498061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 26467873564593 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 26467873564593 : ℝ) = (26467873564593 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (468750000000 / 1654242097787 : ℝ) ≤ (69030979922303 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (131205080411498061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (26467873564593 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1654242097787 / 6250000000000 : ℝ)) ≤ (69030979922303 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_111 : ∀ t : ℝ, (22417546593 / 320000000000 : ℝ) < t → t ≤ (4517139266921 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-15747539875453784772346429 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4517139266921 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_112
  have hV : (503071679325790659525169913793203 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (22417546593 / 320000000000 : ℝ) := by norm_num
    refine le_trans V_pt_111 (Vfield_monotoneOn (show (22417546593 / 320000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (22417546593 / 320000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_112 : (8076883026912816184975121916452787 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (4517139266921 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4517139266921 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (26566953352923 / 100000000000000 : ℝ) ≤ Real.sqrt (4517139266921 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4517139266921 / 64000000000000 : ℝ) ≤ (6641738338231 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6641738338231 / 25000000000000 : ℝ) = (25000000000000 / 6641738338231 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (26566953352923 / 100000000000000 : ℝ) = (2500000000000 / 8855651117641 : ℝ) := by norm_num
  have hL1 : (1364016777757 / 20000000000000 : ℝ) ≤ Real.log (1 + (4517139266921 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4517139266921 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-257432425014137 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6641738338231 / 25000000000000 : ℝ) ≤ (259671227428813 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (131112509936608361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 6641738338231 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 6641738338231 : ℝ) = (6641738338231 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 8855651117641 : ℝ) ≤ (137572706579377 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (131112509936608361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6641738338231 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (26566953352923 / 100000000000000 : ℝ)) ≤ (137572706579377 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_112 : ∀ t : ℝ, (4517139266921 / 64000000000000 : ℝ) < t → t ≤ (2275384607621 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-25162488153044614127613059 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2275384607621 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_113
  have hV : (8076883026912816184975121916452787 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4517139266921 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_112 (Vfield_monotoneOn (show (4517139266921 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4517139266921 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_113 : (40522823283848998955196973339231 / 25000000000000000000000000000000 : ℝ) ≤ Vfield (2275384607621 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2275384607621 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (133328324999 / 500000000000 : ℝ) ≤ Real.sqrt (2275384607621 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2275384607621 / 32000000000000 : ℝ) ≤ (26665664999801 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (26665664999801 / 100000000000000 : ℝ) = (100000000000000 / 26665664999801 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (133328324999 / 500000000000 : ℝ) = (37500000000 / 133328324999 : ℝ) := by norm_num
  have hL1 : (343457719073 / 5000000000000 : ℝ) ≤ Real.log (1 + (2275384607621 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2275384607621 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-128372624490087 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (26665664999801 / 100000000000000 : ℝ) ≤ (65148260015603 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (131020328673248461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 26665664999801 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 26665664999801 : ℝ) = (26665664999801 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (37500000000 / 133328324999 : ℝ) ≤ (274177241507657 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (131020328673248461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (26665664999801 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (133328324999 / 500000000000 : ℝ)) ≤ (274177241507657 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_113 : ∀ t : ℝ, (2275384607621 / 32000000000000 : ℝ) < t → t ≤ (4584399163563 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-125650403642100033919032893 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4584399163563 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_114
  have hV : (40522823283848998955196973339231 / 25000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2275384607621 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_113 (Vfield_monotoneOn (show (2275384607621 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2275384607621 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_114 : (4066095987338150275156925222871317 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (4584399163563 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4584399163563 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (13382006289293 / 50000000000000 : ℝ) ≤ Real.sqrt (4584399163563 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4584399163563 / 64000000000000 : ℝ) ≤ (26764012578587 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (26764012578587 / 100000000000000 : ℝ) = (100000000000000 / 26764012578587 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13382006289293 / 50000000000000 : ℝ) = (3750000000000 / 13382006289293 : ℝ) := by norm_num
  have hL1 : (1729550201703 / 25000000000000 : ℝ) ≤ Real.log (1 + (4584399163563 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4584399163563 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-64015690711423 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (26764012578587 / 100000000000000 : ℝ) ≤ (2043054706397 / 7812500000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130928532437608061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 26764012578587 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 26764012578587 : ℝ) = (26764012578587 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 13382006289293 : ℝ) ≤ (34152402998341 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130928532437608061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (26764012578587 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13382006289293 / 50000000000000 : ℝ)) ≤ (34152402998341 / 125000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_114 : ∀ t : ℝ, (4584399163563 / 64000000000000 : ℝ) < t → t ≤ (1154507277971 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-62746761387075434710655623 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1154507277971 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_115
  have hV : (4066095987338150275156925222871317 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4584399163563 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_114 (Vfield_monotoneOn (show (4584399163563 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4584399163563 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_115 : (8159765197860804951075339684976213 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1154507277971 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1154507277971 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (26862000088077 / 100000000000000 : ℝ) ≤ Real.sqrt (1154507277971 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1154507277971 / 16000000000000 : ℝ) ≤ (13431000044039 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13431000044039 / 50000000000000 : ℝ) = (50000000000000 / 13431000044039 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (26862000088077 / 100000000000000 : ℝ) = (2500000000000 / 8954000029359 : ℝ) := by norm_num
  have hL1 : (3483611594219 / 50000000000000 : ℝ) ≤ Real.log (1 + (1154507277971 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1154507277971 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-255384903028311 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13431000044039 / 50000000000000 : ℝ) ≤ (4100393055921 / 15625000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130837117121595261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 13431000044039 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 13431000044039 : ℝ) = (13431000044039 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 8954000029359 : ℝ) ≤ (272271184243959 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130837117121595261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13431000044039 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (26862000088077 / 100000000000000 : ℝ)) ≤ (272271184243959 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_115 : ∀ t : ℝ, (1154507277971 / 16000000000000 : ℝ) < t → t ≤ (930331812041 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-62670624852976355913084093 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (930331812041 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_116
  have hV : (8159765197860804951075339684976213 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1154507277971 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_115 (Vfield_monotoneOn (show (1154507277971 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1154507277971 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_116 : (8187284544747120876287575912147831 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (930331812041 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (930331812041 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (26959631454399 / 100000000000000 : ℝ) ≤ Real.sqrt (930331812041 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (930331812041 / 12800000000000 : ℝ) ≤ (16849769659 / 62500000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16849769659 / 62500000000 : ℝ) = (62500000000 / 16849769659 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (26959631454399 / 100000000000000 : ℝ) = (2500000000000 / 8986543818133 : ℝ) := by norm_num
  have hL1 : (70162215499 / 1000000000000 : ℝ) ≤ Real.log (1 + (930331812041 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((930331812041 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-254711607229957 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16849769659 / 62500000000 : ℝ) ≤ (263335539885697 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130746078690919961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (62500000000 / 16849769659 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (62500000000 / 16849769659 : ℝ) = (16849769659 / 62500000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 8986543818133 : ℝ) ≤ (54266590037573 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130746078690919961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16849769659 / 62500000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (26959631454399 / 100000000000000 : ℝ)) ≤ (54266590037573 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_116 : ∀ t : ℝ, (930331812041 / 12800000000000 : ℝ) < t → t ≤ (2342644504263 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-125193136454299365082380403 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2342644504263 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_117
  have hV : (8187284544747120876287575912147831 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (930331812041 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_116 (Vfield_monotoneOn (show (930331812041 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (930331812041 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_117 : (8214750234820162119664526626339729 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2342644504263 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2342644504263 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (27056910532841 / 100000000000000 : ℝ) ≤ Real.sqrt (2342644504263 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2342644504263 / 32000000000000 : ℝ) ≤ (13528455266421 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13528455266421 / 50000000000000 : ℝ) = (50000000000000 / 13528455266421 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (27056910532841 / 100000000000000 : ℝ) = (7500000000000 / 27056910532841 : ℝ) := by norm_num
  have hL1 : (1766298978681 / 25000000000000 : ℝ) ≤ Real.log (1 + (2342644504263 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2342644504263 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-254042814402507 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13528455266421 / 50000000000000 : ℝ) ≤ (132121097481247 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130655413183240261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 13528455266421 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 13528455266421 : ℝ) = (13528455266421 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 27056910532841 : ℝ) ≤ (135202176928007 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130655413183240261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13528455266421 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (27056910532841 / 100000000000000 : ℝ)) ≤ (135202176928007 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_117 : ∀ t : ℝ, (2342644504263 / 32000000000000 : ℝ) < t → t ≤ (9404207965373 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2502410420614166946394679 / 1000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9404207965373 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_118
  have hV : (8214750234820162119664526626339729 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2342644504263 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_117 (Vfield_monotoneOn (show (2342644504263 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2342644504263 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_118 : (1645692605480088696464549970198079 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (9404207965373 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9404207965373 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (5421083829991 / 20000000000000 : ℝ) ≤ Real.sqrt (9404207965373 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9404207965373 / 128000000000000 : ℝ) ≤ (6776354787489 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6776354787489 / 25000000000000 : ℝ) = (25000000000000 / 6776354787489 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5421083829991 / 20000000000000 : ℝ) = (1500000000000 / 5421083829991 : ℝ) := by norm_num
  have hL1 : (7089674105741 / 100000000000000 : ℝ) ≤ Real.log (1 + (9404207965373 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9404207965373 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-253710087858919 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6776354787489 / 25000000000000 : ℝ) ≤ (132347068114843 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130610219056521061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 6776354787489 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 6776354787489 : ℝ) = (6776354787489 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 5421083829991 : ℝ) ≤ (67485904611549 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130610219056521061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6776354787489 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5421083829991 / 20000000000000 : ℝ)) ≤ (67485904611549 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_118 : ∀ t : ℝ, (9404207965373 / 128000000000000 : ℝ) < t → t ≤ (4718918956847 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-250097621884485404232769751 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4718918956847 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_119
  have hV : (1645692605480088696464549970198079 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9404207965373 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_118 (Vfield_monotoneOn (show (9404207965373 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9404207965373 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_119 : (1648432497700347253250245513356863 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (4718918956847 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4718918956847 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (5430768221927 / 20000000000000 : ℝ) ≤ Real.sqrt (4718918956847 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4718918956847 / 64000000000000 : ℝ) ≤ (6788460277409 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6788460277409 / 25000000000000 : ℝ) = (25000000000000 / 6788460277409 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5430768221927 / 20000000000000 : ℝ) = (1500000000000 / 5430768221927 : ℝ) := by norm_num
  have hL1 : (1422829261281 / 20000000000000 : ℝ) ≤ Real.log (1 + (4718918956847 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4718918956847 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-253378464714571 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6788460277409 / 25000000000000 : ℝ) ≤ (132572579865629 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (130565116706363861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 6788460277409 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 6788460277409 : ℝ) = (6788460277409 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 5430768221927 : ℝ) ≤ (134742615644207 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (130565116706363861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6788460277409 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5430768221927 / 20000000000000 : ℝ)) ≤ (134742615644207 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_119 : ∀ t : ℝ, (4718918956847 / 64000000000000 : ℝ) < t → t ≤ (1894293572403 / 25600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-249955937413059993818847327 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1894293572403 / 25600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_120
  have hV : (1648432497700347253250245513356863 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4718918956847 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_119 (Vfield_monotoneOn (show (4718918956847 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4718918956847 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
