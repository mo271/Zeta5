import Apery.Table2.U04
import Apery.Table2.U05

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_160 : (10017089701900015711525477641822271 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3519728384093 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3519728384093 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (33164968265159 / 100000000000000 : ℝ) ≤ Real.sqrt (3519728384093 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3519728384093 / 32000000000000 : ℝ) ≤ (829124206629 / 2500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (829124206629 / 2500000000000 : ℝ) = (2500000000000 / 829124206629 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33164968265159 / 100000000000000 : ℝ) = (7500000000000 / 33164968265159 : ℝ) := by norm_num
  have hL1 : (10435236845077 / 100000000000000 : ℝ) ≤ Real.log (1 + (3519728384093 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3519728384093 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-107873824725449 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (829124206629 / 2500000000000 : ℝ) ≤ (320234504194311 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125056182260058561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (2500000000000 / 829124206629 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (2500000000000 / 829124206629 : ℝ) = (829124206629 / 2500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 33164968265159 : ℝ) ≤ (111200685199641 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125056182260058561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (829124206629 / 2500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33164968265159 / 100000000000000 : ℝ)) ≤ (111200685199641 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_160 : ∀ t : ℝ, (3519728384093 / 32000000000000 : ℝ) < t → t ≤ (7061879112973 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-116094399224648297252811429 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7061879112973 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_161
  have hV : (10017089701900015711525477641822271 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3519728384093 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_160 (Vfield_monotoneOn (show (3519728384093 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3519728384093 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_161 : (10033231780128377842038948705342867 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (7061879112973 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7061879112973 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (33217745429243 / 100000000000000 : ℝ) ≤ Real.sqrt (7061879112973 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7061879112973 / 64000000000000 : ℝ) ≤ (8304436357311 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8304436357311 / 25000000000000 : ℝ) = (25000000000000 / 8304436357311 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33217745429243 / 100000000000000 : ℝ) = (7500000000000 / 33217745429243 : ℝ) := by norm_num
  have hL1 : (261669877291 / 2500000000000 : ℝ) ≤ Real.log (1 + (7061879112973 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7061879112973 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-26930635093451 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8304436357311 / 25000000000000 : ℝ) ≤ (320709902775149 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (125008642401974761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 8304436357311 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 8304436357311 : ℝ) = (8304436357311 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 33217745429243 : ℝ) ≤ (222059524449003 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (125008642401974761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8304436357311 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33217745429243 / 100000000000000 : ℝ)) ≤ (222059524449003 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_161 : ∀ t : ℝ, (7061879112973 / 64000000000000 : ℝ) < t → t ≤ (44276884111 / 400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-232022146086143418675401883 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (44276884111 / 400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_162
  have hV : (10033231780128377842038948705342867 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7061879112973 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_161 (Vfield_monotoneOn (show (7061879112973 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7061879112973 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_162 : (10049356532379005604203124307829017 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (44276884111 / 400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (44276884111 / 400000000000 : ℝ) := by norm_num
  have hs1 : (33270438872593 / 100000000000000 : ℝ) ≤ Real.sqrt (44276884111 / 400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (44276884111 / 400000000000 : ℝ) ≤ (16635219436297 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16635219436297 / 50000000000000 : ℝ) = (50000000000000 / 16635219436297 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33270438872593 / 100000000000000 : ℝ) = (7500000000000 / 33270438872593 : ℝ) := by norm_num
  have hL1 : (2099668676423 / 20000000000000 : ℝ) ≤ Real.log (1 + (44276884111 / 400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((44276884111 / 400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-215143424761617 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16635219436297 / 50000000000000 : ℝ) ≤ (321184397486067 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124961192930882961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 16635219436297 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 16635219436297 : ℝ) = (16635219436297 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 33270438872593 : ℝ) ≤ (221719250335619 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124961192930882961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16635219436297 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33270438872593 / 100000000000000 : ℝ)) ≤ (221719250335619 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_162 : ∀ t : ℝ, (44276884111 / 400000000000 : ℝ) < t → t ≤ (7106723802547 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23185723736920935482546757 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7106723802547 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_163
  have hV : (10049356532379005604203124307829017 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (44276884111 / 400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_162 (Vfield_monotoneOn (show (44276884111 / 400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (44276884111 / 400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_163 : (10065464009255817022325048437968299 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (7106723802547 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7106723802547 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (33323048992371 / 100000000000000 : ℝ) ≤ Real.sqrt (7106723802547 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7106723802547 / 64000000000000 : ℝ) ≤ (8330762248093 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8330762248093 / 25000000000000 : ℝ) = (25000000000000 / 8330762248093 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33323048992371 / 100000000000000 : ℝ) = (2500000000000 / 11107682997457 : ℝ) := by norm_num
  have hL1 : (10529881722783 / 100000000000000 : ℝ) ≤ Real.log (1 + (7106723802547 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7106723802547 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-42968535200589 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8330762248093 / 25000000000000 : ℝ) ≤ (8041449811811 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124913833432245661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 8330762248093 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 8330762248093 : ℝ) = (8330762248093 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 11107682997457 : ℝ) ≤ (221380536047541 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124913833432245661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8330762248093 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33323048992371 / 100000000000000 : ℝ)) ≤ (221380536047541 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_163 : ∀ t : ℝ, (7106723802547 / 64000000000000 : ℝ) < t → t ≤ (3564573073667 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-231694008718903147126734307 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3564573073667 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_164
  have hV : (10065464009255817022325048437968299 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7106723802547 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_163 (Vfield_monotoneOn (show (7106723802547 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7106723802547 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_164 : (5040777130578013747813288529867007 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (3564573073667 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3564573073667 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (16687788091303 / 50000000000000 : ℝ) ≤ Real.sqrt (3564573073667 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3564573073667 / 32000000000000 : ℝ) ≤ (33375576182607 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (33375576182607 / 100000000000000 : ℝ) = (100000000000000 / 33375576182607 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16687788091303 / 50000000000000 : ℝ) = (3750000000000 / 16687788091303 : ℝ) := by norm_num
  have hL1 : (10561410119917 / 100000000000000 : ℝ) ≤ Real.log (1 + (3564573073667 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3564573073667 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-214542829030997 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (33375576182607 / 100000000000000 : ℝ) ≤ (161065345923763 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124866563494737061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 33375576182607 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 33375576182607 : ℝ) = (33375576182607 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 16687788091303 : ℝ) ≤ (11052168485067 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124866563494737061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (33375576182607 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16687788091303 / 50000000000000 : ℝ)) ≤ (11052168485067 / 50000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_164 : ∀ t : ℝ, (3564573073667 / 32000000000000 : ℝ) < t → t ≤ (7151568492121 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-231532400941580871156167519 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7151568492121 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_165
  have hV : (5040777130578013747813288529867007 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3564573073667 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_164 (Vfield_monotoneOn (show (3564573073667 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3564573073667 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_165 : (1262203417284039135100663233805551 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (7151568492121 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7151568492121 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (4178502604279 / 12500000000000 : ℝ) ≤ Real.sqrt (7151568492121 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7151568492121 / 64000000000000 : ℝ) ≤ (33428020834233 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (33428020834233 / 100000000000000 : ℝ) = (100000000000000 / 33428020834233 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4178502604279 / 12500000000000 : ℝ) = (937500000000 / 4178502604279 : ℝ) := by norm_num
  have hL1 : (10592928579787 / 100000000000000 : ℝ) ≤ Real.log (1 + (7151568492121 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7151568492121 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-214243878453971 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (33428020834233 / 100000000000000 : ℝ) ≤ (322602499692851 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124819382710204561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 33428020834233 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 33428020834233 : ℝ) = (33428020834233 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (937500000000 / 4178502604279 : ℝ) ≤ (55176934884993 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124819382710204561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (33428020834233 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4178502604279 / 12500000000000 : ℝ)) ≤ (55176934884993 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_165 : ∀ t : ℝ, (7151568492121 / 64000000000000 : ℝ) < t → t ≤ (1793497709227 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-231372358800150935494650111 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1793497709227 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_166
  have hV : (1262203417284039135100663233805551 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7151568492121 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_165 (Vfield_monotoneOn (show (7151568492121 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7151568492121 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_166 : (2528420822648495296722305488962589 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (1793497709227 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1793497709227 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (8370095833781 / 25000000000000 : ℝ) ≤ Real.sqrt (1793497709227 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1793497709227 / 16000000000000 : ℝ) ≤ (267843066681 / 800000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (267843066681 / 800000000000 : ℝ) = (800000000000 / 267843066681 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8370095833781 / 25000000000000 : ℝ) = (1875000000000 / 8370095833781 : ℝ) := by norm_num
  have hL1 : (10624437108653 / 100000000000000 : ℝ) ≤ Real.log (1 + (1793497709227 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1793497709227 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-213945818928279 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (267843066681 / 800000000000 : ℝ) ≤ (323073420058573 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124772290673632361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (800000000000 / 267843066681 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (800000000000 / 267843066681 : ℝ) = (267843066681 / 800000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 8370095833781 : ℝ) ≤ (220373633931037 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124772290673632361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (267843066681 / 800000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8370095833781 / 25000000000000 : ℝ)) ≤ (220373633931037 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_166 : ∀ t : ℝ, (1793497709227 / 16000000000000 : ℝ) < t → t ≤ (1439282636339 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-231213830637784918682848603 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1439282636339 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_167
  have hV : (2528420822648495296722305488962589 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1793497709227 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_166 (Vfield_monotoneOn (show (1793497709227 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1793497709227 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_167 : (2532430541976158118131849208316339 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (1439282636339 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1439282636339 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (8383166017531 / 25000000000000 : ℝ) ≤ Real.sqrt (1439282636339 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1439282636339 / 12800000000000 : ℝ) ≤ (268261312561 / 800000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (268261312561 / 800000000000 : ℝ) = (800000000000 / 268261312561 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8383166017531 / 25000000000000 : ℝ) = (1875000000000 / 8383166017531 : ℝ) := by norm_num
  have hL1 : (2663983928193 / 25000000000000 : ℝ) ≤ Real.log (1 + (1439282636339 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1439282636339 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-213648645157971 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (268261312561 / 800000000000 : ℝ) ≤ (40442932120469 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124725286983114461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (800000000000 / 268261312561 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (800000000000 / 268261312561 : ℝ) = (268261312561 / 800000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 8383166017531 : ℝ) ≤ (11002052068257 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124725286983114461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (268261312561 / 800000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8383166017531 / 25000000000000 : ℝ)) ≤ (11002052068257 / 50000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_167 : ∀ t : ℝ, (1439282636339 / 12800000000000 : ℝ) < t → t ≤ (3609417763241 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-231056768046877822325105561 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3609417763241 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_168
  have hV : (2532430541976158118131849208316339 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1439282636339 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_167 (Vfield_monotoneOn (show (1439282636339 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1439282636339 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_168 : (10145744019786370754204823005967827 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3609417763241 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3609417763241 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (33584863421083 / 100000000000000 : ℝ) ≤ Real.sqrt (3609417763241 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3609417763241 / 32000000000000 : ℝ) ≤ (8396215855271 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8396215855271 / 25000000000000 : ℝ) = (25000000000000 / 8396215855271 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33584863421083 / 100000000000000 : ℝ) = (7500000000000 / 33584863421083 : ℝ) := by norm_num
  have hL1 : (2137484879679 / 20000000000000 : ℝ) ≤ Real.log (1 + (3609417763241 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3609417763241 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-53338087973543 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8396215855271 / 25000000000000 : ℝ) ≤ (81003153599193 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124678371239812461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 8396215855271 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 8396215855271 : ℝ) = (8396215855271 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 33584863421083 : ℝ) ≤ (2746374380677 / 12500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124678371239812461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8396215855271 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33584863421083 / 100000000000000 : ℝ)) ≤ (2746374380677 / 12500000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_168 : ∀ t : ℝ, (3609417763241 / 32000000000000 : ℝ) < t → t ≤ (7241257871269 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-115450562788394130956404193 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7241257871269 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_169
  have hV : (10145744019786370754204823005967827 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3609417763241 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_168 (Vfield_monotoneOn (show (3609417763241 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3609417763241 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_169 : (2032349779123359237535754938891913 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (7241257871269 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7241257871269 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (6727396353377 / 20000000000000 : ℝ) ≤ Real.sqrt (7241257871269 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7241257871269 / 64000000000000 : ℝ) ≤ (16818490883443 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16818490883443 / 50000000000000 : ℝ) = (50000000000000 / 16818490883443 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6727396353377 / 20000000000000 : ℝ) = (1500000000000 / 6727396353377 : ℝ) := by norm_num
  have hL1 : (2143780634353 / 20000000000000 : ℝ) ≤ Real.log (1 + (7241257871269 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7241257871269 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-106528466967263 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16818490883443 / 50000000000000 : ℝ) ≤ (81120224078897 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124631543047930861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 16818490883443 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 16818490883443 : ℝ) = (16818490883443 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 6727396353377 : ℝ) ≤ (54845087482417 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124631543047930861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16818490883443 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6727396353377 / 20000000000000 : ℝ)) ≤ (54845087482417 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_169 : ∀ t : ℝ, (7241257871269 / 64000000000000 : ℝ) < t → t ≤ (907960027007 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-57686715118727004761498913 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (907960027007 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_170
  have hV : (2032349779123359237535754938891913 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7241257871269 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_169 (Vfield_monotoneOn (show (7241257871269 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7241257871269 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_170 : (5088868422286306240734532455855367 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (907960027007 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (907960027007 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (16844509741743 / 50000000000000 : ℝ) ≤ Real.sqrt (907960027007 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (907960027007 / 8000000000000 : ℝ) ≤ (33689019483487 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (33689019483487 / 100000000000000 : ℝ) = (100000000000000 / 33689019483487 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16844509741743 / 50000000000000 : ℝ) = (1250000000000 / 5614836580581 : ℝ) := by norm_num
  have hL1 : (5375186019561 / 50000000000000 : ℝ) ≤ Real.log (1 + (907960027007 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((907960027007 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-26595298265331 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (33689019483487 / 100000000000000 : ℝ) ≤ (162474153324061 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124584802014677461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 33689019483487 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 33689019483487 : ℝ) = (33689019483487 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 5614836580581 : ℝ) ≤ (219052228641271 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124584802014677461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (33689019483487 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16844509741743 / 50000000000000 : ℝ)) ≤ (219052228641271 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_170 : ∀ t : ℝ, (907960027007 / 8000000000000 : ℝ) < t → t ≤ (7286102560843 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-461187864913065349105907 / 200000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7286102560843 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_171
  have hV : (5088868422286306240734532455855367 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (907960027007 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_170 (Vfield_monotoneOn (show (907960027007 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (907960027007 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_171 : (10193707915628942705448413520647167 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (7286102560843 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7286102560843 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (33740976943943 / 100000000000000 : ℝ) ≤ Real.sqrt (7286102560843 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7286102560843 / 64000000000000 : ℝ) ≤ (4217622117993 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4217622117993 / 12500000000000 : ℝ) = (12500000000000 / 4217622117993 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33740976943943 / 100000000000000 : ℝ) = (7500000000000 / 33740976943943 : ℝ) := by norm_num
  have hL1 : (10781831006699 / 100000000000000 : ℝ) ≤ Real.log (1 + (7286102560843 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7286102560843 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-10623435167379 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4217622117993 / 12500000000000 : ℝ) ≤ (325414849292557 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124538147750233961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 4217622117993 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 4217622117993 : ℝ) = (4217622117993 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 33740976943943 : ℝ) ≤ (1367034847219 / 6250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124538147750233961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4217622117993 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33740976943943 / 100000000000000 : ℝ)) ≤ (1367034847219 / 6250000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_171 : ∀ t : ℝ, (7286102560843 / 64000000000000 : ℝ) < t → t ≤ (730852490563 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-230442303499688443345041983 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (730852490563 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_172
  have hV : (10193707915628942705448413520647167 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7286102560843 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_171 (Vfield_monotoneOn (show (7286102560843 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7286102560843 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_172 : (10209662157559080787179580168637667 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (730852490563 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (730852490563 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (33792854518443 / 100000000000000 : ℝ) ≤ Real.sqrt (730852490563 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (730852490563 / 6400000000000 : ℝ) ≤ (8448213629611 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8448213629611 / 25000000000000 : ℝ) = (25000000000000 / 8448213629611 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33792854518443 / 100000000000000 : ℝ) = (2500000000000 / 11264284839481 : ℝ) := by norm_num
  have hL1 : (10813280080721 / 100000000000000 : ℝ) ≤ Real.log (1 + (730852490563 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((730852490563 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-212175880543267 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8448213629611 / 25000000000000 : ℝ) ≤ (162940264058817 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124491579867726261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 8448213629611 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 8448213629611 : ℝ) = (8448213629611 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 11264284839481 : ℝ) ≤ (218400379751969 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124491579867726261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8448213629611 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33792854518443 / 100000000000000 : ℝ)) ≤ (218400379751969 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_172 : ∀ t : ℝ, (730852490563 / 6400000000000 : ℝ) < t → t ≤ (7330947250417 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-28786492207709553638044223 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7330947250417 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_173
  have hV : (10209662157559080787179580168637667 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (730852490563 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_172 (Vfield_monotoneOn (show (730852490563 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (730852490563 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_173 : (5112799809468449548678089856297961 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (7330947250417 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7330947250417 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (16922326287169 / 50000000000000 : ℝ) ≤ Real.sqrt (7330947250417 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7330947250417 / 64000000000000 : ℝ) ≤ (33844652574339 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (33844652574339 / 100000000000000 : ℝ) = (100000000000000 / 33844652574339 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16922326287169 / 50000000000000 : ℝ) = (3750000000000 / 16922326287169 : ℝ) := by norm_num
  have hL1 : (1084471926741 / 10000000000000 : ℝ) ≤ Real.log (1 + (7330947250417 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7330947250417 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-26485489086003 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (33844652574339 / 100000000000000 : ℝ) ≤ (5099146046297 / 15625000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124445097983188861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 33844652574339 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 33844652574339 : ℝ) = (33844652574339 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 16922326287169 : ℝ) ≤ (54519157606603 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124445097983188861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (33844652574339 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16922326287169 / 50000000000000 : ℝ)) ≤ (54519157606603 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_173 : ∀ t : ℝ, (7330947250417 / 64000000000000 : ℝ) < t → t ≤ (1838342398801 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23014280091458240762421831 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1838342398801 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_174
  have hV : (5112799809468449548678089856297961 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7330947250417 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_173 (Vfield_monotoneOn (show (7330947250417 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7330947250417 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_174 : (10241520348135707512710666226110499 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1838342398801 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1838342398801 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (33896371476171 / 100000000000000 : ℝ) ≤ Real.sqrt (1838342398801 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1838342398801 / 16000000000000 : ℝ) ≤ (8474092869043 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8474092869043 / 25000000000000 : ℝ) = (25000000000000 / 8474092869043 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33896371476171 / 100000000000000 : ℝ) = (2500000000000 / 11298790492057 : ℝ) := by norm_num
  have hL1 : (10876148572981 / 100000000000000 : ℝ) ≤ Real.log (1 + (1838342398801 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1838342398801 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-8463711792161 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8474092869043 / 25000000000000 : ℝ) ≤ (326809309639511 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124398701715538561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 8474092869043 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 8474092869043 : ℝ) = (8474092869043 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 11298790492057 : ℝ) ≤ (217754316884599 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124398701715538561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8474092869043 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33896371476171 / 100000000000000 : ℝ)) ≤ (217754316884599 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_174 : ∀ t : ℝ, (1838342398801 / 16000000000000 : ℝ) < t → t ≤ (3699107142389 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-229848087282723942760056889 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3699107142389 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_175
  have hV : (10241520348135707512710666226110499 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1838342398801 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_174 (Vfield_monotoneOn (show (1838342398801 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1838342398801 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_175 : (10273311802498310169557600135805313 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3699107142389 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3699107142389 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (33999573261977 / 100000000000000 : ℝ) ≤ Real.sqrt (3699107142389 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3699107142389 / 32000000000000 : ℝ) ≤ (16999786630989 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16999786630989 / 50000000000000 : ℝ) = (50000000000000 / 16999786630989 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (33999573261977 / 100000000000000 : ℝ) = (7500000000000 / 33999573261977 : ℝ) := by norm_num
  have hL1 : (10938977565599 / 100000000000000 : ℝ) ≤ Real.log (1 + (3699107142389 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3699107142389 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-211013089254693 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16999786630989 / 50000000000000 : ℝ) ≤ (40966835198393 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124306164520775261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 16999786630989 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 16999786630989 : ℝ) = (16999786630989 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 33999573261977 : ℝ) ≤ (108556977463753 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124306164520775261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16999786630989 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (33999573261977 / 100000000000000 : ℝ)) ≤ (108556977463753 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_175 : ∀ t : ℝ, (3699107142389 / 32000000000000 : ℝ) < t → t ≤ (465191185897 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-57389480852071813949765201 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (465191185897 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_176
  have hV : (10273311802498310169557600135805313 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3699107142389 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_175 (Vfield_monotoneOn (show (3699107142389 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3699107142389 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_176 : (2061007380733416942250324642067129 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (465191185897 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (465191185897 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (6820492547441 / 20000000000000 : ℝ) ≤ Real.sqrt (465191185897 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (465191185897 / 4000000000000 : ℝ) ≤ (17051231368603 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17051231368603 / 50000000000000 : ℝ) = (50000000000000 / 17051231368603 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6820492547441 / 20000000000000 : ℝ) = (1500000000000 / 6820492547441 : ℝ) := by norm_num
  have hL1 : (11001767108179 / 100000000000000 : ℝ) ≤ Real.log (1 + (465191185897 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((465191185897 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-42087344986127 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17051231368603 / 50000000000000 : ℝ) ≤ (328656673882761 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124213965291213561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 17051231368603 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 17051231368603 : ℝ) = (17051231368603 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 6820492547441 : ℝ) ≤ (216479210511927 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124213965291213561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17051231368603 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6820492547441 / 20000000000000 : ℝ)) ≤ (216479210511927 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_176 : ∀ t : ℝ, (465191185897 / 4000000000000 : ℝ) < t → t ≤ (3743951831963 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-229272092642673961181051671 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3743951831963 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_177
  have hV : (2061007380733416942250324642067129 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (465191185897 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_176 (Vfield_monotoneOn (show (465191185897 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (465191185897 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_177 : (5168348015754649418618278806558827 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (3743951831963 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3743951831963 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (17102521360083 / 50000000000000 : ℝ) ≤ Real.sqrt (3743951831963 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3743951831963 / 32000000000000 : ℝ) ≤ (34205042720167 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (34205042720167 / 100000000000000 : ℝ) = (100000000000000 / 34205042720167 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17102521360083 / 50000000000000 : ℝ) = (1250000000000 / 5700840453361 : ℝ) := by norm_num
  have hL1 : (1106451725023 / 10000000000000 : ℝ) ≤ Real.log (1 + (3743951831963 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3743951831963 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-41972732707419 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (34205042720167 / 100000000000000 : ℝ) ≤ (329575316006881 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124122101078801561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 34205042720167 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 34205042720167 : ℝ) = (34205042720167 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 5700840453361 : ℝ) ≤ (843164070181 / 3906250000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124122101078801561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (34205042720167 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17102521360083 / 50000000000000 : ℝ)) ≤ (843164070181 / 3906250000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_177 : ∀ t : ℝ, (3743951831963 / 32000000000000 : ℝ) < t → t ≤ (15065496707 / 128000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2862379973050526671968801 / 1250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (15065496707 / 128000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_178
  have hV : (5168348015754649418618278806558827 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3743951831963 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_177 (Vfield_monotoneOn (show (3743951831963 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3743951831963 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_178 : (2592072390689949330948772687422671 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (15065496707 / 128000000000 : ℝ) := by
  have hp : (0 : ℝ) < (15065496707 / 128000000000 : ℝ) := by norm_num
  have hs1 : (8576828996759 / 25000000000000 : ℝ) ≤ Real.sqrt (15065496707 / 128000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (15065496707 / 128000000000 : ℝ) ≤ (34307315987037 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (34307315987037 / 100000000000000 : ℝ) = (100000000000000 / 34307315987037 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8576828996759 / 25000000000000 : ℝ) = (1875000000000 / 8576828996759 : ℝ) := by norm_num
  have hL1 : (1112722804117 / 10000000000000 : ℝ) ≤ Real.log (1 + (15065496707 / 128000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((15065496707 / 128000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-209293867433929 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (34307315987037 / 100000000000000 : ℝ) ≤ (330490637007463 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (124030568978743361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 34307315987037 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 34307315987037 : ℝ) = (34307315987037 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 8576828996759 : ℝ) ≤ (43045249854457 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (124030568978743361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (34307315987037 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8576828996759 / 25000000000000 : ℝ)) ≤ (43045249854457 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_178 : ∀ t : ℝ, (15065496707 / 128000000000 : ℝ) < t → t ≤ (3788796521537 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-114356329426800556612511627 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3788796521537 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_179
  have hV : (2592072390689949330948772687422671 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (15065496707 / 128000000000 : ℝ) := by norm_num
    refine le_trans V_pt_178 (Vfield_monotoneOn (show (15065496707 / 128000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (15065496707 / 128000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_179 : (2599954467760629593146426226737727 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (3788796521537 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3788796521537 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (8602321318183 / 25000000000000 : ℝ) ≤ Real.sqrt (3788796521537 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3788796521537 / 32000000000000 : ℝ) ≤ (34409285272733 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (34409285272733 / 100000000000000 : ℝ) = (100000000000000 / 34409285272733 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8602321318183 / 25000000000000 : ℝ) = (1875000000000 / 8602321318183 : ℝ) := by norm_num
  have hL1 : (5594949765161 / 50000000000000 : ℝ) ≤ Real.log (1 + (3788796521537 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3788796521537 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-208727299620769 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (34409285272733 / 100000000000000 : ℝ) ≤ (165701332754413 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (123939366128607061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 34409285272733 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 34409285272733 : ℝ) = (34409285272733 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 8602321318183 : ℝ) ≤ (214607874021623 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (123939366128607061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (34409285272733 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8602321318183 / 25000000000000 : ℝ)) ≤ (214607874021623 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_179 : ∀ t : ℝ, (3788796521537 / 32000000000000 : ℝ) < t → t ≤ (952804716581 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-228438710384632926968803913 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (952804716581 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_180
  have hV : (2599954467760629593146426226737727 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3788796521537 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_179 (Vfield_monotoneOn (show (3788796521537 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3788796521537 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_180 : (10431281326894356492104727087955361 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (952804716581 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (952804716581 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (34510953271769 / 100000000000000 : ℝ) ≤ Real.sqrt (952804716581 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (952804716581 / 8000000000000 : ℝ) ≤ (3451095327177 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3451095327177 / 10000000000000 : ℝ) = (10000000000000 / 3451095327177 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (34510953271769 / 100000000000000 : ℝ) = (7500000000000 / 34510953271769 : ℝ) := by norm_num
  have hL1 : (11252531766917 / 100000000000000 : ℝ) ≤ Real.log (1 + (952804716581 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((952804716581 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-104081961861303 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3451095327177 / 10000000000000 : ℝ) ≤ (332311429720367 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (123848489707452961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 3451095327177 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 3451095327177 : ℝ) = (3451095327177 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 34510953271769 : ℝ) ≤ (213994799375043 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (123848489707452961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3451095327177 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (34510953271769 / 100000000000000 : ℝ)) ≤ (213994799375043 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_180 : ∀ t : ℝ, (952804716581 / 8000000000000 : ℝ) < t → t ≤ (3833641211111 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-114084200122073659290196963 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3833641211111 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_181
  have hV : (10431281326894356492104727087955361 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (952804716581 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_180 (Vfield_monotoneOn (show (952804716581 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (952804716581 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_181 : (5231340149185374555603198374083567 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (3833641211111 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3833641211111 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (17306161319543 / 50000000000000 : ℝ) ≤ Real.sqrt (3833641211111 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3833641211111 / 32000000000000 : ℝ) ≤ (34612322639087 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (34612322639087 / 100000000000000 : ℝ) = (100000000000000 / 34612322639087 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17306161319543 / 50000000000000 : ℝ) = (3750000000000 / 17306161319543 : ℝ) := by norm_num
  have hL1 : (2263024960019 / 20000000000000 : ℝ) ≤ Real.log (1 + (3833641211111 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3833641211111 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-207603704001769 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (34612322639087 / 100000000000000 : ℝ) ≤ (333216957444983 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (123757936934991361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 34612322639087 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 34612322639087 : ℝ) = (34612322639087 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 17306161319543 : ℝ) ≤ (53346737505493 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (123757936934991361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (34612322639087 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17306161319543 / 50000000000000 : ℝ)) ≤ (53346737505493 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_181 : ∀ t : ℝ, (3833641211111 / 32000000000000 : ℝ) < t → t ≤ (1928031777949 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-227901587824857215434498113 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1928031777949 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_182
  have hV : (5231340149185374555603198374083567 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3833641211111 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_181 (Vfield_monotoneOn (show (3833641211111 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3833641211111 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_182 : (5247007574365100444559231143549901 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1928031777949 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1928031777949 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (17356697995429 / 50000000000000 : ℝ) ≤ Real.sqrt (1928031777949 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1928031777949 / 16000000000000 : ℝ) ≤ (34713395990859 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (34713395990859 / 100000000000000 : ℝ) = (100000000000000 / 34713395990859 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17356697995429 / 50000000000000 : ℝ) = (3750000000000 / 17356697995429 : ℝ) := by norm_num
  have hL1 : (11377678678901 / 100000000000000 : ℝ) ≤ Real.log (1 + (1928031777949 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1928031777949 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-8281864209613 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (34713395990859 / 100000000000000 : ℝ) ≤ (334119276087333 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (123667705070756361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 34713395990859 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 34713395990859 : ℝ) = (34713395990859 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 17356697995429 : ℝ) ≤ (106392126070831 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (123667705070756361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (34713395990859 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17356697995429 / 50000000000000 : ℝ)) ≤ (106392126070831 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_182 : ∀ t : ℝ, (1928031777949 / 16000000000000 : ℝ) < t → t ≤ (121903382671 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-227377944111885152681370679 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (121903382671 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_183
  have hV : (5247007574365100444559231143549901 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1928031777949 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_182 (Vfield_monotoneOn (show (1928031777949 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1928031777949 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_183 : (1319561741311833811205456641772211 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (121903382671 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (121903382671 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (4364333115419 / 12500000000000 : ℝ) ≤ Real.sqrt (121903382671 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (121903382671 / 1000000000000 : ℝ) ≤ (34914664923353 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (34914664923353 / 100000000000000 : ℝ) = (100000000000000 / 34914664923353 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4364333115419 / 12500000000000 : ℝ) = (937500000000 / 4364333115419 : ℝ) := by norm_num
  have hL1 : (92021353353 / 800000000000 : ℝ) ≤ Real.log (1 + (121903382671 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((121903382671 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-8237665316773 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (34914664923353 / 100000000000000 : ℝ) ≤ (335914393800623 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (123488193299427361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 34914664923353 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 34914664923353 : ℝ) = (34914664923353 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (937500000000 / 4364333115419 : ℝ) ≤ (423188045481 / 2000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (123488193299427361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (34914664923353 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4364333115419 / 12500000000000 : ℝ)) ≤ (423188045481 / 2000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_183 : ∀ t : ℝ, (121903382671 / 1000000000000 : ℝ) < t → t ≤ (1972876467523 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-226866841533911604759988019 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1972876467523 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_184
  have hV : (1319561741311833811205456641772211 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (121903382671 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_183 (Vfield_monotoneOn (show (121903382671 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (121903382671 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_184 : (1327340066030117220377705610714631 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (1972876467523 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1972876467523 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (4389347531599 / 12500000000000 : ℝ) ≤ Real.sqrt (1972876467523 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1972876467523 / 16000000000000 : ℝ) ≤ (35114780252793 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (35114780252793 / 100000000000000 : ℝ) = (100000000000000 / 35114780252793 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4389347531599 / 12500000000000 : ℝ) = (937500000000 / 4389347531599 : ℝ) := by norm_num
  have hL1 : (5813751814063 / 50000000000000 : ℝ) ≤ Real.log (1 + (1972876467523 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1972876467523 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-51212184229541 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (35114780252793 / 100000000000000 : ℝ) ≤ (337696994432507 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (123309933236238961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 35114780252793 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 35114780252793 : ℝ) = (35114780252793 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (937500000000 / 4389347531599 : ℝ) ≤ (52605887249663 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (123309933236238961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (35114780252793 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4389347531599 / 12500000000000 : ℝ)) ≤ (52605887249663 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_184 : ∀ t : ℝ, (1972876467523 / 16000000000000 : ℝ) < t → t ≤ (199529881231 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-226367461898046543146071251 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (199529881231 / 1600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_185
  have hV : (1327340066030117220377705610714631 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1972876467523 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_184 (Vfield_monotoneOn (show (1972876467523 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1972876467523 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_185 : (5340348875132960052091990442877597 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (199529881231 / 1600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (199529881231 / 1600000000000 : ℝ) := by norm_num
  have hs1 : (17656880795413 / 50000000000000 : ℝ) ≤ Real.sqrt (199529881231 / 1600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (199529881231 / 1600000000000 : ℝ) ≤ (35313761590827 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (35313761590827 / 100000000000000 : ℝ) = (100000000000000 / 35313761590827 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17656880795413 / 50000000000000 : ℝ) = (3750000000000 / 17656880795413 : ℝ) := by norm_num
  have hL1 : (11752182444981 / 100000000000000 : ℝ) ≤ Real.log (1 + (199529881231 / 1600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((199529881231 / 1600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-203767656122123 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (35313761590827 / 100000000000000 : ℝ) ≤ (8486682091897 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (123132904311901661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 35313761590827 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 35313761590827 : ℝ) = (35313761590827 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 17656880795413 : ℝ) ≤ (209272290285427 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (123132904311901661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (35313761590827 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17656880795413 / 50000000000000 : ℝ)) ≤ (209272290285427 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_185 : ∀ t : ℝ, (199529881231 / 1600000000000 : ℝ) < t → t ≤ (2017721157097 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-112939542362542755298495617 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2017721157097 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_186
  have hV : (5340348875132960052091990442877597 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (199529881231 / 1600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_185 (Vfield_monotoneOn (show (199529881231 / 1600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (199529881231 / 1600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_186 : (10742428358469915265508688756966619 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2017721157097 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2017721157097 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (35511627999651 / 100000000000000 : ℝ) ≤ Real.sqrt (2017721157097 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2017721157097 / 16000000000000 : ℝ) ≤ (8877906999913 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8877906999913 / 25000000000000 : ℝ) = (25000000000000 / 8877906999913 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (35511627999651 / 100000000000000 : ℝ) = (2500000000000 / 11837209333217 : ℝ) := by norm_num
  have hL1 : (742294125457 / 6250000000000 : ℝ) ≤ Real.log (1 + (2017721157097 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2017721157097 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-202698137794737 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8877906999913 / 25000000000000 : ℝ) ≤ (170612730786483 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (122957086522193061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 8877906999913 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 8877906999913 : ℝ) = (8877906999913 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 11837209333217 : ℝ) ≤ (104069863231127 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (122957086522193061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8877906999913 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (35511627999651 / 100000000000000 : ℝ)) ≤ (104069863231127 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_186 : ∀ t : ℝ, (2017721157097 / 16000000000000 : ℝ) < t → t ≤ (510035875471 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-225401070431143083619121989 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (510035875471 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_187
  have hV : (10742428358469915265508688756966619 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2017721157097 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_186 (Vfield_monotoneOn (show (2017721157097 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2017721157097 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_187 : (10803915069130726970910784365685773 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (510035875471 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (510035875471 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (35708398013317 / 100000000000000 : ℝ) ≤ Real.sqrt (510035875471 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (510035875471 / 4000000000000 : ℝ) ≤ (17854199006659 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17854199006659 / 50000000000000 : ℝ) = (50000000000000 / 17854199006659 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (35708398013317 / 100000000000000 : ℝ) = (7500000000000 / 35708398013317 : ℝ) := by norm_num
  have hL1 : (6000537350647 / 50000000000000 : ℝ) ≤ Real.log (1 + (510035875471 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((510035875471 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-100819968611573 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17854199006659 / 50000000000000 : ℝ) ≤ (42871465341561 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (122782460406240861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 17854199006659 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 17854199006659 : ℝ) = (17854199006659 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 35708398013317 : ℝ) ≤ (207025356894601 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (122782460406240861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17854199006659 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (35708398013317 / 100000000000000 : ℝ)) ≤ (207025356894601 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_187 : ∀ t : ℝ, (510035875471 / 4000000000000 : ℝ) < t → t ≤ (1042494095729 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-44894780085098190418874617 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1042494095729 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_188
  have hV : (10803915069130726970910784365685773 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (510035875471 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_187 (Vfield_monotoneOn (show (510035875471 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (510035875471 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_188 : (10926167439527539722696731482483943 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1042494095729 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1042494095729 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (36098720471247 / 100000000000000 : ℝ) ≤ Real.sqrt (1042494095729 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1042494095729 / 8000000000000 : ℝ) ≤ (2256170029453 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2256170029453 / 6250000000000 : ℝ) = (6250000000000 / 2256170029453 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (36098720471247 / 100000000000000 : ℝ) = (2500000000000 / 12032906823749 : ℝ) := by norm_num
  have hL1 : (12249349021731 / 100000000000000 : ℝ) ≤ Real.log (1 + (1042494095729 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1042494095729 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-99778274307437 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2256170029453 / 6250000000000 : ℝ) ≤ (86607311834001 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (122436707945889261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 2256170029453 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 2256170029453 : ℝ) = (2256170029453 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 12032906823749 : ℝ) ≤ (204849289978397 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (122436707945889261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2256170029453 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (36098720471247 / 100000000000000 : ℝ)) ≤ (204849289978397 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_188 : ∀ t : ℝ, (1042494095729 / 8000000000000 : ℝ) < t → t ≤ (266229110129 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-223582016111935778746211333 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (266229110129 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_189
  have hV : (10926167439527539722696731482483943 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1042494095729 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_188 (Vfield_monotoneOn (show (1042494095729 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1042494095729 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_189 : (11047475709012300535941295210629647 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (266229110129 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (266229110129 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (36484867419863 / 100000000000000 : ℝ) ≤ Real.sqrt (266229110129 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (266229110129 / 2000000000000 : ℝ) ≤ (4560608427483 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4560608427483 / 12500000000000 : ℝ) = (12500000000000 / 4560608427483 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (36484867419863 / 100000000000000 : ℝ) = (7500000000000 / 36484867419863 : ℝ) := by norm_num
  have hL1 : (1562126058381 / 12500000000000 : ℝ) ≤ Real.log (1 + (266229110129 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((266229110129 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24689460090297 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4560608427483 / 12500000000000 : ℝ) ≤ (349841313291351 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (122095501350354561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 4560608427483 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 4560608427483 : ℝ) = (4560608427483 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 36484867419863 : ℝ) ≤ (40548088099037 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (122095501350354561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4560608427483 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (36484867419863 / 100000000000000 : ℝ)) ≤ (40548088099037 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_189 : ∀ t : ℝ, (266229110129 / 2000000000000 : ℝ) < t → t ≤ (110976113009 / 800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-221891612447916974075661051 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (110976113009 / 800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_190
  have hV : (11047475709012300535941295210629647 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (266229110129 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_189 (Vfield_monotoneOn (show (266229110129 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (266229110129 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_190 : (2257467992170528960953351512336197 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (110976113009 / 800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (110976113009 / 800000000000 : ℝ) := by norm_num
  have hs1 : (7449030574813 / 20000000000000 : ℝ) ≤ Real.sqrt (110976113009 / 800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (110976113009 / 800000000000 : ℝ) ≤ (18622576437033 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (18622576437033 / 50000000000000 : ℝ) = (50000000000000 / 18622576437033 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7449030574813 / 20000000000000 : ℝ) = (1500000000000 / 7449030574813 : ℝ) := by norm_num
  have hL1 : (3247623715537 / 25000000000000 : ℝ) ≤ Real.log (1 + (110976113009 / 800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((110976113009 / 800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-38710960641801 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (18622576437033 / 50000000000000 : ℝ) ≤ (356534524259149 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (121426180253574761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 18622576437033 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 18622576437033 : ℝ) = (18622576437033 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 7449030574813 : ℝ) ≤ (24838882956067 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (121426180253574761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (18622576437033 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7449030574813 / 20000000000000 : ℝ)) ≤ (24838882956067 / 125000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_190 : ∀ t : ℝ, (110976113009 / 800000000000 : ℝ) < t → t ≤ (72162863729 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-44061874901302234382364153 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (72162863729 / 500000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_191
  have hV : (2257467992170528960953351512336197 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (110976113009 / 800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_190 (Vfield_monotoneOn (show (110976113009 / 800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (110976113009 / 800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_191 : (11523661450399625740968368555552663 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (72162863729 / 500000000000 : ℝ) := by
  have hp : (0 : ℝ) < (72162863729 / 500000000000 : ℝ) := by norm_num
  have hs1 : (37990226040127 / 100000000000000 : ℝ) ≤ Real.sqrt (72162863729 / 500000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (72162863729 / 500000000000 : ℝ) ≤ (593597281877 / 1562500000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (593597281877 / 1562500000000 : ℝ) = (1562500000000 / 593597281877 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (37990226040127 / 100000000000000 : ℝ) = (7500000000000 / 37990226040127 : ℝ) := by norm_num
  have hL1 : (13481557922957 / 100000000000000 : ℝ) ≤ Real.log (1 + (72162863729 / 500000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((72162863729 / 500000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-189744852168193 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (593597281877 / 1562500000000 : ℝ) ≤ (22691350020301 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (120773472647008061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1562500000000 / 593597281877 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (1562500000000 / 593597281877 : ℝ) = (593597281877 / 1562500000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 37990226040127 : ℝ) ≤ (24364099180507 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (120773472647008061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (593597281877 / 1562500000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (37990226040127 / 100000000000000 : ℝ)) ≤ (24364099180507 / 125000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_191 : ∀ t : ℝ, (72162863729 / 500000000000 : ℝ) < t → t ≤ (4675203313927 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-217948750577812708015789959 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4675203313927 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_192
  have hV : (11523661450399625740968368555552663 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (72162863729 / 500000000000 : ℝ) := by norm_num
    refine le_trans V_pt_191 (Vfield_monotoneOn (show (72162863729 / 500000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (72162863729 / 500000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_192 : (2319550237823934619468291380980197 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (4675203313927 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4675203313927 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (7644608650813 / 20000000000000 : ℝ) ≤ Real.sqrt (4675203313927 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4675203313927 / 32000000000000 : ℝ) ≤ (19111521627033 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (19111521627033 / 50000000000000 : ℝ) = (50000000000000 / 19111521627033 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7644608650813 / 20000000000000 : ℝ) = (1500000000000 / 7644608650813 : ℝ) := by norm_num
  have hL1 : (13636496487931 / 100000000000000 : ℝ) ≤ Real.log (1 + (4675203313927 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4675203313927 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3771369847857 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (19111521627033 / 50000000000000 : ℝ) ≤ (584151299863 / 1600000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (120570176438052161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 19111521627033 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 19111521627033 : ℝ) = (19111521627033 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 7644608650813 : ℝ) ≤ (96877576836823 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (120570176438052161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (19111521627033 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7644608650813 / 20000000000000 : ℝ)) ≤ (96877576836823 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_192 : ∀ t : ℝ, (4675203313927 / 32000000000000 : ℝ) < t → t ≤ (2365991674599 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-3385992685626310146148623 / 1562500000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2365991674599 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_193
  have hV : (2319550237823934619468291380980197 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4675203313927 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_192 (Vfield_monotoneOn (show (4675203313927 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4675203313927 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_193 : (364734525510705642328185764859227 / 156250000000000000000000000000000 : ℝ) ≤ Vfield (2365991674599 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2365991674599 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (1201701591683 / 3125000000000 : ℝ) ≤ Real.sqrt (2365991674599 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2365991674599 / 16000000000000 : ℝ) ≤ (38454450933857 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (38454450933857 / 100000000000000 : ℝ) = (100000000000000 / 38454450933857 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1201701591683 / 3125000000000 : ℝ) = (234375000000 / 1201701591683 : ℝ) := by norm_num
  have hL1 : (13791195364637 / 100000000000000 : ℝ) ≤ Real.log (1 + (2365991674599 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2365991674599 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-46851452525051 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (38454450933857 / 100000000000000 : ℝ) ≤ (367112090487233 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (120368423630766361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 38454450933857 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 38454450933857 : ℝ) = (38454450933857 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (234375000000 / 1201701591683 : ℝ) ≤ (38523580208753 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (120368423630766361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (38454450933857 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1201701591683 / 3125000000000 : ℝ)) ≤ (38523580208753 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_193 : ∀ t : ℝ, (2365991674599 / 16000000000000 : ℝ) < t → t ≤ (4788763384469 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-107825167877679817954269901 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4788763384469 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_194
  have hV : (364734525510705642328185764859227 / 156250000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2365991674599 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_193 (Vfield_monotoneOn (show (2365991674599 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2365991674599 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_194 : (1468115826968849807979892050712653 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (4788763384469 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4788763384469 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (4835559296837 / 12500000000000 : ℝ) ≤ Real.sqrt (4788763384469 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4788763384469 / 32000000000000 : ℝ) ≤ (38684474374697 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (38684474374697 / 100000000000000 : ℝ) = (100000000000000 / 38684474374697 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4835559296837 / 12500000000000 : ℝ) = (937500000000 / 4835559296837 : ℝ) := by norm_num
  have hL1 : (174320691169 / 1250000000000 : ℝ) ≤ Real.log (1 + (4788763384469 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4788763384469 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-9312824544367 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (38684474374697 / 100000000000000 : ℝ) ≤ (184557226209237 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (120168187437642261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 38684474374697 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 38684474374697 : ℝ) = (38684474374697 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (937500000000 / 4835559296837 : ℝ) ≤ (11968777751701 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (120168187437642261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (38684474374697 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4835559296837 / 12500000000000 : ℝ)) ≤ (11968777751701 / 62500000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_194 : ∀ t : ℝ, (4788763384469 / 32000000000000 : ℝ) < t → t ≤ (9634306804209 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-215165358248105047447896783 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9634306804209 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_195
  have hV : (1468115826968849807979892050712653 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4788763384469 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_194 (Vfield_monotoneOn (show (4788763384469 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4788763384469 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_195 : (11781514395175448448135766961643851 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9634306804209 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9634306804209 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (38798974704979 / 100000000000000 : ℝ) ≤ Real.sqrt (9634306804209 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9634306804209 / 64000000000000 : ℝ) ≤ (1939948735249 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1939948735249 / 5000000000000 : ℝ) = (5000000000000 / 1939948735249 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (38798974704979 / 100000000000000 : ℝ) = (7500000000000 / 38798974704979 : ℝ) := by norm_num
  have hL1 : (701139794149 / 5000000000000 : ℝ) ≤ Real.log (1 + (9634306804209 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9634306804209 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-185686747128881 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1939948735249 / 5000000000000 : ℝ) ≤ (18505501383377 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (120068629912735661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 1939948735249 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 1939948735249 : ℝ) = (1939948735249 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 38798974704979 : ℝ) ≤ (23868620068879 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (120068629912735661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1939948735249 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (38798974704979 / 100000000000000 : ℝ)) ≤ (23868620068879 / 125000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_195 : ∀ t : ℝ, (9634306804209 / 64000000000000 : ℝ) < t → t ≤ (242277170987 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-53675207027495025416044599 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (242277170987 / 1600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_196
  have hV : (11781514395175448448135766961643851 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9634306804209 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_195 (Vfield_monotoneOn (show (9634306804209 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9634306804209 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_196 : (738626299081200501541644075606671 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (242277170987 / 1600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (242277170987 / 1600000000000 : ℝ) := by norm_num
  have hs1 : (2432071132759 / 6250000000000 : ℝ) ≤ Real.sqrt (242277170987 / 1600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (242277170987 / 1600000000000 : ℝ) ≤ (7782627624829 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7782627624829 / 20000000000000 : ℝ) = (20000000000000 / 7782627624829 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (2432071132759 / 6250000000000 : ℝ) = (468750000000 / 2432071132759 : ℝ) := by norm_num
  have hL1 : (14099877011601 / 100000000000000 : ℝ) ≤ Real.log (1 + (242277170987 / 1600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((242277170987 / 1600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-46280057767249 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7782627624829 / 20000000000000 : ℝ) ≤ (74220381669123 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119969441844928161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 7782627624829 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 7782627624829 : ℝ) = (7782627624829 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (468750000000 / 2432071132759 : ℝ) ≤ (190402214852329 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119969441844928161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7782627624829 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (2432071132759 / 6250000000000 : ℝ)) ≤ (190402214852329 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_196 : ∀ t : ℝ, (242277170987 / 1600000000000 : ℝ) < t → t ≤ (9747866874751 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-214253371513051616275010301 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9747866874751 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_197
  have hV : (738626299081200501541644075606671 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (242277170987 / 1600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_196 (Vfield_monotoneOn (show (242277170987 / 1600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (242277170987 / 1600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_197 : (11854446297820562830364105709617577 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9747866874751 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9747866874751 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (39026967588833 / 100000000000000 : ℝ) ≤ Real.sqrt (9747866874751 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9747866874751 / 64000000000000 : ℝ) ≤ (19513483794417 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (19513483794417 / 50000000000000 : ℝ) = (50000000000000 / 19513483794417 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (39026967588833 / 100000000000000 : ℝ) = (7500000000000 / 39026967588833 : ℝ) := by norm_num
  have hL1 : (443028086593 / 3125000000000 : ℝ) ≤ Real.log (1 + (9747866874751 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9747866874751 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-184556906342643 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (19513483794417 / 50000000000000 : ℝ) ≤ (372090125812239 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119870620098265761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 19513483794417 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 19513483794417 : ℝ) = (19513483794417 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 39026967588833 : ℝ) ≤ (18986013947249 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119870620098265761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (19513483794417 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (39026967588833 / 100000000000000 : ℝ)) ≤ (18986013947249 / 100000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_197 : ∀ t : ℝ, (9747866874751 / 64000000000000 : ℝ) < t → t ≤ (4902323455011 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-53455129915275280262998321 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4902323455011 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_198
  have hV : (11854446297820562830364105709617577 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9747866874751 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_197 (Vfield_monotoneOn (show (9747866874751 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9747866874751 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_198 : (2378158287868762537286559738067491 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (4902323455011 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4902323455011 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (7828093202539 / 20000000000000 : ℝ) ≤ Real.sqrt (4902323455011 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4902323455011 / 32000000000000 : ℝ) ≤ (4892558251587 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4892558251587 / 12500000000000 : ℝ) = (12500000000000 / 4892558251587 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7828093202539 / 20000000000000 : ℝ) = (1500000000000 / 7828093202539 : ℝ) := by norm_num
  have hL1 : (3563465313123 / 25000000000000 : ℝ) ≤ Real.log (1 + (4902323455011 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4902323455011 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1839967371959 / 1000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4892558251587 / 12500000000000 : ℝ) ≤ (23317169436349 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119772161581331261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 4892558251587 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 4892558251587 : ℝ) = (4892558251587 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 7828093202539 : ℝ) ≤ (3786453365803 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119772161581331261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4892558251587 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7828093202539 / 20000000000000 : ℝ)) ≤ (3786453365803 / 20000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_198 : ∀ t : ℝ, (4902323455011 / 32000000000000 : ℝ) < t → t ≤ (9861426945293 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-213400398492837361219873477 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9861426945293 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_199
  have hV : (2378158287868762537286559738067491 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4902323455011 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_198 (Vfield_monotoneOn (show (4902323455011 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4902323455011 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_199 : (2385411342288393753428409349238819 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (9861426945293 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9861426945293 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (7850727253451 / 20000000000000 : ℝ) ≤ Real.sqrt (9861426945293 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9861426945293 / 64000000000000 : ℝ) ≤ (4906704533407 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4906704533407 / 12500000000000 : ℝ) = (12500000000000 / 4906704533407 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7850727253451 / 20000000000000 : ℝ) = (1500000000000 / 7850727253451 : ℝ) := by norm_num
  have hL1 : (358269113683 / 2500000000000 : ℝ) ≤ Real.log (1 + (9861426945293 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9861426945293 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-183439688472353 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4906704533407 / 12500000000000 : ℝ) ≤ (374055694331361 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (119674063246353561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 4906704533407 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 4906704533407 : ℝ) = (4906704533407 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 7850727253451 : ℝ) ≤ (47197434121827 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (119674063246353561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4906704533407 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7850727253451 / 20000000000000 : ℝ)) ≤ (47197434121827 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_199 : ∀ t : ℝ, (9861426945293 / 64000000000000 : ℝ) < t → t ≤ (2479551745141 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-212991543269576060556325357 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2479551745141 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_200
  have hV : (2385411342288393753428409349238819 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9861426945293 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_199 (Vfield_monotoneOn (show (9861426945293 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9861426945293 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
